/**************************************************************************
 *
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 *
 **************************************************************************/

// Write-only golden-string tests for the SMT-LIB backend.
//
// Build a tiny formula, emit the SMT-LIB script to a temp file, and assert
// the file content matches a string literal. No external solver required.
//
// The interactive child-process pipeline tests live alongside each native
// backend's regression file (z3.test.cpp etc.). They share the scenario
// helpers in smtlib_pipeline.test.h, which lets one CTest entry per
// (test × solver) report pass/fail without per-test SKIP noise.

#include <catch2/catch_test_macros.hpp>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <unistd.h>

#include "camada.h"
#include "smtlibsolver.h"

namespace {

std::string makeTempPath() {
  char Tmp[] = "/tmp/camada-smtlib-XXXXXX";
  int Fd = ::mkstemp(Tmp);
  REQUIRE(Fd >= 0);
  ::close(Fd);
  return std::string(Tmp);
}

std::string readFile(const std::string &Path) {
  std::ifstream In(Path);
  REQUIRE(In.good());
  std::stringstream Ss;
  Ss << In.rdbuf();
  return Ss.str();
}

} // namespace

TEST_CASE("SMTLIB write-only emits a minimal script", "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV8 = Solver->mkBVSort(8);
    auto X = Solver->mkSymbol("x", BV8);
    auto Five = Solver->mkBVFromBin("00000101", BV8);
    Solver->addConstraint(Solver->mkEqual(X, Five));
    Solver->check();
  } // Solver dtor flushes via FileEmitter dtor.

  const std::string Expected = "(set-option :print-success false)\n"
                               "(set-option :produce-models true)\n"
                               "(set-option :produce-unsat-assumptions true)\n"
                               "(set-option :global-declarations true)\n"
                               "(set-info :status unknown)\n"
                               "(set-logic ALL)\n"
                               "(declare-fun |x| () (_ BitVec 8))\n"
                               "(assert (= |x| #b00000101))\n"
                               "(check-sat)\n";

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  REQUIRE(Got == Expected);
}

TEST_CASE("SMTLIB write-only quotes hostile symbol names", "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV4 = Solver->mkBVSort(4);
    // Names like main::1::x.field appear in ESBMC.
    auto Sym = Solver->mkSymbol("main::1::faces.a", BV4);
    (void)Sym;
  }

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  // The symbol must appear quoted. We do not pin the exact line because the
  // preamble may be tweaked later; we only assert the declaration line shape.
  REQUIRE(Got.find("(declare-fun |main::1::faces.a| () (_ BitVec 4))\n") !=
          std::string::npos);
}

// Regression for a bug Codex caught: distinct Camada names must produce
// distinct SMT-LIB symbols, even when the names contain `|`, `\`, or `%`.
// The previous lossy substitution (`|`/`\` -> `?`) collapsed `a|b` and `a?b`
// into the same emitted symbol. The fix is a percent-encoding that's
// reversible and collision-free.
TEST_CASE("SMTLIB write-only encodes special chars without collision",
          "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV4 = Solver->mkBVSort(4);
    Solver->mkSymbol("a|b", BV4);
    Solver->mkSymbol("a?b", BV4);
    Solver->mkSymbol("a\\b", BV4);
    Solver->mkSymbol("a%b", BV4);
  }

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  // `?` survives unchanged. `|`, `\`, `%` are percent-encoded.
  REQUIRE(Got.find("(declare-fun |a%7Cb| () (_ BitVec 4))\n") !=
          std::string::npos);
  REQUIRE(Got.find("(declare-fun |a?b| () (_ BitVec 4))\n") !=
          std::string::npos);
  REQUIRE(Got.find("(declare-fun |a%5Cb| () (_ BitVec 4))\n") !=
          std::string::npos);
  REQUIRE(Got.find("(declare-fun |a%25b| () (_ BitVec 4))\n") !=
          std::string::npos);
}

TEST_CASE("SMTLIB write-only preserves bool/eq emission", "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV1 = Solver->mkBVSort(1);
    auto B = Solver->mkSymbol("b", BV1);
    Solver->addConstraint(Solver->mkEqual(B, Solver->mkBVFromBin("1", 1)));
  }

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  REQUIRE(Got.find("(declare-fun |b| () (_ BitVec 1))\n") != std::string::npos);
  REQUIRE(Got.find("(assert (= |b| #b1))\n") != std::string::npos);
}

// Regression for a bug Codex caught: getWidthFromSolver() must return the
// stored width, not re-derive sig+exp+1 — BVFP stores the *encoded*
// significand width, so re-deriving overshoots by one and aborts in
// validateSortWidth() when the BVFP sort is constructed.
TEST_CASE("SMTLIB write-only constructs BV-encoded FP sorts", "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto FP32 = Solver->mkFP32Sort(camada::FPEncoding::BV);
    REQUIRE(FP32->getWidth() == 32);
    auto FP64 = Solver->mkFP64Sort(camada::FPEncoding::BV);
    REQUIRE(FP64->getWidth() == 64);
  }

  std::remove(Path.c_str());
}

// Regression for a bug Codex caught: mkBVFromDec(-1, W) must produce all ones
// of width W, even when W > 64. The previous implementation cast int64_t to
// uint64_t and dropped the high bits.
TEST_CASE("SMTLIB write-only emits wide negative BV literals correctly",
          "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV128 = Solver->mkBVSort(128);
    auto X = Solver->mkSymbol("x", BV128);
    auto NegOne = Solver->mkBVFromDec(-1, BV128);
    Solver->addConstraint(Solver->mkEqual(X, NegOne));
  }

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  // Expect 128 '1' bits.
  std::string ExpectedBits(128, '1');
  REQUIRE(Got.find("(assert (= |x| #b" + ExpectedBits + "))\n") !=
          std::string::npos);
}

// Same regression, narrow case kept passing before — assert the full chain
// still works for typical widths so a future refactor doesn't silently break
// the common path.
TEST_CASE("SMTLIB write-only emits 32-bit -1 literal as 32 ones", "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV32 = Solver->mkBVSort(32);
    auto X = Solver->mkSymbol("x", BV32);
    Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(-1, BV32)));
  }

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  REQUIRE(Got.find("(assert (= |x| #b" + std::string(32, '1') + "))\n") !=
          std::string::npos);
}

// Regression for a Codex-flagged parser weakness: getInt() must accept an
// integral rational model value even when the rational is unreduced
// (Num != Den, but Den evenly divides Num). Solver versions vary in
// whether they reduce rational fractions before reporting them, so the
// parser should not depend on them all reducing. We exercise the parser
// directly via the test-only entry point so the test isn't gated on which
// solvers happen to be reachable on the host.
TEST_CASE("SMTLIB getInt accepts integral unreduced rationals", "[SMTLIB]") {
  using camada::SMTLIBSolver;

  // Plain integer: bare numeral and parenthesized negative.
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("7") == "7");
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("(- 5)") == "-5");

  // Decimal-typed integer (z3's Real-typed get-value shape).
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("2.0") == "2");
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("(- 3.0)") == "-3");

  // Reduced rational: trivially handled.
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("(/ 6 1)") == "6");

  // Unreduced rationals where the division is exact.
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("(/ 4 2)") == "2");
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("(/ 100 25)") == "4");
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("(- (/ 10 5))") == "-2");

  // Non-integral rationals must remain rejected (getInt's contract is
  // "integer model value"; truncation would be silently lossy).
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("(/ 7 2)").empty());
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest("3.14").empty());

  // Wide values: ensures the decimal-string long-division helper isn't
  // capped at 64 bits.
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest(
              "(/ 100000000000000000000 100000000000000000000)") == "1");
  REQUIRE(SMTLIBSolver::parseIntModelValueForTest(
              "(/ 100000000000000000000 50000000000000000000)") == "2");
}

// Pin the let-binding emission for shared subterms: a DAG node referenced
// twice is bound to a %t temporary at its first occurrence and referenced
// by name afterwards; once-used nodes stay inline.
TEST_CASE("SMTLIB write-only let-binds shared subterms", "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV8 = Solver->mkBVSort(8);
    auto X = Solver->mkSymbol("x", BV8);
    auto Y = Solver->mkSymbol("y", BV8);
    auto Sum = Solver->mkBVAdd(X, Y);      // shared twice
    auto Prod = Solver->mkBVMul(Sum, Sum); // shares Sum
    Solver->addConstraint(Solver->mkEqual(Prod, X));
    Solver->check();
  }

  const std::string Expected =
      "(set-option :print-success false)\n"
      "(set-option :produce-models true)\n"
      "(set-option :produce-unsat-assumptions true)\n"
      "(set-option :global-declarations true)\n"
      "(set-info :status unknown)\n"
      "(set-logic ALL)\n"
      "(declare-fun |x| () (_ BitVec 8))\n"
      "(declare-fun |y| () (_ BitVec 8))\n"
      "(assert (let ((%t0 (bvadd |x| |y|))) (= (bvmul %t0 %t0) |x|)))\n"
      "(check-sat)\n";

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  REQUIRE(Got == Expected);
}

// Symbols spelled like let temporaries must not be captured: quoteSymbol
// encodes every literal '%' as "%25", so a user symbol "%t0" renders as
// |%25t0| and can never alias the unquoted %t0 temporary.
TEST_CASE("SMTLIB write-only let temporaries cannot capture user symbols",
          "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV8 = Solver->mkBVSort(8);
    auto Hostile = Solver->mkSymbol("%t0", BV8);
    auto Y = Solver->mkSymbol("y", BV8);
    auto Sum = Solver->mkBVAdd(Y, Y); // let-bound as %t0
    Solver->addConstraint(Solver->mkEqual(
        Solver->mkBVAdd(Solver->mkBVMul(Sum, Sum), Hostile), Y));
    Solver->check();
  }

  const std::string Expected = "(set-option :print-success false)\n"
                               "(set-option :produce-models true)\n"
                               "(set-option :produce-unsat-assumptions true)\n"
                               "(set-option :global-declarations true)\n"
                               "(set-info :status unknown)\n"
                               "(set-logic ALL)\n"
                               "(declare-fun |%25t0| () (_ BitVec 8))\n"
                               "(declare-fun |y| () (_ BitVec 8))\n"
                               "(assert (let ((%t0 (bvadd |y| |y|))) "
                               "(= (bvadd (bvmul %t0 %t0) |%25t0|) |y|)))\n"
                               "(check-sat)\n";

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  REQUIRE(Got == Expected);
}

// Deep, lightly shared chains must emit without exhausting the stack: the
// renderer is iterative (a 50k-node linear chain overflows a recursive
// emitter long before this size).
TEST_CASE("SMTLIB write-only emits deep expression chains", "[SMTLIB]") {
  std::string Path = makeTempPath();

  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV8 = Solver->mkBVSort(8);
    auto X = Solver->mkSymbol("x", BV8);
    auto One = Solver->mkBVFromBin("00000001", BV8);
    auto Chain = X;
    for (int I = 0; I < 50000; ++I)
      Chain = Solver->mkBVAdd(Chain, One);
    Solver->addConstraint(Solver->mkEqual(Chain, X));
    Solver->check();
  }

  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  REQUIRE(Got.find("(check-sat)") != std::string::npos);
}

TEST_CASE("SMTLIB feature capabilities", "[SMTLIB]") {
  std::string Path = makeTempPath();
  auto solver = std::make_unique<camada::SMTLIBSolver>(Path);
  using camada::SolverFeature;
  REQUIRE(solver->supports(SolverFeature::IntRealArithmetic));
  REQUIRE(solver->supports(SolverFeature::Quantifiers));
  REQUIRE(solver->supports(SolverFeature::UninterpretedFunctions));
  REQUIRE(solver->supports(SolverFeature::NativeFloatingPoint));
  REQUIRE(solver->supports(SolverFeature::NativeTuples));
  REQUIRE(solver->supports(SolverFeature::NativeConstantArrays));
  // UnsatAssumptions reflects the runtime probe: in write-only mode there
  // is no child to answer :produce-unsat-assumptions, so it is false here
  // and true against children that accept the option.
  REQUIRE_FALSE(solver->supports(SolverFeature::UnsatAssumptions));
  REQUIRE_FALSE(solver->supports(SolverFeature::Timeouts));
  REQUIRE_FALSE(solver->supports(SolverFeature::ArrayModels));

  // Camada tuple lowering flips the native-tuples bit.
  auto camadaTuples = std::make_unique<camada::SMTLIBSolver>(
      Path, camada::TupleEncoding::Camada);
  REQUIRE_FALSE(camadaTuples->supports(SolverFeature::NativeTuples));

  solver.reset();
  camadaTuples.reset();
  std::remove(Path.c_str());
}
