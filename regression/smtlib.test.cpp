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

// Tests for the SMT-LIB write-only backend (issue #57 Phase 1).
//
// Two test groups:
//
//  1. Golden-string emission tests — build a tiny formula, emit the SMT-LIB
//     script to a temp file, and assert the file content matches a string
//     literal. No external solver required.
//
//  2. End-to-end pipeline tests — build a problem on both SMTLIBSolver and
//     Z3Solver, pipe the emitted script through `z3 -in`, and assert the
//     parsed sat/unsat matches Z3Solver's native check() result. Skipped
//     gracefully if no usable z3 binary is found.

#include <catch2/catch_test_macros.hpp>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <unistd.h>
#include <vector>

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

// ---------------------------------------------------------------------------
// End-to-end pipeline tests
//
// Phase 1 acceptance gate: emitted SMT-LIB must be syntactically valid. The
// cleanest way to assert this is to run the script through a real solver and
// check the result matches what Camada's native Z3 backend says. We use Z3
// because it's already on PATH for the build (deps download stages it under
// build/deps/install/bin/z3), or we fall back to whatever is on PATH.
// ---------------------------------------------------------------------------

namespace {

// Find a usable z3 binary. Returns empty string if none.
std::string findZ3() {
#ifdef CAMADA_TEST_Z3_BIN
  if (::access(CAMADA_TEST_Z3_BIN, X_OK) == 0)
    return CAMADA_TEST_Z3_BIN;
#endif
  // Fall back to PATH lookup via popen("which z3").
  if (FILE *P = ::popen("command -v z3", "r")) {
    char Buf[4096];
    std::string Out;
    while (std::fgets(Buf, sizeof(Buf), P))
      Out.append(Buf);
    ::pclose(P);
    while (!Out.empty() && (Out.back() == '\n' || Out.back() == '\r'))
      Out.pop_back();
    if (!Out.empty() && ::access(Out.c_str(), X_OK) == 0)
      return Out;
  }
  return {};
}

// Run `z3 -smt2 <Path>` and return the first whitespace-trimmed line of
// stdout. Empty string means z3 didn't produce a parseable answer.
std::string runZ3OnFile(const std::string &Z3, const std::string &Path) {
  std::string Cmd = Z3 + " -smt2 " + Path + " 2>&1";
  FILE *P = ::popen(Cmd.c_str(), "r");
  if (!P)
    return {};
  char Buf[4096];
  std::string Out;
  while (std::fgets(Buf, sizeof(Buf), P))
    Out.append(Buf);
  ::pclose(P);
  // Take the first non-empty line.
  std::stringstream Ss(Out);
  std::string Line;
  while (std::getline(Ss, Line)) {
    while (!Line.empty() && (Line.back() == '\r' || Line.back() == ' '))
      Line.pop_back();
    if (!Line.empty())
      return Line;
  }
  return {};
}

} // namespace

// Cross-validates the SMTLIBSolver-emitted script against the native Z3
// backend. Skipped when the library was built without Z3 support — the rest
// of the pipeline tests (unsat, BV-mix, push/pop) don't use Z3Solver and
// keep running unconditionally as long as a z3 binary is present.
#ifdef SOLVER_Z3_ENABLED
TEST_CASE("SMTLIB pipeline: SAT problem matches z3 -in", "[SMTLIB][pipeline]") {
  const std::string Z3 = findZ3();
  if (Z3.empty())
    SKIP("No z3 binary found on PATH or in deps install dir");

  // Native check via Z3Solver, for cross-validation.
  auto Native = camada::createZ3Solver();
  auto BV8 = Native->mkBVSort(8);
  auto X = Native->mkSymbol("x", BV8);
  auto Five = Native->mkBVFromDec(5, BV8);
  Native->addConstraint(Native->mkEqual(X, Five));
  auto NativeResult = Native->check();
  REQUIRE(NativeResult == camada::checkResult::SAT);

  // Same problem through SMTLIBSolver to a temp file.
  std::string Path = makeTempPath();
  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto SBV8 = Solver->mkBVSort(8);
    auto SX = Solver->mkSymbol("x", SBV8);
    auto SFive = Solver->mkBVFromDec(5, SBV8);
    Solver->addConstraint(Solver->mkEqual(SX, SFive));
    Solver->check();
  }

  std::string Z3Says = runZ3OnFile(Z3, Path);
  std::remove(Path.c_str());

  REQUIRE(Z3Says == "sat");
}
#endif // SOLVER_Z3_ENABLED

TEST_CASE("SMTLIB pipeline: UNSAT problem matches z3 -in",
          "[SMTLIB][pipeline]") {
  const std::string Z3 = findZ3();
  if (Z3.empty())
    SKIP("No z3 binary found on PATH or in deps install dir");

  std::string Path = makeTempPath();
  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV8 = Solver->mkBVSort(8);
    auto X = Solver->mkSymbol("x", BV8);
    Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(5, BV8)));
    Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(7, BV8)));
    Solver->check();
  }

  std::string Z3Says = runZ3OnFile(Z3, Path);
  std::remove(Path.c_str());

  REQUIRE(Z3Says == "unsat");
}

TEST_CASE("SMTLIB pipeline: BV ops mix matches z3 -in", "[SMTLIB][pipeline]") {
  const std::string Z3 = findZ3();
  if (Z3.empty())
    SKIP("No z3 binary found on PATH or in deps install dir");

  std::string Path = makeTempPath();
  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV32 = Solver->mkBVSort(32);
    auto X = Solver->mkSymbol("x", BV32);
    auto Y = Solver->mkSymbol("y", BV32);
    auto Sum = Solver->mkBVAdd(X, Y);
    auto Diff = Solver->mkBVSub(X, Y);
    auto Three = Solver->mkBVFromDec(3, BV32);
    auto One = Solver->mkBVFromDec(1, BV32);
    // x + y = 3 AND x - y = 1  =>  x = 2, y = 1
    Solver->addConstraint(Solver->mkEqual(Sum, Three));
    Solver->addConstraint(Solver->mkEqual(Diff, One));
    Solver->check();
  }

  std::string Z3Says = runZ3OnFile(Z3, Path);
  std::remove(Path.c_str());

  REQUIRE(Z3Says == "sat");
}

TEST_CASE("SMTLIB pipeline: push/pop scoping matches z3 -in",
          "[SMTLIB][pipeline]") {
  const std::string Z3 = findZ3();
  if (Z3.empty())
    SKIP("No z3 binary found on PATH or in deps install dir");

  std::string Path = makeTempPath();
  {
    auto Solver = std::make_unique<camada::SMTLIBSolver>(Path);
    auto BV8 = Solver->mkBVSort(8);
    auto X = Solver->mkSymbol("x", BV8);
    auto Five = Solver->mkBVFromDec(5, BV8);
    auto Seven = Solver->mkBVFromDec(7, BV8);

    Solver->addConstraint(Solver->mkEqual(X, Five));
    Solver->check(); // expected sat

    Solver->push();
    Solver->addConstraint(Solver->mkEqual(X, Seven));
    Solver->check(); // expected unsat (x = 5 AND x = 7)
    Solver->pop();
    Solver->check(); // expected sat again
  }

  std::string Cmd = Z3 + " -smt2 " + Path + " 2>&1";
  FILE *P = ::popen(Cmd.c_str(), "r");
  REQUIRE(P != nullptr);
  char Buf[4096];
  std::string Out;
  while (std::fgets(Buf, sizeof(Buf), P))
    Out.append(Buf);
  ::pclose(P);
  std::remove(Path.c_str());

  // Expect three lines: sat, unsat, sat (in that order).
  std::stringstream Ss(Out);
  std::vector<std::string> Lines;
  std::string Line;
  while (std::getline(Ss, Line)) {
    while (!Line.empty() && (Line.back() == '\r' || Line.back() == ' '))
      Line.pop_back();
    if (!Line.empty())
      Lines.push_back(Line);
  }
  REQUIRE(Lines.size() == 3);
  REQUIRE(Lines[0] == "sat");
  REQUIRE(Lines[1] == "unsat");
  REQUIRE(Lines[2] == "sat");
}
