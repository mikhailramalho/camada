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
                               "(set-option :produce-models true)\n"
                               "(set-option :global-declarations true)\n"
                               "(set-info :status unknown)\n"
                               "(set-logic QF_AUFBV)\n"
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
// Phase 2: interactive child-process pipe
//
// SMTLIBSolver constructed with the SMTLIBProcessTag spawns a child solver
// via `sh -c <cmd>` and round-trips check()/get* through bidirectional pipes.
// Camada's verified solver matrix at the time of writing: z3, cvc5, bitwuzla,
// yices-smt2, mathsat. Each test below is parameterized over every binary
// actually found on disk; tests gracefully SKIP when no usable binary is
// available.
// ---------------------------------------------------------------------------

#include <catch2/generators/catch_generators.hpp>
#include <catch2/generators/catch_generators_range.hpp>

namespace {

struct SolverDescriptor {
  std::string Name;    // human-readable, e.g. "z3"
  std::string Command; // shell-ready: full path + flags
};

bool isExecutable(const std::string &Path) {
  return ::access(Path.c_str(), X_OK) == 0;
}

// Try the compile-time hint (CAMADA_TEST_<NAME>_BIN), falling back to the
// system PATH. Returns empty string if neither resolves to an executable.
std::string findInPath(const std::string &Name, const char *HintBin) {
  if (HintBin && isExecutable(HintBin))
    return HintBin;
  std::string Cmd = "command -v " + Name;
  if (FILE *P = ::popen(Cmd.c_str(), "r")) {
    char Buf[4096];
    std::string Out;
    while (std::fgets(Buf, sizeof(Buf), P))
      Out.append(Buf);
    ::pclose(P);
    while (!Out.empty() && (Out.back() == '\n' || Out.back() == '\r'))
      Out.pop_back();
    if (!Out.empty() && isExecutable(Out))
      return Out;
  }
  return {};
}

// Discover every SMT-LIB-speaking solver this build can reach. Each entry's
// command is ready to be passed to camada::createSMTLIBSolver().
std::vector<SolverDescriptor> discoverSolvers() {
  std::vector<SolverDescriptor> Result;
#ifdef CAMADA_TEST_Z3_BIN
  if (std::string Bin = findInPath("z3", CAMADA_TEST_Z3_BIN); !Bin.empty())
    Result.push_back({"z3", Bin + " -in"});
#else
  if (std::string Bin = findInPath("z3", nullptr); !Bin.empty())
    Result.push_back({"z3", Bin + " -in"});
#endif
#ifdef CAMADA_TEST_CVC5_BIN
  if (std::string Bin = findInPath("cvc5", CAMADA_TEST_CVC5_BIN); !Bin.empty())
    Result.push_back({"cvc5", Bin + " --lang smt2 --incremental"});
#else
  if (std::string Bin = findInPath("cvc5", nullptr); !Bin.empty())
    Result.push_back({"cvc5", Bin + " --lang smt2 --incremental"});
#endif
#ifdef CAMADA_TEST_BITWUZLA_BIN
  if (std::string Bin = findInPath("bitwuzla", CAMADA_TEST_BITWUZLA_BIN);
      !Bin.empty())
    Result.push_back({"bitwuzla", Bin});
#else
  if (std::string Bin = findInPath("bitwuzla", nullptr); !Bin.empty())
    Result.push_back({"bitwuzla", Bin});
#endif
#ifdef CAMADA_TEST_YICES_SMT2_BIN
  if (std::string Bin = findInPath("yices-smt2", CAMADA_TEST_YICES_SMT2_BIN);
      !Bin.empty())
    Result.push_back({"yices-smt2", Bin + " --incremental"});
#else
  if (std::string Bin = findInPath("yices-smt2", nullptr); !Bin.empty())
    Result.push_back({"yices-smt2", Bin + " --incremental"});
#endif
#ifdef CAMADA_TEST_MATHSAT_BIN
  if (std::string Bin = findInPath("mathsat", CAMADA_TEST_MATHSAT_BIN);
      !Bin.empty())
    Result.push_back({"mathsat", Bin});
#else
  if (std::string Bin = findInPath("mathsat", nullptr); !Bin.empty())
    Result.push_back({"mathsat", Bin});
#endif
  // STP is intentionally absent: its interactive SMT-LIB front-end has two
  // structural issues that the verified matrix can't paper over —
  // (get-value ...) returns junk unless `-p` is passed, and `-p` causes STP
  // to emit an unsolicited `(model ...)` block after every `(check-sat)`,
  // which desyncs the line-oriented response pipe. Camada still supports STP
  // through its native C-API backend (camada::createSTPSolver()).
  return Result;
}

const std::vector<SolverDescriptor> &availableSolvers() {
  static const std::vector<SolverDescriptor> Solvers = discoverSolvers();
  return Solvers;
}

} // namespace

// Test-helper macro: pull a SolverDescriptor for the current iteration, or
// SKIP the case if no solver is reachable. Catch2's GENERATE_REF requires the
// vector to outlive the test (the static cache from availableSolvers()
// satisfies that).
#define CAMADA_SMTLIB_FOREACH_SOLVER(VarName)                                  \
  if (availableSolvers().empty())                                              \
    SKIP("No SMT-LIB-speaking solver found on PATH or in deps install dir");   \
  auto VarName = GENERATE_REF(Catch::Generators::from_range(availableSolvers()))

TEST_CASE("SMTLIB interactive: public factory works against every solver",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  auto Solver = camada::createSMTLIBSolver(S.Command);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(1, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

TEST_CASE("SMTLIB interactive: dual emitter logs to file too",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  std::string Path = makeTempPath();
  {
    auto Solver = camada::createSMTLIBSolver(S.Command, Path);
    auto BV8 = Solver->mkBVSort(8);
    auto X = Solver->mkSymbol("x", BV8);
    Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(3, BV8)));
    REQUIRE(Solver->check() == camada::checkResult::SAT);
  }
  std::string Got = readFile(Path);
  std::remove(Path.c_str());

  // The script should contain the declarations and the assertion.
  REQUIRE(Got.find("(declare-fun |x| () (_ BitVec 8))\n") != std::string::npos);
  REQUIRE(Got.find("(assert (= |x| #b00000011))\n") != std::string::npos);
  REQUIRE(Got.find("(check-sat)\n") != std::string::npos);
}

TEST_CASE("SMTLIB interactive: SAT problem returns SAT from check()",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  auto Solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBProcessTag{}, S.Command);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(5, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

TEST_CASE("SMTLIB interactive: UNSAT problem returns UNSAT from check()",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  auto Solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBProcessTag{}, S.Command);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(5, BV8)));
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(7, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::UNSAT);
}

TEST_CASE("SMTLIB interactive: getBV round-trips a concrete value",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  auto Solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBProcessTag{}, S.Command);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(42, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);

  auto Result = Solver->getBV(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == 42);
}

TEST_CASE("SMTLIB interactive: getBV round-trips a 1-bit value",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  auto Solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBProcessTag{}, S.Command);
  auto BV1 = Solver->mkBVSort(1);
  auto B = Solver->mkSymbol("b", BV1);
  Solver->addConstraint(Solver->mkEqual(B, Solver->mkBVFromBin("1", 1)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);

  // 1-bit BV with the high (and only) bit set is -1 in two's complement,
  // which is what Camada's getBV() returns (signed interpretation).
  auto Result = Solver->getBV(B);
  REQUIRE(Result);
  REQUIRE(Result.value() == -1);

  // The unsigned/binary form should be exactly "1".
  auto Bin = Solver->getBVInBin(B);
  REQUIRE(Bin);
  REQUIRE(Bin.value() == "1");
}

TEST_CASE("SMTLIB interactive: push/pop returns sat/unsat/sat from check()",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  auto Solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBProcessTag{}, S.Command);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  auto Five = Solver->mkBVFromDec(5, BV8);
  auto Seven = Solver->mkBVFromDec(7, BV8);

  Solver->addConstraint(Solver->mkEqual(X, Five));
  REQUIRE(Solver->check() == camada::checkResult::SAT);

  Solver->push();
  Solver->addConstraint(Solver->mkEqual(X, Seven));
  REQUIRE(Solver->check() == camada::checkResult::UNSAT);
  Solver->pop();

  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

TEST_CASE("SMTLIB interactive: symbol declared in pushed scope survives pop",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  // Without (set-option :global-declarations true), declarations made inside
  // a (push) are dropped on (pop) and a follow-up reference to the symbol
  // would fail with "unknown constant" in the child solver.
  auto Solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBProcessTag{}, S.Command);
  auto BV8 = Solver->mkBVSort(8);

  Solver->push();
  auto X = Solver->mkSymbol("x", BV8);
  Solver->pop();

  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(9, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Bin = Solver->getBVInBin(X);
  REQUIRE(Bin);
  REQUIRE(Bin.value() == "00001001");
}

TEST_CASE("SMTLIB interactive: getBVInBin handles 128-bit decimal model value",
          "[SMTLIB][pipeline]") {
  CAMADA_SMTLIB_FOREACH_SOLVER(S);
  CAPTURE(S.Name);

  // Some solvers (e.g. MathSAT) emit BV model values in `(_ bv<n> <w>)` decimal
  // form. Widths above 64 must still parse correctly.
  auto Solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBProcessTag{}, S.Command);
  auto BV128 = Solver->mkBVSort(128);
  auto X = Solver->mkSymbol("x", BV128);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(42, BV128)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);

  auto Bin = Solver->getBVInBin(X);
  REQUIRE(Bin);
  // 42 = 0b101010, zero-extended to 128 bits.
  std::string Expected(128, '0');
  Expected.replace(Expected.size() - 6, 6, "101010");
  REQUIRE(Bin.value() == Expected);
}
