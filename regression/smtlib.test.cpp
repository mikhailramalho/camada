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

#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include "camada.h"
#include "solvers/smtlibsolver.h"

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

// ---------------------------------------------------------------------------
// One-shot mode (SMTLIBOneShotTag): serialize to a file, run a shell command
// on it, scan stdout for a verdict; an optional interactive model solver
// serves get-value queries after a sat verdict.
// ---------------------------------------------------------------------------

namespace {

// Write an executable shell script and return its path.
std::string makeScript(const std::string &Body) {
  std::string Path = makeTempPath();
  {
    std::ofstream Out(Path);
    REQUIRE(Out.good());
    Out << "#!/bin/sh\n" << Body;
  }
  REQUIRE(::chmod(Path.c_str(), 0755) == 0);
  return Path;
}

std::vector<std::string> z3ModelArgv() {
#ifdef CAMADA_TEST_Z3_BIN
  if (::access(CAMADA_TEST_Z3_BIN, X_OK) == 0)
    return {CAMADA_TEST_Z3_BIN, "-in"};
#endif
  return {};
}

// Fork-and-expect-abort, local copy of the tests.h helper (this file does
// not include the shared fixture headers).
template <typename Fn> void requireAborts(Fn &&Body) {
  ::pid_t Pid = ::fork();
  REQUIRE(Pid >= 0);
  if (Pid == 0) {
    Body();
    std::_Exit(0);
  }
  int Status = 0;
  REQUIRE(::waitpid(Pid, &Status, 0) == Pid);
  REQUIRE(WIFSIGNALED(Status));
  REQUIRE(WTERMSIG(Status) == SIGABRT);
}

} // namespace

TEST_CASE("SMTLIB one-shot verdict scanner contract", "[SMTLIB][oneshot]") {
  using camada::checkResult;
  using camada::parseOneShotVerdictLine;

  // Bare SMT-LIB verdicts.
  REQUIRE(parseOneShotVerdictLine("sat") == checkResult::SAT);
  REQUIRE(parseOneShotVerdictLine("unsat") == checkResult::UNSAT);
  REQUIRE(parseOneShotVerdictLine("unknown") == checkResult::UNKNOWN);

  // SAT-competition style.
  REQUIRE(parseOneShotVerdictLine("s SATISFIABLE") == checkResult::SAT);
  REQUIRE(parseOneShotVerdictLine("s UNSATISFIABLE") == checkResult::UNSAT);
  REQUIRE(parseOneShotVerdictLine("s UNKNOWN") == checkResult::UNKNOWN);

  // Surrounding whitespace tolerated.
  REQUIRE(parseOneShotVerdictLine("  sat") == checkResult::SAT);
  REQUIRE(parseOneShotVerdictLine("unsat\r\n") == checkResult::UNSAT);
  REQUIRE(parseOneShotVerdictLine("\t s SATISFIABLE \n") == checkResult::SAT);

  // Everything else rejected — no substring matching.
  REQUIRE_FALSE(parseOneShotVerdictLine("").has_value());
  REQUIRE_FALSE(parseOneShotVerdictLine("   ").has_value());
  REQUIRE_FALSE(parseOneShotVerdictLine("c solving /tmp/q.smt2").has_value());
  REQUIRE_FALSE(
      parseOneShotVerdictLine("[NeuroSym] loading model...").has_value());
  REQUIRE_FALSE(parseOneShotVerdictLine("unsat core").has_value());
  REQUIRE_FALSE(parseOneShotVerdictLine("presat").has_value());
  REQUIRE_FALSE(parseOneShotVerdictLine("SATISFIABLE").has_value());
  REQUIRE_FALSE(parseOneShotVerdictLine("s sat").has_value());
}

TEST_CASE("SMTLIB one-shot sat with model solver", "[SMTLIB][oneshot]") {
  auto ModelArgv = z3ModelArgv();
  if (ModelArgv.empty())
    SKIP("no staged z3 binary for the model solver");

  std::string Formula = makeTempPath();
  // The stand-in checks it actually received the formula file, emits log
  // noise a substring scanner would trip on, then the verdict.
  std::string Script = makeScript("test -f \"$1\" || exit 9\n"
                                  "echo '[fake-mallob] c unsat core noise'\n"
                                  "echo sat\n");
  long SeenPgid = 0;
  auto solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBOneShotTag{}, Formula, Script + " %f", ModelArgv,
      [&SeenPgid](long Pgid) { SeenPgid = Pgid; });

  auto X = solver->mkSymbol("x", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(X, solver->mkBVFromDec(5, 8)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  // Pgid handed out at spawn; the formula file is complete.
  REQUIRE(SeenPgid > 0);
  std::string Written = readFile(Formula);
  REQUIRE(Written.find("(check-sat)") != std::string::npos);
  REQUIRE(Written.find("(assert") != std::string::npos);

  // The parallel model solver agrees and serves the model.
  REQUIRE(solver->oneShotModelVerdict() == camada::checkResult::SAT);
  REQUIRE(solver->oneShotModelSolverLive());
  auto Val = solver->getBV(X);
  REQUIRE(Val);
  REQUIRE(Val.value() == 5);

  // Single-query restriction: a second check aborts.
  requireAborts([&]() { (void)solver->check(); });

  solver.reset();
  std::remove(Formula.c_str());
  std::remove(Script.c_str());
}

TEST_CASE("SMTLIB one-shot silent model solver is dropped, not hung",
          "[SMTLIB][oneshot]") {
  // A model child that consumes input but never acks (it does not speak
  // the :print-success protocol) used to deadlock the constructor:
  // camada blocked reading an ack the child would never send, before the
  // caller ever got control. It must instead be dropped at the first
  // bounded read, costing only counterexample support.
  // RAII restore: a failing REQUIRE below must not leave the shortened
  // process-global timeout behind for later tests.
  struct TimeoutGuard {
    unsigned Saved = camada::SMTLIBSolver::OneShotModelAckTimeoutMs;
    ~TimeoutGuard() { camada::SMTLIBSolver::OneShotModelAckTimeoutMs = Saved; }
  } Guard;
  camada::SMTLIBSolver::OneShotModelAckTimeoutMs = 200;

  // Two shapes of silence: a child that never answers anything, and a
  // mono-style child that answers only (check-sat) and exits.
  const std::string SilentBody = "while read line; do :; done\n";
  const std::string MonoBody = "while read line; do\n"
                               "  case \"$line\" in\n"
                               "  '(check-sat)') echo sat; exit 0;;\n"
                               "  esac\n"
                               "done\n";
  for (const std::string &Body : {SilentBody, MonoBody}) {
    std::string Formula = makeTempPath();
    std::string Verdict = makeScript("echo sat\n");
    std::string Child = makeScript(Body);
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Verdict + " %f",
        std::vector<std::string>{Child});
    // Dropped during the preamble already.
    REQUIRE_FALSE(solver->oneShotModelSolverLive());

    auto X = solver->mkSymbol("x", solver->mkBVSort(8));
    solver->addConstraint(solver->mkEqual(X, solver->mkBVFromDec(5, 8)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    REQUIRE_FALSE(solver->oneShotModelVerdict().has_value());

    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Verdict.c_str());
    std::remove(Child.c_str());
  }
}

TEST_CASE("SMTLIB one-shot garbled model solver is dropped, not fatal",
          "[SMTLIB][oneshot]") {
  // A model child that answers unparseable lines used to hit fatalError
  // (killing the host process) at the first non-`success` ack. An
  // auxiliary child's garbage must cost only counterexample support.
  std::string Formula = makeTempPath();
  std::string Verdict = makeScript("echo sat\n");
  std::string Garbled = makeScript("while read line; do echo banana; done\n");
  auto solver = std::make_unique<camada::SMTLIBSolver>(
      camada::SMTLIBOneShotTag{}, Formula, Verdict + " %f",
      std::vector<std::string>{Garbled});
  REQUIRE_FALSE(solver->oneShotModelSolverLive());

  auto X = solver->mkSymbol("x", solver->mkBVSort(8));
  solver->addConstraint(solver->mkEqual(X, solver->mkBVFromDec(5, 8)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
  REQUIRE_FALSE(solver->oneShotModelVerdict().has_value());

  solver.reset();
  std::remove(Formula.c_str());
  std::remove(Verdict.c_str());
  std::remove(Garbled.c_str());
}

TEST_CASE("SMTLIB one-shot verdict handling", "[SMTLIB][oneshot]") {
  // Last verdict wins, and SAT-competition style is accepted.
  {
    std::string Formula = makeTempPath();
    std::string Script = makeScript("echo sat\necho 's UNSATISFIABLE'\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f");
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
  }
  // No verdict: UNKNOWN, with the command, exit status, and output tail
  // retrievable for the caller's diagnostics.
  {
    std::string Formula = makeTempPath();
    std::string Script =
        makeScript("echo '[fake] warming up'\necho '[fake] done'\nexit 3\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f");
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::checkResult::UNKNOWN);
    const camada::OneShotDiagnostics &D = solver->oneShotDiagnostics();
    REQUIRE(D.Command.find(Formula) != std::string::npos);
    REQUIRE(D.ExitStatus == "exit code 3");
    REQUIRE(D.OutputTail.find("[fake] warming up") != std::string::npos);
    REQUIRE(D.OutputTail.find("[fake] done") != std::string::npos);
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
  }
  // A verdict from a signal-killed solver is discarded: a truncated run
  // must not become a verification verdict.
  {
    std::string Formula = makeTempPath();
    std::string Script = makeScript("echo sat\nkill -9 $$\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f");
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::checkResult::UNKNOWN);
    REQUIRE(solver->oneShotDiagnostics().ExitStatus == "signal 9");
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
  }
}

TEST_CASE("SMTLIB one-shot %f substitution", "[SMTLIB][oneshot]") {
  // Every %f is replaced with the same (quoted) path.
  {
    std::string Formula = makeTempPath();
    std::string Script = makeScript(
        "test -f \"$1\" && test \"$1\" = \"$2\" && echo sat || echo unsat\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f %f");
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
  }
  // Without %f the quoted path is appended — even when it contains
  // characters a shell would otherwise split or interpret.
  {
    char Dir[] = "/tmp/camada one-shot XXXXXX";
    REQUIRE(::mkdtemp(Dir) != nullptr);
    std::string Formula = std::string(Dir) + "/it's a formula.smt2";
    std::string Script =
        makeScript("test -f \"$1\" && echo sat || echo unsat\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script);
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    solver.reset();
    std::remove(Formula.c_str());
    ::rmdir(Dir);
    std::remove(Script.c_str());
  }
}

TEST_CASE("SMTLIB one-shot diverging and dying model solvers",
          "[SMTLIB][oneshot]") {
  // Diverging: the one-shot solver claims sat on an unsatisfiable formula;
  // the model solver disagrees. Camada returns both verdicts and does NOT
  // abort — the caller compares and decides how to report it.
  {
    auto ModelArgv = z3ModelArgv();
    if (ModelArgv.empty())
      SKIP("no staged z3 binary for the model solver");
    std::string Formula = makeTempPath();
    std::string Script = makeScript("echo sat\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f", ModelArgv);
    auto A = solver->mkSymbol("a", solver->mkBoolSort());
    solver->addConstraint(A);
    solver->addConstraint(solver->mkNot(A));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    REQUIRE(solver->oneShotModelVerdict() == camada::checkResult::UNSAT);
    REQUIRE_FALSE(solver->oneShotModelSolverLive());
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
  }
  // Dying: a model solver that exits immediately is dropped; the one-shot
  // flow continues file-only without counterexample support.
  {
    std::string Formula = makeTempPath();
    std::string Script = makeScript("echo sat\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f",
        std::vector<std::string>{"false"});
    auto X = solver->mkSymbol("x", solver->mkBVSort(8));
    solver->addConstraint(solver->mkEqual(X, solver->mkBVFromDec(5, 8)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    REQUIRE_FALSE(solver->oneShotModelSolverLive());
    REQUIRE_FALSE(solver->oneShotModelVerdict().has_value());
    REQUIRE_FALSE(solver->getBV(X));
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
  }
}

TEST_CASE("SMTLIB one-shot assumption checks and mid-negotiation death",
          "[SMTLIB][oneshot]") {
  // checkSatAssuming must route through the one-shot flow (assumptions
  // land in the formula file inside a scope), not silently query only the
  // auxiliary model solver.
  {
    std::string Formula = makeTempPath();
    std::string Script = makeScript("echo sat\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f");
    auto A = solver->mkSymbol("a", solver->mkBoolSort());
    REQUIRE(solver->checkSatAssuming({A}) == camada::checkResult::SAT);
    std::string Written = readFile(Formula);
    REQUIRE(Written.find("(check-sat)") != std::string::npos);
    REQUIRE(Written.find("(push 1)") != std::string::npos);
    // The single-query restriction holds through this entry point too.
    requireAborts([&]() { (void)solver->check(); });
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
  }
  // A model child that rejects (set-logic ALL) and then dies exercises the
  // fallback branch of the preamble negotiation: it must degrade to
  // file-only, not abort the host.
  {
    std::string Formula = makeTempPath();
    std::string Script = makeScript("echo sat\n");
    // Ack the five preamble reads before set-logic, reject ALL, then exit:
    // print-success, produce-models, produce-unsat-assumptions,
    // global-declarations, set-info.
    std::string DyingModel = makeScript("echo success\n"
                                        "echo success\n"
                                        "echo success\n"
                                        "echo success\n"
                                        "echo success\n"
                                        "echo '(error \"no ALL here\")'\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f",
        std::vector<std::string>{DyingModel});
    REQUIRE_FALSE(solver->oneShotModelSolverLive());
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
    std::remove(DyingModel.c_str());
  }
}

TEST_CASE("SMTLIB caller-chosen logic", "[SMTLIB][logic]") {
  // Write-only: a non-empty Logic is emitted verbatim in place of ALL.
  {
    std::string Path = makeTempPath();
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        Path, camada::TupleEncoding::Native, "QF_BV");
    solver->addConstraint(solver->mkBool(true));
    (void)solver->check();
    solver.reset();
    std::string Written = readFile(Path);
    REQUIRE(Written.find("(set-logic QF_BV)") != std::string::npos);
    REQUIRE(Written.find("(set-logic ALL)") == std::string::npos);
    std::remove(Path.c_str());
  }
  // Empty Logic keeps today's behaviour.
  {
    std::string Path = makeTempPath();
    auto solver = std::make_unique<camada::SMTLIBSolver>(Path);
    solver->addConstraint(solver->mkBool(true));
    (void)solver->check();
    solver.reset();
    REQUIRE(readFile(Path).find("(set-logic ALL)") != std::string::npos);
    std::remove(Path.c_str());
  }
  // One-shot: the formula file carries the caller's logic.
  {
    std::string Formula = makeTempPath();
    std::string Script = makeScript("echo sat\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f",
        std::vector<std::string>{}, camada::PgidCallback{},
        camada::TupleEncoding::Native, "QF_BV");
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    REQUIRE(readFile(Formula).find("(set-logic QF_BV)") != std::string::npos);
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
  }
  // One-shot with an override AND a model child that dies right before the
  // set-logic read: the override branch must drop the child and still write
  // the caller's logic to the formula file, not abort.
  {
    std::string Formula = makeTempPath();
    std::string Script = makeScript("echo sat\n");
    // Ack the five preamble reads before set-logic, then exit.
    std::string DyingModel = makeScript("echo success\n"
                                        "echo success\n"
                                        "echo success\n"
                                        "echo success\n"
                                        "echo success\n");
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBOneShotTag{}, Formula, Script + " %f",
        std::vector<std::string>{DyingModel}, camada::PgidCallback{},
        camada::TupleEncoding::Native, "QF_BV");
    REQUIRE_FALSE(solver->oneShotModelSolverLive());
    solver->addConstraint(solver->mkBool(true));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    REQUIRE(readFile(Formula).find("(set-logic QF_BV)") != std::string::npos);
    solver.reset();
    std::remove(Formula.c_str());
    std::remove(Script.c_str());
    std::remove(DyingModel.c_str());
  }
}

TEST_CASE("SMTLIB caller-chosen logic against a child", "[SMTLIB][logic]") {
  auto ModelArgv = z3ModelArgv();
  if (ModelArgv.empty())
    SKIP("no staged z3 binary");

  // An accepted explicit logic solves normally, and the tee file mirrors
  // it — including after reset(), which re-runs the preamble from the
  // stored member.
  {
    std::string Path = makeTempPath();
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBProcessTag{}, ModelArgv, Path,
        camada::TupleEncoding::Native, "QF_AUFBV");
    auto X = solver->mkSymbol("x", solver->mkBVSort(8));
    solver->addConstraint(solver->mkEqual(X, solver->mkBVFromDec(7, 8)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    solver->reset();
    auto Y = solver->mkSymbol("y", solver->mkBVSort(8));
    solver->addConstraint(solver->mkEqual(Y, solver->mkBVFromDec(9, 8)));
    REQUIRE(solver->check() == camada::checkResult::SAT);
    solver.reset();
    std::string Written = readFile(Path);
    REQUIRE(Written.find("(set-logic QF_AUFBV)") != std::string::npos);
    REQUIRE(Written.find("(set-logic ALL)") == std::string::npos);
    // Both preambles (construction and reset) carried the override.
    auto First = Written.find("(set-logic QF_AUFBV)");
    REQUIRE(Written.find("(set-logic QF_AUFBV)", First + 1) !=
            std::string::npos);
    std::remove(Path.c_str());
  }
  // A rejected explicit logic is a fatal error, not a silent downgrade.
  requireAborts([&]() {
    auto solver = std::make_unique<camada::SMTLIBSolver>(
        camada::SMTLIBProcessTag{}, ModelArgv, camada::TupleEncoding::Native,
        "NOT_A_LOGIC");
    (void)solver->check();
  });
}
