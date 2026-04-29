// Helpers for the SMT-LIB pipeline tests, parameterized by the child-solver
// command. Each <solver>.test.cpp uses these helpers to spin up an
// SMTLIBSolver wired to that backend's child binary, then drives it through
// the same shared fixtures (tests.h, simple.test.h, fp.test.h, ...) used by
// the native backends. That gives us:
//   - one CTest entry per (test × solver), so failures point to a specific
//     pair, and per-solver capability subsets are decided by *which* fixtures
//     the per-solver test file invokes;
//   - reuse of the already-tested semantic checks from tests.h, instead of
//     re-deriving narrow versions for the SMT-LIB pipeline;
//   - a small set of pipeline-specific checks (kept inline below) for things
//     no native fixture covers: the public factory, dual file+pipe emission,
//     and the wide-BV / native-FP model-parsing edge cases that were only
//     ever bugs through the SMT-LIB pipe.
//
// Per-solver binary lookup: each solver gets its own command function
// (z3Command(), cvc5Command(), ...) that prefers the deps-staged binary
// (CAMADA_TEST_<NAME>_BIN, set by CMake) and falls back to PATH. Tests SKIP
// rather than fail when the binary isn't reachable.
//
// Solver wrapper: makeSMTLIBSolver(Cmd) returns an SMTSolverRef that drives
// the named child via the SMT-LIB pipe. Pass it directly to any of the
// existing fixture helpers — they're already polymorphic over SMTSolverRef.

#ifndef CAMADA_REGRESSION_SMTLIB_PIPELINE_TEST_H_
#define CAMADA_REGRESSION_SMTLIB_PIPELINE_TEST_H_

#include "camada.h"

#include <catch2/catch_test_macros.hpp>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <unistd.h>

namespace camada_smtlib_pipeline {

inline bool isExecutable(const std::string &Path) {
  return ::access(Path.c_str(), X_OK) == 0;
}

// Try the compile-time hint first, then `command -v <Name>` on PATH.
// Returns empty string if neither resolves to an executable.
inline std::string findExecutable(const std::string &Name,
                                  const char *HintBin) {
  if (HintBin && *HintBin && isExecutable(HintBin))
    return HintBin;
  std::string ProbeCmd = "command -v " + Name;
  if (FILE *P = ::popen(ProbeCmd.c_str(), "r")) {
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

// Per-solver command lookup.
inline std::string z3Command() {
#ifdef CAMADA_TEST_Z3_BIN
  std::string Bin = findExecutable("z3", CAMADA_TEST_Z3_BIN);
#else
  std::string Bin = findExecutable("z3", nullptr);
#endif
  return Bin.empty() ? std::string{} : Bin + " -in";
}

inline std::string cvc5Command() {
#ifdef CAMADA_TEST_CVC5_BIN
  std::string Bin = findExecutable("cvc5", CAMADA_TEST_CVC5_BIN);
#else
  std::string Bin = findExecutable("cvc5", nullptr);
#endif
  // --incremental is required for (push)/(pop). --arrays-exp enables cvc5's
  // experimental array support, which covers `((as const ...))` const-array
  // literals — without it cvc5 emits "Cannot handle assertion with term of
  // kind STORE_ALL" and the formula returns unknown.
  return Bin.empty() ? std::string{}
                     : Bin + " --lang smt2 --incremental --arrays-exp";
}

inline std::string bitwuzlaCommand() {
#ifdef CAMADA_TEST_BITWUZLA_BIN
  std::string Bin = findExecutable("bitwuzla", CAMADA_TEST_BITWUZLA_BIN);
#else
  std::string Bin = findExecutable("bitwuzla", nullptr);
#endif
  return Bin;
}

inline std::string yicesSmt2Command() {
#ifdef CAMADA_TEST_YICES_SMT2_BIN
  std::string Bin = findExecutable("yices-smt2", CAMADA_TEST_YICES_SMT2_BIN);
#else
  std::string Bin = findExecutable("yices-smt2", nullptr);
#endif
  return Bin.empty() ? std::string{} : Bin + " --incremental";
}

inline std::string mathsatCommand() {
#ifdef CAMADA_TEST_MATHSAT_BIN
  std::string Bin = findExecutable("mathsat", CAMADA_TEST_MATHSAT_BIN);
#else
  std::string Bin = findExecutable("mathsat", nullptr);
#endif
  return Bin;
}

// Build an SMTSolverRef driving the given child command. The returned ref
// works with any fixture helper that takes `const camada::SMTSolverRef &`.
inline camada::SMTSolverRef makeSMTLIBSolver(const std::string &Cmd) {
  return camada::createSMTLIBSolver(Cmd);
}

// Skip the test if the binary isn't reachable.
#define CAMADA_SMTLIB_REQUIRE_BINARY(CmdExpr, Name)                            \
  std::string Cmd = (CmdExpr);                                                 \
  if (Cmd.empty())                                                             \
    SKIP(std::string(Name) + " binary not found on PATH or in deps install");

// =============================================================================
// SMT-LIB-pipeline-specific helpers. These exercise behaviors that don't have
// a counterpart in the existing shared fixtures: the createSMTLIBSolver
// factory itself, dual file+pipe emission, and the model-value parsing for
// shapes that only the SMT-LIB pipeline produces (wide BV decimal, native FP
// special constants).
// =============================================================================

inline std::string makeTempPath() {
  char Tmp[] = "/tmp/camada-smtlib-XXXXXX";
  int Fd = ::mkstemp(Tmp);
  REQUIRE(Fd >= 0);
  ::close(Fd);
  return std::string(Tmp);
}

inline std::string readFile(const std::string &Path) {
  std::ifstream In(Path);
  REQUIRE(In.good());
  std::stringstream Ss;
  Ss << In.rdbuf();
  return Ss.str();
}

// The createSMTLIBSolver(Cmd) public factory must produce a solver that can
// drive a trivial round-trip through the child.
inline void runSMTLIBPublicFactory(const std::string &Cmd) {
  auto Solver = camada::createSMTLIBSolver(Cmd);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(1, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

// The dual-emitter form (Cmd + path) must drive the child AND tee the script
// to disk simultaneously.
inline void runSMTLIBDualEmitter(const std::string &Cmd) {
  std::string Path = makeTempPath();
  {
    auto Solver = camada::createSMTLIBSolver(Cmd, Path);
    auto BV8 = Solver->mkBVSort(8);
    auto X = Solver->mkSymbol("x", BV8);
    Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(3, BV8)));
    REQUIRE(Solver->check() == camada::checkResult::SAT);
  }
  std::string Got = readFile(Path);
  std::remove(Path.c_str());
  REQUIRE(Got.find("(declare-fun |x| () (_ BitVec 8))\n") != std::string::npos);
  REQUIRE(Got.find("(assert (= |x| #b00000011))\n") != std::string::npos);
  REQUIRE(Got.find("(check-sat)\n") != std::string::npos);
}

} // namespace camada_smtlib_pipeline

#endif // CAMADA_REGRESSION_SMTLIB_PIPELINE_TEST_H_
