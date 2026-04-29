// Helpers for the SMT-LIB pipeline tests, parameterized by the child-solver
// command. Each <solver>.test.cpp picks up only the helpers its solver
// supports and wraps them in TEST_CASEs tagged with that solver's name. This
// gives one CTest entry per (test × solver) — clearer than a Catch2-internal
// matrix loop, since CTest can show pass/fail per solver and the discovery
// is rooted in the existing `compile_test` machinery.
//
// Layout:
//   - findExecutable / smtlib_<name>_command: per-solver binary lookup that
//     prefers the deps-staged binary and falls back to PATH. Returns the full
//     shell command, or "" if neither is reachable.
//   - runSMTLIB_<scenario>(Cmd): executes one pipeline scenario against the
//     given child-solver command. Bodies are unchanged from the previous
//     matrix-style tests in smtlib.test.cpp.

#ifndef CAMADA_REGRESSION_SMTLIB_PIPELINE_TEST_H_
#define CAMADA_REGRESSION_SMTLIB_PIPELINE_TEST_H_

#include "camada.h"
#include "smtlibsolver.h"

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

// Per-solver command lookup. Each function returns the full shell command
// suitable for camada::createSMTLIBSolver(), or "" if the binary isn't
// reachable. The CAMADA_TEST_<NAME>_BIN macros are defined by CMake when the
// deps build staged the binary.
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
  return Bin.empty() ? std::string{} : Bin + " --lang smt2 --incremental";
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

// Test-helper macro: skip this test if the named solver's binary is not
// reachable. Each solver's test file uses the variant matching its own
// command lookup. The skip is rare in practice — the test only compiles in
// when the solver's C-API library is available, and the binaries ship from
// the same dep build.
#define CAMADA_SMTLIB_REQUIRE_BINARY(CmdExpr, Name)                            \
  std::string Cmd = (CmdExpr);                                                 \
  if (Cmd.empty())                                                             \
    SKIP(std::string(Name) + " binary not found on PATH or in deps install");

// Helper to read an entire file into a string (for the dual-emitter test).
inline std::string readFile(const std::string &Path) {
  std::ifstream In(Path);
  REQUIRE(In.good());
  std::stringstream Ss;
  Ss << In.rdbuf();
  return Ss.str();
}

inline std::string makeTempPath() {
  char Tmp[] = "/tmp/camada-smtlib-XXXXXX";
  int Fd = ::mkstemp(Tmp);
  REQUIRE(Fd >= 0);
  ::close(Fd);
  return std::string(Tmp);
}

// =============================================================================
// Scenario helpers. Each one runs a single pipeline scenario against the given
// child-solver command. The bodies are extracted verbatim from the previous
// matrix-style tests in smtlib.test.cpp.
// =============================================================================

inline void runSMTLIBPublicFactory(const std::string &Cmd) {
  auto Solver = camada::createSMTLIBSolver(Cmd);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(1, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

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

inline void runSMTLIBSatProblem(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(5, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

inline void runSMTLIBUnsatProblem(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(5, BV8)));
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(7, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::UNSAT);
}

inline void runSMTLIBGetBV(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(42, BV8)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Result = Solver->getBV(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == 42);
}

inline void runSMTLIBGetBV1Bit(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BV1 = Solver->mkBVSort(1);
  auto B = Solver->mkSymbol("b", BV1);
  Solver->addConstraint(Solver->mkEqual(B, Solver->mkBVFromBin("1", 1)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  // 1-bit BV with the high (and only) bit set is -1 in two's complement.
  auto Result = Solver->getBV(B);
  REQUIRE(Result);
  REQUIRE(Result.value() == -1);
  auto Bin = Solver->getBVInBin(B);
  REQUIRE(Bin);
  REQUIRE(Bin.value() == "1");
}

inline void runSMTLIBPushPop(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
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

inline void runSMTLIBSymbolSurvivesPop(const std::string &Cmd) {
  // Without (set-option :global-declarations true), declarations made inside
  // a (push) are dropped on (pop) and follow-up references would fail with
  // "unknown constant" in the child solver.
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
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

inline void runSMTLIBGetBVInBin128(const std::string &Cmd) {
  // Some solvers (e.g. MathSAT) emit BV model values in `(_ bv<n> <w>)` decimal
  // form. Widths above 64 must still parse correctly.
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BV128 = Solver->mkBVSort(128);
  auto X = Solver->mkSymbol("x", BV128);
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkBVFromDec(42, BV128)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Bin = Solver->getBVInBin(X);
  REQUIRE(Bin);
  std::string Expected(128, '0');
  Expected.replace(Expected.size() - 6, 6, "101010");
  REQUIRE(Bin.value() == Expected);
}

inline void runSMTLIBGetFP32BVEncoded(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto FP32 = Solver->mkFP32Sort(camada::FPEncoding::BV);
  auto X = Solver->mkSymbol("x", FP32);
  Solver->addConstraint(
      Solver->mkEqual(X, Solver->mkFP32(2.5f, camada::FPEncoding::BV)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Result = Solver->getFP32(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == 2.5f);
}

inline void runSMTLIBGetFP64BVEncoded(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto FP64 = Solver->mkFP64Sort(camada::FPEncoding::BV);
  auto X = Solver->mkSymbol("x", FP64);
  Solver->addConstraint(
      Solver->mkEqual(X, Solver->mkFP64(-3.14, camada::FPEncoding::BV)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Result = Solver->getFP64(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == -3.14);
}

inline void runSMTLIBGetFP32Native(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto FP32 = Solver->mkFP32Sort(camada::FPEncoding::Native);
  auto X = Solver->mkSymbol("x", FP32);
  Solver->addConstraint(
      Solver->mkEqual(X, Solver->mkFP32(2.5f, camada::FPEncoding::Native)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Result = Solver->getFP32(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == 2.5f);
}

inline void runSMTLIBGetFP64Native(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto FP64 = Solver->mkFP64Sort(camada::FPEncoding::Native);
  auto X = Solver->mkSymbol("x", FP64);
  Solver->addConstraint(
      Solver->mkEqual(X, Solver->mkFP64(-3.14, camada::FPEncoding::Native)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Result = Solver->getFP64(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == -3.14);
}

inline void runSMTLIBNativeFPAdd(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto FP32 = Solver->mkFP32Sort(camada::FPEncoding::Native);
  auto X = Solver->mkSymbol("x", FP32);
  auto RM = Solver->mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::Native);
  auto OnePointFive = Solver->mkFP32(1.5f, camada::FPEncoding::Native);
  auto Two = Solver->mkFP32(2.0f, camada::FPEncoding::Native);
  Solver->addConstraint(
      Solver->mkEqual(X, Solver->mkFPAdd(OnePointFive, Two, RM)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Result = Solver->getFP32(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == 3.5f);
}

inline void runSMTLIBNativeFPInfinity(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto FP32 = Solver->mkFP32Sort(camada::FPEncoding::Native);
  auto X = Solver->mkSymbol("x", FP32);
  Solver->addConstraint(Solver->mkEqual(
      X, Solver->mkInf(false, 8, 24, camada::FPEncoding::Native)));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Bin = Solver->getFPInBin(X);
  REQUIRE(Bin);
  REQUIRE(Bin.value() == "01111111100000000000000000000000");
}

inline void runSMTLIBNativeFPNegFlipNaN(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto FP32 = Solver->mkFP32Sort(camada::FPEncoding::Native);
  auto X = Solver->mkSymbol("x", FP32);
  Solver->addConstraint(Solver->mkFPIsNaN(X));
  auto Negged = Solver->mkFPNeg(X, camada::FPNegBehavior::FlipSignBit);
  auto XBits = Solver->mkIEEEFPToBV(X);
  auto NeggedBits = Solver->mkIEEEFPToBV(Negged);
  auto XSign = Solver->mkBVExtract(31, 31, XBits);
  auto NSign = Solver->mkBVExtract(31, 31, NeggedBits);
  Solver->addConstraint(Solver->mkEqual(NSign, Solver->mkBVNot(XSign)));
  auto XRest = Solver->mkBVExtract(30, 0, XBits);
  auto NRest = Solver->mkBVExtract(30, 0, NeggedBits);
  Solver->addConstraint(Solver->mkEqual(NRest, XRest));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

inline void runSMTLIBNativeFPNaNModel(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto FP32 = Solver->mkFP32Sort(camada::FPEncoding::Native);
  auto X = Solver->mkSymbol("x", FP32);
  Solver->addConstraint(Solver->mkFPIsNaN(X));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Bin = Solver->getFPInBin(X);
  REQUIRE(Bin);
  REQUIRE(Bin.value().substr(0, 9) == "011111111");
  REQUIRE(Bin.value().substr(9).find('1') != std::string::npos);
}

inline void runSMTLIBGetArrayElement(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto IdxSort = Solver->mkBVSort(3);
  auto ElemSort = Solver->mkBVSort(8);
  auto ArrSort = Solver->mkArraySort(IdxSort, ElemSort);
  auto Arr = Solver->mkSymbol("a", ArrSort);
  auto Idx = Solver->mkBVFromDec(2, IdxSort);
  auto Val = Solver->mkBVFromDec(99, ElemSort);
  auto Updated = Solver->mkArrayStore(Arr, Idx, Val);
  Solver->addConstraint(
      Solver->mkEqual(Solver->mkArraySelect(Updated, Idx), Val));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Selected = Solver->getArrayElement(Updated, Idx);
  REQUIRE(Selected->Sort == ElemSort);
  auto Bin = Solver->getBVInBin(Selected);
  REQUIRE(Bin);
  REQUIRE(Bin.value() == "01100011"); // 99
}

inline void runSMTLIBGetIntPositive(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto X = Solver->mkSymbol("x", Solver->mkIntSort());
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkInt(int64_t{42})));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Result = Solver->getInt(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == "42");
}

inline void runSMTLIBGetIntNegative(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto X = Solver->mkSymbol("x", Solver->mkIntSort());
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkInt(int64_t{-7})));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Result = Solver->getInt(X);
  REQUIRE(Result);
  REQUIRE(Result.value() == "-7");
}

inline void runSMTLIBIntArithCompare(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto Int = Solver->mkIntSort();
  auto X = Solver->mkSymbol("x", Int);
  auto Y = Solver->mkSymbol("y", Int);
  Solver->addConstraint(
      Solver->mkEqual(Solver->mkArithAdd(X, Y), Solver->mkInt(int64_t{10})));
  Solver->addConstraint(Solver->mkArithGt(X, Y));
  Solver->addConstraint(Solver->mkEqual(X, Solver->mkInt(int64_t{7})));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Yval = Solver->getInt(Y);
  REQUIRE(Yval);
  REQUIRE(Yval.value() == "3");
}

inline void runSMTLIBGetRationalPositive(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto Y = Solver->mkSymbol("y", Solver->mkRealSort());
  Solver->addConstraint(
      Solver->mkEqual(Y, Solver->mkReal(int64_t{3}, int64_t{4})));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Num = Solver->getRealNumerator(Y);
  auto Den = Solver->getRealDenominator(Y);
  REQUIRE(Num);
  REQUIRE(Den);
  REQUIRE(Num.value() == "3");
  REQUIRE(Den.value() == "4");
}

inline void runSMTLIBGetRationalNegative(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto Y = Solver->mkSymbol("y", Solver->mkRealSort());
  Solver->addConstraint(
      Solver->mkEqual(Y, Solver->mkReal(int64_t{-7}, int64_t{8})));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Num = Solver->getRealNumerator(Y);
  auto Den = Solver->getRealDenominator(Y);
  REQUIRE(Num);
  REQUIRE(Den);
  REQUIRE(Num.value() == "-7");
  REQUIRE(Den.value() == "8");
}

inline void runSMTLIBIntRealConvIsInt(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  // (to_real 5) = 5.0  →  is_int(5.0) = true
  auto Five = Solver->mkInt(int64_t{5});
  auto FiveReal = Solver->mkInt2Real(Five);
  Solver->addConstraint(Solver->mkIsInt(FiveReal));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  Solver->reset();
  // (to_int 7.5) = 7
  auto SevenHalf = Solver->mkReal(int64_t{15}, int64_t{2});
  auto Seven = Solver->mkReal2Int(SevenHalf);
  Solver->addConstraint(Solver->mkEqual(Seven, Solver->mkInt(int64_t{7})));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

inline void runSMTLIBUF(const std::string &Cmd) {
  // f : BV8 -> BV8. Constrain f(0) = 5, then check f's value at 0 in the
  // model.
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BV8 = Solver->mkBVSort(8);
  auto FuncSort = Solver->mkFunctionSort({BV8}, BV8);
  auto F = Solver->mkSymbol("f", FuncSort);
  auto Zero = Solver->mkBVFromDec(0, BV8);
  auto Five = Solver->mkBVFromDec(5, BV8);
  auto FZero = Solver->mkApply(F, {Zero});
  Solver->addConstraint(Solver->mkEqual(FZero, Five));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto Bin = Solver->getBVInBin(FZero);
  REQUIRE(Bin);
  REQUIRE(Bin.value() == "00000101");
}

inline void runSMTLIBForall(const std::string &Cmd) {
  // (forall ((x BV8)) (= x x)) is trivially valid.
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  auto Body = Solver->mkEqual(X, X);
  Solver->addConstraint(Solver->mkForall({X}, Body));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

inline void runSMTLIBExists(const std::string &Cmd) {
  // (exists ((x BV8)) (= x #x05)) is satisfiable.
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BV8 = Solver->mkBVSort(8);
  auto X = Solver->mkSymbol("x", BV8);
  auto Body = Solver->mkEqual(X, Solver->mkBVFromDec(5, BV8));
  Solver->addConstraint(Solver->mkExists({X}, Body));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

inline void runSMTLIBTupleProjection(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto BoolS = Solver->mkBoolSort();
  auto BV8 = Solver->mkBVSort(8);
  auto TupSort = Solver->mkTupleSort({BoolS, BV8});
  auto T = Solver->mkSymbol("t", TupSort);
  auto Tup =
      Solver->mkTuple({Solver->mkBool(true), Solver->mkBVFromDec(42, BV8)});
  Solver->addConstraint(Solver->mkEqual(T, Tup));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
  auto B = Solver->mkTupleSelect(T, 0);
  auto V = Solver->mkTupleSelect(T, 1);
  auto BVal = Solver->getBool(B);
  auto VBin = Solver->getBVInBin(V);
  REQUIRE(BVal);
  REQUIRE(VBin);
  REQUIRE(BVal.value() == true);
  REQUIRE(VBin.value() == "00101010"); // 42
}

inline void runSMTLIBEmptyTuple(const std::string &Cmd) {
  auto Solver =
      std::make_unique<camada::SMTLIBSolver>(camada::SMTLIBProcessTag{}, Cmd);
  auto TupSort = Solver->mkTupleSort({});
  auto T = Solver->mkSymbol("e", TupSort);
  Solver->addConstraint(Solver->mkEqual(T, Solver->mkTuple({})));
  REQUIRE(Solver->check() == camada::checkResult::SAT);
}

} // namespace camada_smtlib_pipeline

#endif // CAMADA_REGRESSION_SMTLIB_PIPELINE_TEST_H_
