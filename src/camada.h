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

#ifndef CAMADA_H_
#define CAMADA_H_

#include <climits>
#include <memory>

#include "camadaexpr.h"
#include "camadasort.h"

namespace camada {

/// Return camada version
std::string getCamadaVersion();

/// Abort program if Cond is false and prints Msg to stderr
void abortCondWithMessage(bool Cond, const std::string &Msg);

/// Abort program and prints Msg to stderr
[[noreturn]] void abortWithMessage(const std::string &Msg);

enum class checkResult { SAT, UNSAT, UNKNOWN };

enum class RoundingMode {
  ROUND_TO_EVEN = 0,
  ROUND_TO_AWAY = 1,
  ROUND_TO_PLUS_INF = 2,
  ROUND_TO_MINUS_INF = 3,
  ROUND_TO_ZERO = 4,
};

/// Generic base class for SMT Solvers
///
/// This class is responsible for wrapping all sorts and expression generation,
/// through the mk* methods. It also provides methods to create SMT expressions
/// straight from clang's Expr, through the from* methods.
class SMTSolver {
public:
  SMTSolver() = default;
  virtual ~SMTSolver() = default;

  /// Wrapper to create new SMTSort
  template <typename SolverSort>
  SMTSortRef newSortRef(const SMTSort &Sort) const {
    return std::make_shared<SolverSort>(toSolverSort<SolverSort>(Sort));
  }

  /// Wrapper to create new SMTExpr
  virtual SMTExprRef newExprRef(const SMTExpr &Exp) const = 0;

  /// Returns a boolean sort.
  virtual SMTSortRef getBoolSort() = 0;

  /// Returns an appropriate bitvector sort for the given bitwidth.
  virtual SMTSortRef getBitvectorSort(const unsigned BitWidth) = 0;

  /// Returns an appropriate rounding mode sort.
  virtual SMTSortRef getRoundingModeSort() = 0;

  /// Returns an appropriate floating-point sort for the given bitwidth.
  virtual SMTSortRef getFPSort(const unsigned ExpWidth,
                               const unsigned SigWidth) = 0;

  /// Convenience method to create a 32 bits long a floating-point sort.
  SMTSortRef getFP32Sort() { return getFPSort(8, 24); }

  /// Convenience method to create a 64 bits long a floating-point sort.
  SMTSortRef getFP64Sort() { return getFPSort(11, 53); }

  /// Given a constraint, adds it to the solver
  virtual void addConstraint(const SMTExprRef &Exp) = 0;

  /// Creates a bitvector addition operation
  virtual SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector subtraction operation
  virtual SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector multiplication operation
  virtual SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed modulus operation
  virtual SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned modulus operation
  virtual SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed division operation
  virtual SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned division operation
  virtual SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector logical shift left operation
  virtual SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector arithmetic shift right operation
  virtual SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector logical shift right operation
  virtual SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector negation operation
  virtual SMTExprRef mkBVNeg(const SMTExprRef &Exp) = 0;

  /// Creates a bitvector not operation
  virtual SMTExprRef mkBVNot(const SMTExprRef &Exp) = 0;

  /// Creates a bitvector xor operation
  virtual SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector or operation
  virtual SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector and operation
  virtual SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned less-than operation
  virtual SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed less-than operation
  virtual SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned greater-than operation
  virtual SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkBVUle(LHS, RHS));
  }

  /// Creates a bitvector signed greater-than operation
  virtual SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkBVSle(LHS, RHS));
  }

  /// Creates a bitvector unsigned less-equal-than operation
  virtual SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed less-equal-than operation
  virtual SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned greater-equal-than operation
  virtual SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkBVUlt(LHS, RHS));
  }

  /// Creates a bitvector signed greater-equal-than operation
  virtual SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkBVSlt(LHS, RHS));
  }

  /// Creates a boolean not operation
  virtual SMTExprRef mkNot(const SMTExprRef &Exp) = 0;

  /// Creates a boolean equality operation
  virtual SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean and operation
  virtual SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean or operation
  virtual SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean xor operation
  virtual SMTExprRef mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean ite operation
  virtual SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                           const SMTExprRef &F) = 0;

  /// Creates a bitvector sign extension operation
  virtual SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) = 0;

  /// Creates a bitvector zero extension operation
  virtual SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) = 0;

  /// Creates a bitvector extract operation
  virtual SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                                 const SMTExprRef &Exp) = 0;

  /// Creates a bitvector concat operation
  virtual SMTExprRef mkBVConcat(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  SMTExprRef mkBVRedOr(SMTExprRef Exp) {
    // bvredor = bvnot(bvcomp(x,0)) ? bv1 : bv0;
    SMTExprRef comp = mkEqual(Exp, mkBitvector(0, Exp->getWidth()));
    return mkIte(mkNot(comp), mkBitvector(1, 1), mkBitvector(0, 1));
  }

  SMTExprRef mkBVRedAnd(SMTExprRef Exp) {
    // bvredand = bvcomp(x,-1) ? bv1 : bv0;
    SMTExprRef comp = mkEqual(Exp, mkBitvector(ULLONG_MAX, Exp->getWidth()));
    return mkIte(comp, mkBitvector(1, 1), mkBitvector(0, 1));
  }

  /// Creates a floating-point absolute operation
  virtual SMTExprRef mkFPAbs(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point negation operation
  virtual SMTExprRef mkFPNeg(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isInfinite operation
  virtual SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isNaN operation
  virtual SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isNormal operation
  virtual SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isNormal operation
  virtual SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isZero operation
  virtual SMTExprRef mkFPIsZero(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point multiplication operation
  virtual SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) = 0;

  /// Creates a floating-point division operation
  virtual SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) = 0;

  /// Creates a floating-point remainder operation
  virtual SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point addition operation
  virtual SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) = 0;

  /// Creates a floating-point subtraction operation
  virtual SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) = 0;

  /// Creates a floating-point square root operation
  virtual SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const RoundingMode R) = 0;

  /// Creates a floating-point fused-multiply add operation: round((x * y) + z)
  virtual SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z, const RoundingMode R) = 0;

  /// Creates a floating-point less-than operation
  virtual SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point greater-than operation
  virtual SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkFPLt(RHS, LHS);
  }

  /// Creates a floating-point less-than-or-equal operation
  virtual SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point greater-than-or-equal operation
  virtual SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkNot(mkFPLt(RHS, LHS));
  }

  /// Creates a floating-point equality operation
  virtual SMTExprRef mkFPEqual(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates a floating-point conversion from floatint-point to floating-point
  /// operation
  virtual SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const RoundingMode R) = 0;

  /// Creates a floating-point conversion from signed bitvector to
  /// floatint-point operation
  virtual SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) = 0;

  /// Creates a floating-point conversion from unsigned bitvector to
  /// floatint-point operation
  virtual SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) = 0;

  /// Creates a floating-point conversion from floatint-point to signed
  /// bitvector operation
  virtual SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floatint-point to unsigned
  /// bitvector operation
  virtual SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floatint-point to the closest
  /// integer, considering the rounding mode.
  virtual SMTExprRef mkFPtoIntegral(const SMTExprRef &From, RoundingMode R) = 0;

  /// If the a model is available, returns the value of a given boolean symbol
  virtual bool getBool(const SMTExprRef &Exp) = 0;

  /// If the a model is available, returns the value of a given bitvector
  /// symbol as a 64-bits int
  virtual int64_t getBitvector(const SMTExprRef &Exp) = 0;

  /// If the a model is available, returns the value of a given floating-point
  /// symbol as float
  virtual float getFP(const SMTExprRef &Exp) = 0;

  /// If the a model is available, returns the value of a given floating-point
  /// symbol as double
  virtual double getDouble(const SMTExprRef &Exp) = 0;

  /// Constructs an SMTExprRef from a boolean.
  virtual SMTExprRef mkBool(const bool b) = 0;

  /// Constructs an SMTExprRef from an integer and its bit width
  virtual SMTExprRef mkBitvector(const int64_t Int, const SMTSortRef &Sort) = 0;

  /// Convinience method to create a bitvector using the value and the bitwidth
  virtual SMTExprRef mkBitvector(const int64_t Int, unsigned BitWidth) {
    return mkBitvector(Int, getBitvectorSort(BitWidth));
  }

  /// Creates a new symbol, given a name and a sort
  virtual SMTExprRef mkSymbol(const char *Name, SMTSortRef Sort) = 0;

  /// Constructs an SMTExprRef from a float.
  virtual SMTExprRef mkFP(const float Float) = 0;

  /// Constructs an SMTExprRef from a double.
  virtual SMTExprRef mkDouble(const double Double) = 0;

  /// Returns an appropriate floating-point rounding mode.
  virtual SMTExprRef mkRoundingMode(const RoundingMode R) = 0;

  /// Convenience method to create 32 bits long NaN
  SMTExprRef mkNaN32(const bool Sgn) { return mkNaN(Sgn, 8, 24); }

  /// Convenience method to create 64 bits long NaN
  SMTExprRef mkNaN64(const bool Sgn) { return mkNaN(Sgn, 11, 53); }

  /// Convenience method to create 32 bits long Inf
  SMTExprRef mkInf32(const bool Sgn) { return mkInf(Sgn, 8, 24); }

  /// Convenience method to create 64 bits long Inf
  SMTExprRef mkInf64(const bool Sgn) { return mkInf(Sgn, 11, 53); }

  /// Reinterpret a bitvector as a floating-point, using the IEEE format
  virtual SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp,
                                  const SMTSortRef &To) = 0;

  /// Reinterpret a floating-point as a bitvector, using the IEEE format
  virtual SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) = 0;

  /// Check if the constraints are satisfiable
  virtual checkResult check() = 0;

  /// Reset the solver and remove all constraints.
  virtual void reset() = 0;

  /// Dump formula
  virtual void dump();

  /// Dump Model
  virtual void dumpModel();

protected:
  /// Flag to enable encoding floating-points using bitvectors even if the
  /// solver supports floating-points. For solvers that don't support
  /// floating-point arithmetic, bitvectors will be used even if this flag is
  /// false
  bool useCamadaFP = false;

  /// Returns a NaN floating-point
  virtual SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) = 0;

  /// Returns a Inf floating-point
  virtual SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) = 0;

  /// Returns an appropriate floating-point sort, encoded as a bitvector.
  virtual SMTSortRef getBVFPSort(const unsigned ExpWidth,
                                 const unsigned SigWidth) = 0;

  /// Returns an appropriate rounding mode sort, encoded as a bitvector.
  virtual SMTSortRef getBVRoundingModeSort() = 0;
};

/// Shared pointer for SMTSolvers.
using SMTSolverRef = std::shared_ptr<SMTSolver>;

/// Convenience method to create a Z3Solver object
SMTSolverRef createZ3Solver();

/// Convenience method to create a MathSATSolver object
SMTSolverRef createMathSATSolver();

/// Convenience method to create a CVC4Solver object
SMTSolverRef createCVC4Solver();

/// Convenience method to create a BoolectorSolver object
SMTSolverRef createBoolectorSolver();

/// Convenience method to create a YicesSolver object
SMTSolverRef createYicesSolver();

} // namespace camada

#endif
