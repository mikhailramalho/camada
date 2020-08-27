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

#include <string>

#include "camadaexpr.h"

namespace camada {

/// Return camada version
std::string getCamadaVersion();

enum class checkResult { SAT, UNSAT, UNKNOWN };

enum class RM {
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
  SMTSortRef newSortRef(const SolverSort &Sort) const {
    return std::make_shared<SolverSort>(Sort);
  }

  /// Wrapper to create new SMTExpr
  virtual SMTExprRef newExprRef(const SMTExpr &Exp) const = 0;

  /// Returns a boolean sort.
  virtual SMTSortRef mkBoolSort() = 0;

  /// Returns an appropriate bitvector sort for the given bitwidth.
  virtual SMTSortRef mkBVSort(const unsigned BitWidth) = 0;

  /// Returns an appropriate rounding mode sort.
  virtual SMTSortRef mkRMSort() = 0;

  /// Returns an appropriate floating-point sort for the given bitwidth.
  virtual SMTSortRef mkFPSort(const unsigned ExpWidth,
                              const unsigned SigWidth) = 0;

  /// Convenience method to create a 32 bits long a floating-point sort.
  SMTSortRef mkFP32Sort() { return mkFPSort(8, 23); }

  /// Convenience method to create a 64 bits long a floating-point sort.
  SMTSortRef mkFP64Sort() { return mkFPSort(11, 52); }

  /// Returns an appropriate array sort.
  virtual SMTSortRef mkArraySort(const SMTSortRef &IndexSort,
                                 const SMTSortRef &ElemSort) = 0;

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
  virtual SMTExprRef mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
    return mkAnd(mkOr(LHS, RHS), mkNot(mkAnd(LHS, RHS)));
  }

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

  SMTExprRef mkBVRedOr(const SMTExprRef &Exp) {
    // bvredor = bvnot(bvcomp(x,0)) ? bv1 : bv0;
    SMTExprRef comp = mkEqual(Exp, mkBVFromDec(0, Exp->getWidth()));
    return mkIte(mkNot(comp), mkBVFromDec(1, 1), mkBVFromDec(0, 1));
  }

  SMTExprRef mkBVRedAnd(const SMTExprRef &Exp) {
    // bvredand = bvcomp(x,-1) ? bv1 : bv0;
    SMTExprRef comp = mkEqual(Exp, mkBVFromDec(-1, Exp->getWidth()));
    return mkIte(comp, mkBVFromDec(1, 1), mkBVFromDec(0, 1));
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
                             const RM &R) = 0;

  /// Creates a floating-point division operation
  virtual SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RM &R) = 0;

  /// Creates a floating-point remainder operation
  virtual SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point addition operation
  virtual SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RM &R) = 0;

  /// Creates a floating-point subtraction operation
  virtual SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RM &R) = 0;

  /// Creates a floating-point square root operation
  virtual SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const RM &R) = 0;

  /// Creates a floating-point fused-multiply add operation: round((x * y) + z)
  virtual SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z, const RM &R) = 0;

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
                              const RM &R) = 0;

  /// Creates a floating-point conversion from signed bitvector to
  /// floatint-point operation
  virtual SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RM &R) = 0;

  /// Creates a floating-point conversion from unsigned bitvector to
  /// floatint-point operation
  virtual SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RM &R) = 0;

  /// Creates a floating-point conversion from floatint-point to signed
  /// bitvector operation
  virtual SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floatint-point to unsigned
  /// bitvector operation
  virtual SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floatint-point to the closest
  /// integer, considering the rounding mode.
  virtual SMTExprRef mkFPtoIntegral(const SMTExprRef &From, const RM &R) = 0;

  /// Creates an array select operation. It returns the element in position
  /// Index of Array.
  virtual SMTExprRef mkArraySelect(const SMTExprRef &Array,
                                   const SMTExprRef &Index) = 0;

  /// Creates an array store operation. It stores Element in position Index of
  /// Array.
  virtual SMTExprRef mkArrayStore(const SMTExprRef &Array,
                                  const SMTExprRef &Index,
                                  const SMTExprRef &Element) = 0;

  /// If a model is available, returns the value of a given boolean symbol
  virtual bool getBool(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given bitvector
  /// symbol as a 64-bits int
  int64_t getBV(const SMTExprRef &Exp);

  /// If a model is available, returns the value of a given bitvector
  /// symbol as a 2-complement form binary string
  virtual std::string getBVInBin(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given floating-point
  /// symbol as a binary string in the IEEE-754 format: 1 bit for the sign + N
  /// bits for the exponent + M bits for the significand
  virtual std::string getFPInBin(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given floating-point
  /// symbol as float. We assume the floating-point is using the IEEE-754
  /// format: 1 bit for the sign + 8 bits for the exponent + 23 bits for the
  /// significand and 1 hidden bit in the significand
  float getFP32(const SMTExprRef &Exp);

  /// If a model is available, returns the value of a given floating-point
  /// symbol as double. We assume the floating-point is using the IEEE-754
  /// format: 1 bit for the sign + 11 bits for the exponent + 52 bits for the
  /// significand and 1 hidden bit in the significand
  double getFP64(const SMTExprRef &Exp);

  /// If a model is available, returns the Expr in position Index of Array
  virtual SMTExprRef getArrayElement(const SMTExprRef &Array,
                                     const SMTExprRef &Index) = 0;

  /// Constructs an SMTExprRef from a boolean.
  virtual SMTExprRef mkBool(const bool b) = 0;

  /// Constructs an SMTExprRef from an integer in base 10 and its sort
  virtual SMTExprRef mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) = 0;

  /// Convinience method to create a bitvector from an integer in base 10 and
  /// its bitwidth
  SMTExprRef mkBVFromDec(const int64_t Int, unsigned BitWidth) {
    return mkBVFromDec(Int, mkBVSort(BitWidth));
  }

  /// Constructs an SMTExprRef from an integer in base 2 and its sort
  virtual SMTExprRef mkBVFromBin(const std::string &Int,
                                 const SMTSortRef &Sort) = 0;

  /// Convinience method to create a bitvector from an integer in base 2 and
  /// its bitwidth
  SMTExprRef mkBVFromBin(const std::string &Int, unsigned BitWidth) {
    return mkBVFromBin(Int, mkBVSort(BitWidth));
  }

  /// Convinience method to create a bitvector from an integer in base 2
  SMTExprRef mkBVFromBin(const std::string &Int) {
    return mkBVFromBin(Int, Int.length());
  }

  /// Creates a new symbol, given a name and a sort
  virtual SMTExprRef mkSymbol(const std::string &Name, SMTSortRef Sort) = 0;

  /// Constructs a floating-point from a binary string, in the IEEE-754 format:
  /// 1 bit for the sign + N bits for the exponent + M bits for the significand
  virtual SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth) = 0;

  /// Constructs an SMTExprRef from a float. We assume the floating-point is
  /// using the IEEE-754 format: 1 bit for the sign + 8 bits for the exponent +
  /// 23 bits for the significand and 1 hidden bit in the significand
  SMTExprRef mkFP32(const float Float);

  /// Constructs an SMTExprRef from a double.  We assume the floating-point is
  /// using the IEEE-754 format: 1 bit for the sign + 11 bits for the exponent +
  /// 52 bits for the significand and 1 hidden bit in the significand
  SMTExprRef mkFP64(const double Double);

  /// Returns an appropriate floating-point rounding mode.
  virtual SMTExprRef mkRM(const RM &R) = 0;

  /// Returns a NaN floating-point
  virtual SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) = 0;

  /// Convenience method to create 32 bits long NaN
  SMTExprRef mkNaN32(const bool Sgn) { return mkNaN(Sgn, 8, 23); }

  /// Convenience method to create 64 bits long NaN
  SMTExprRef mkNaN64(const bool Sgn) { return mkNaN(Sgn, 11, 52); }

  /// Returns a Inf floating-point
  virtual SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) = 0;

  /// Convenience method to create 32 bits long Inf
  SMTExprRef mkInf32(const bool Sgn) { return mkInf(Sgn, 8, 23); }

  /// Convenience method to create 64 bits long Inf
  SMTExprRef mkInf64(const bool Sgn) { return mkInf(Sgn, 11, 52); }

  /// Creates an array and initializes all elements to InitValue
  virtual SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                                  const SMTExprRef &InitValue) = 0;

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

  /// Returns an appropriate floating-point sort, encoded as a bitvector.
  virtual SMTSortRef mkBVFPSort(const unsigned ExpWidth,
                                 const unsigned SigWidth) = 0;

  /// Returns an appropriate rounding mode sort, encoded as a bitvector.
  virtual SMTSortRef mkBVRMSort() = 0;
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

/// Convenience method to create a STPSolver object
SMTSolverRef createSTPSolver();

} // namespace camada

#endif
