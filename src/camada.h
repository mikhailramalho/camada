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

#include <array>
#include <cstdint>
#include <deque>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "camadacache.h"
#include "camadaexpr.h"
#include "camadafeatures.h"

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
/// through the mk* methods.
class SMTSolver {
public:
  SMTSolver() = default;
  virtual ~SMTSolver() = default;

  /// Wrapper to create new SMTExpr
  virtual SMTExprRef newExprRef(const SMTExpr &Exp) const = 0;

  /// Returns a boolean sort.
  virtual SMTSortRef mkBoolSort() = 0;

  /// Returns an integer sort.
  virtual SMTSortRef mkIntSort() = 0;

  /// Returns a real sort.
  virtual SMTSortRef mkRealSort() = 0;

  /// Returns an appropriate bitvector sort for the given bitwidth.
  virtual SMTSortRef mkBVSort(const unsigned BitWidth) = 0;

  /// Returns an appropriate rounding mode sort.
  virtual SMTSortRef mkRMSort() = 0;

  /// Returns an appropriate floating-point sort for the given bitwidth.
  virtual SMTSortRef mkFPSort(const unsigned ExpWidth,
                              const unsigned SigWidth) = 0;

  /// Convenience method to create a 32 bits long a floating-point sort.
  virtual SMTSortRef mkFP32Sort() = 0;

  /// Convenience method to create a 64 bits long a floating-point sort.
  virtual SMTSortRef mkFP64Sort() = 0;

  /// Returns an appropriate array sort.
  virtual SMTSortRef mkArraySort(const SMTSortRef &IndexSort,
                                 const SMTSortRef &ElemSort) = 0;

  /// Returns an appropriate function sort.
  virtual SMTSortRef mkFunctionSort(const std::vector<SMTSortRef> &DomainSorts,
                                    const SMTSortRef &CodomainSort) = 0;

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

  /// Creates a bitvector xnor operation
  virtual SMTExprRef mkBVXnor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector nor operation
  virtual SMTExprRef mkBVNor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector nand operation
  virtual SMTExprRef mkBVNand(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned less-than operation
  virtual SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed less-than operation
  virtual SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned greater-than operation
  virtual SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed greater-than operation
  virtual SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned less-equal-than operation
  virtual SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed less-equal-than operation
  virtual SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned greater-equal-than operation
  virtual SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed greater-equal-than operation
  virtual SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean not operation
  virtual SMTExprRef mkNot(const SMTExprRef &Exp) = 0;

  /// Creates a boolean equality operation
  virtual SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean implication operation
  virtual SMTExprRef mkImplies(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates a boolean and operation
  virtual SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean or operation
  virtual SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean xor operation
  virtual SMTExprRef mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic unary minus operation.
  virtual SMTExprRef mkArithNeg(const SMTExprRef &Exp) = 0;

  /// Creates an arithmetic addition operation.
  virtual SMTExprRef mkArithAdd(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic subtraction operation.
  virtual SMTExprRef mkArithSub(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic multiplication operation.
  virtual SMTExprRef mkArithMul(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic division operation.
  virtual SMTExprRef mkArithDiv(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic less-than operation.
  virtual SMTExprRef mkArithLt(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic greater-than operation.
  virtual SMTExprRef mkArithGt(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic less-than-or-equal operation.
  virtual SMTExprRef mkArithLe(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic greater-than-or-equal operation.
  virtual SMTExprRef mkArithGe(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

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

  /// Creates a bitvector reduction-or operation
  virtual SMTExprRef mkBVRedOr(const SMTExprRef &Exp) = 0;

  /// Creates a bitvector reduction-and operation
  virtual SMTExprRef mkBVRedAnd(const SMTExprRef &Exp) = 0;

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
                             const SMTExprRef &R) = 0;

  /// Creates a floating-point division operation
  virtual SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const SMTExprRef &R) = 0;

  /// Creates a floating-point remainder operation
  virtual SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point addition operation
  virtual SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const SMTExprRef &R) = 0;

  /// Creates a floating-point subtraction operation
  virtual SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const SMTExprRef &R) = 0;

  /// Creates a floating-point square root operation
  virtual SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const SMTExprRef &R) = 0;

  /// Creates a floating-point fused-multiply add operation: round((x * y) + z)
  virtual SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z, const SMTExprRef &R) = 0;

  /// Creates a floating-point less-than operation
  virtual SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point greater-than operation
  virtual SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point less-than-or-equal operation
  virtual SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point greater-than-or-equal operation
  virtual SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point equality operation
  virtual SMTExprRef mkFPEqual(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates a floating-point conversion from floatint-point to floating-point
  /// operation
  virtual SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const SMTExprRef &R) = 0;

  /// Creates a floating-point conversion from signed bitvector to
  /// floatint-point operation
  virtual SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const SMTExprRef &R) = 0;

  /// Creates a floating-point conversion from unsigned bitvector to
  /// floatint-point operation
  virtual SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const SMTExprRef &R) = 0;

  /// Creates a floating-point conversion from floatint-point to signed
  /// bitvector operation
  virtual SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floatint-point to unsigned
  /// bitvector operation
  virtual SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floatint-point to the closest
  /// integer, considering the rounding mode.
  virtual SMTExprRef mkFPtoIntegral(const SMTExprRef &From,
                                    const SMTExprRef &R) = 0;

  /// Creates an array select operation. It returns the element in position
  /// Index of Array.
  virtual SMTExprRef mkArraySelect(const SMTExprRef &Array,
                                   const SMTExprRef &Index) = 0;

  /// Creates an array store operation. It stores Element in position Index of
  /// Array.
  virtual SMTExprRef mkArrayStore(const SMTExprRef &Array,
                                  const SMTExprRef &Index,
                                  const SMTExprRef &Element) = 0;

  /// Applies a function symbol to arguments.
  virtual SMTExprRef mkApply(const SMTExprRef &Function,
                             const std::vector<SMTExprRef> &Args) = 0;

  /// Creates a universally quantified formula over Vars with Body.
  virtual SMTExprRef mkForall(const std::vector<SMTExprRef> &Vars,
                              const SMTExprRef &Body) = 0;

  /// Creates an existentially quantified formula over Vars with Body.
  virtual SMTExprRef mkExists(const std::vector<SMTExprRef> &Vars,
                              const SMTExprRef &Body) = 0;

  /// If a model is available, returns the value of a given boolean symbol
  virtual bool getBool(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given bitvector
  /// symbol as a 64-bits int
  virtual int64_t getBV(const SMTExprRef &Exp) = 0;

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
  virtual float getFP32(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given floating-point
  /// symbol as double. We assume the floating-point is using the IEEE-754
  /// format: 1 bit for the sign + 11 bits for the exponent + 52 bits for the
  /// significand and 1 hidden bit in the significand
  virtual double getFP64(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the Expr in position Index of Array
  virtual SMTExprRef getArrayElement(const SMTExprRef &Array,
                                     const SMTExprRef &Index) = 0;

  /// Constructs an SMTExprRef from a boolean.
  virtual SMTExprRef mkBool(const bool b) = 0;

  /// Constructs an SMTExprRef from an integer.
  virtual SMTExprRef mkInt(int64_t v) = 0;

  /// Constructs an SMTExprRef from a real written as SMT-LIB numeral text.
  virtual SMTExprRef mkReal(const std::string &v) = 0;

  /// Constructs an SMTExprRef from an integral real.
  virtual SMTExprRef mkReal(int64_t v) = 0;

  /// Constructs an SMTExprRef from a rational real numerator/denominator.
  virtual SMTExprRef mkReal(int64_t num, int64_t den) = 0;

  /// Constructs an SMTExprRef from an integer in base 10 and its sort
  virtual SMTExprRef mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) = 0;

  /// Convinience method to create a bitvector from an integer in base 10 and
  /// its bitwidth
  virtual SMTExprRef mkBVFromDec(const int64_t Int, unsigned BitWidth) = 0;

  /// Constructs an SMTExprRef from an integer in base 2 and its sort
  virtual SMTExprRef mkBVFromBin(const std::string &Int,
                                 const SMTSortRef &Sort) = 0;

  /// Convinience method to create a bitvector from an integer in base 2 and
  /// its bitwidth
  virtual SMTExprRef mkBVFromBin(const std::string &Int, unsigned BitWidth) = 0;

  /// Convinience method to create a bitvector from an integer in base 2
  virtual SMTExprRef mkBVFromBin(const std::string &Int) = 0;

  /// Creates a new symbol, given a name and a sort
  virtual SMTExprRef mkSymbol(const std::string &Name,
                              const SMTSortRef &Sort) = 0;

  /// Constructs a floating-point from a binary string, in the IEEE-754 format:
  /// 1 bit for the sign + N bits for the exponent + M bits for the significand
  virtual SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth) = 0;

  /// Constructs an SMTExprRef from a float. We assume the floating-point is
  /// using the IEEE-754 format: 1 bit for the sign + 8 bits for the exponent +
  /// 23 bits for the significand and 1 hidden bit in the significand
  virtual SMTExprRef mkFP32(const float Float) = 0;

  /// Constructs an SMTExprRef from a double.  We assume the floating-point is
  /// using the IEEE-754 format: 1 bit for the sign + 11 bits for the exponent +
  /// 52 bits for the significand and 1 hidden bit in the significand
  virtual SMTExprRef mkFP64(const double Double) = 0;

  /// Returns an appropriate floating-point rounding mode.
  virtual SMTExprRef mkRM(const RM &R) = 0;

  /// Returns a NaN floating-point
  virtual SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) = 0;

  /// Convenience method to create 32 bits long NaN
  virtual SMTExprRef mkNaN32(const bool Sgn) = 0;

  /// Convenience method to create 64 bits long NaN
  virtual SMTExprRef mkNaN64(const bool Sgn) = 0;

  /// Returns a Inf floating-point
  virtual SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) = 0;

  /// Convenience method to create 32 bits long Inf
  virtual SMTExprRef mkInf32(const bool Sgn) = 0;

  /// Convenience method to create 64 bits long Inf
  virtual SMTExprRef mkInf64(const bool Sgn) = 0;

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

  /// Create a new assertion scope.
  virtual void push(unsigned nscopes = 1) = 0;

  /// Pop one or more assertion scopes.
  virtual void pop(unsigned nscopes = 1) = 0;

  /// Returns the solver name and version
  virtual std::string getSolverNameAndVersion() const = 0;

  /// Dump formula
  virtual void dump() = 0;

  /// Dump Model
  virtual void dumpModel() = 0;

  /// Flag to enable encoding floating-points using bitvectors even if the
  /// solver supports floating-points. For solvers that don't support
  /// floating-point arithmetic, bitvectors will be used even if this flag is
  /// false
  bool useCamadaFP = false;

protected:
  /// Wrapper to create new SMTSort
  template <typename SolverSort>
  SMTSortRef newSortRef(const SolverSort &Sort) const {
    auto OwnedSort = std::make_unique<SolverSort>(Sort);
#ifndef NDEBUG
    assert(OwnedSort->validateSortWidth());
    OwnedSort->markWidthValidated();
#endif
    const SMTSort *SortPtr = OwnedSort.get();
    SortArena.emplace_back(std::move(OwnedSort));
    return SMTSortRef(SortPtr, HandleState, HandleState->Generation);
  }

  template <typename SolverExpr>
  SMTExprRef storeExprRef(const SolverExpr &Exp) const {
    auto OwnedExpr = std::make_unique<SolverExpr>(Exp);
    const SMTExpr *ExprPtr = OwnedExpr.get();
    ExprArena.emplace_back(std::move(OwnedExpr));
    return SMTExprRef(ExprPtr, HandleState, HandleState->Generation);
  }

  template <typename SolverExpr>
  SMTExprRef storeOwnedExprRef(std::unique_ptr<SolverExpr> Exp) const {
    const SMTExpr *ExprPtr = Exp.get();
    ExprArena.emplace_back(std::move(Exp));
    return SMTExprRef(ExprPtr, HandleState, HandleState->Generation);
  }

  void invalidateGeneratedObjects();

  void clearSortCaches();

  void clearExprCaches();

  void initializeCommonSingletons();

  mutable std::deque<std::unique_ptr<SMTSort>> SortArena;
  mutable std::deque<std::unique_ptr<SMTExpr>> ExprArena;
  mutable std::array<SMTExprRef, 2> CachedBoolExprs;
  mutable SMTExprRef CachedBVOne1Expr;
  mutable std::array<SMTExprRef, 5> CachedSmallBVZeroExprs;
  mutable std::array<SMTExprRef, 5> CachedRMBVExprs;
  mutable std::vector<SMTExprRef> CachedBVNegOneExprs;
  mutable std::vector<SMTExprRef> CachedBVZeroExprs;
  mutable std::vector<SMTExprRef> CachedBVOneExprs;
  mutable SMTSortRef CachedBoolSort;
  mutable SMTSortRef CachedIntSort;
  mutable SMTSortRef CachedRealSort;
  mutable SMTSortRef CachedNativeRMSort;
  mutable SMTSortRef CachedEncodedRMSort;
  mutable std::unordered_map<SymbolExprCacheKey, SMTExprRef,
                             SymbolExprCacheKeyHash>
      SymbolExprCache;
  mutable std::unordered_map<FPSpecialExprCacheKey, SMTExprRef,
                             FPSpecialExprCacheKeyHash>
      FPSpecialExprCache;
  mutable std::unordered_map<unsigned, SMTSortRef> BVSortCache;
  mutable std::unordered_map<FPSortCacheKey, SMTSortRef, FPSortCacheKeyHash>
      NativeFPSortCache;
  mutable std::unordered_map<FPSortCacheKey, SMTSortRef, FPSortCacheKeyHash>
      EncodedFPSortCache;
  mutable std::unordered_map<ArraySortCacheKey, SMTSortRef,
                             ArraySortCacheKeyHash>
      ArraySortCache;
  mutable std::unordered_map<FunctionSortCacheKey, SMTSortRef,
                             FunctionSortCacheKeyHash>
      FunctionSortCache;
  std::shared_ptr<SMTHandleState> HandleState =
      std::make_shared<SMTHandleState>();

  /// Returns an appropriate floating-point sort, encoded as a bitvector.
  virtual SMTSortRef mkBVFPSort(const unsigned ExpWidth,
                                const unsigned SigWidth) = 0;

  /// Returns an appropriate rounding mode sort, encoded as a bitvector.
  virtual SMTSortRef mkBVRMSort() = 0;
};

/// Unique pointer for SMTSolvers.
using SMTSolverRef = std::unique_ptr<SMTSolver>;

/// Convenience method to create a Z3Solver object
SMTSolverRef createZ3Solver();

/// Convenience method to create a MathSATSolver object
SMTSolverRef createMathSATSolver();

/// Convenience method to create a CVC5Solver object
SMTSolverRef createCVC5Solver();

/// Convenience method to create a BitwuzlaSolver object
SMTSolverRef createBitwuzlaSolver();

/// Convenience method to create a YicesSolver object
SMTSolverRef createYicesSolver();

/// Convenience method to create a STPSolver object
SMTSolverRef createSTPSolver();

} // namespace camada

#endif
