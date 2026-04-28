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

#ifndef CAMADAIMPL_H_
#define CAMADAIMPL_H_

#include <array>
#include <cassert>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "camada.h"
#include "camadaarena.h"
#include "camadacache.h"
#include "camadaexpr.h"
#include "camadasort.h"

namespace camada {

class SMTSolverImpl : public SMTSolver {
public:
  SMTSolverImpl() = default;
  /// Backend destructors MUST call invalidateGeneratedObjects() before
  /// releasing backend resources (contexts, term managers, etc.). The arena
  /// destructors run during base-class teardown, after derived members are
  /// already gone, so any expression or sort still held by the arena would
  /// destruct against a dead backend. The check below catches a missed call
  /// before it becomes a use-after-free.
  virtual ~SMTSolverImpl() override {
    fatalErrorIf(
        !SortArena.empty() || !ExprArena.empty(),
        "Derived solver destructor must call invalidateGeneratedObjects() "
        "before releasing backend resources");
    // Bump generation so outstanding handles become invalid before the
    // arenas destroy the underlying objects.
    HandleState->bumpGeneration();
  }

protected:
  template <typename SolverExpr, typename... Args>
  SMTExprRef makeExprRef(SMTExprKind Kind, Args &&...ArgsV) {
    auto *Exp =
        ExprArena.create<SolverExpr>(Kind, std::forward<Args>(ArgsV)...);
    assert(Exp->Sort->isWidthValidated());
    return SMTExprRef(Exp, HandleState, HandleState->Generation);
  }

  template <typename SolverSort> SMTSortRef makeSortRef(SolverSort Sort) {
    auto *OwnedSort = SortArena.create<SolverSort>(std::move(Sort));
    assert(OwnedSort->validateSortWidth());
#ifndef NDEBUG
    OwnedSort->markWidthValidated();
#endif
    return SMTSortRef(OwnedSort, HandleState, HandleState->Generation);
  }

  void invalidateGeneratedObjects();
  void clearSortCaches();
  void clearExprCaches();
  void initializeCommonSingletons();

  ObjectArena SortArena;
  ObjectArena ExprArena;
  std::array<SMTExprRef, 2> CachedBoolExprs;
  SMTExprRef CachedBVOne1Expr;
  std::array<SMTExprRef, 5> CachedSmallBVZeroExprs;
  std::array<SMTExprRef, 5> CachedRMBVExprs;
  std::array<std::vector<SMTExprRef>, 3> CachedSmallBVExprs;
  SMTSortRef CachedBoolSort;
  SMTSortRef CachedIntSort;
  SMTSortRef CachedRealSort;
  std::array<SMTSortRef, 2> CachedRMSorts;
  std::unordered_map<SymbolExprCacheKey, SMTExprRef, SymbolExprCacheKeyHash>
      SymbolExprCache;
  std::unordered_map<FPSpecialExprCacheKey, SMTExprRef,
                     FPSpecialExprCacheKeyHash>
      FPSpecialExprCache;
  std::unordered_map<FPConstExprCacheKey, SMTExprRef, FPConstExprCacheKeyHash>
      FPConstExprCache;
  std::unordered_map<unsigned, SMTSortRef> BVSortCache;
  std::array<std::unordered_map<FPSortCacheKey, SMTSortRef, FPSortCacheKeyHash>,
             2>
      FPSortCaches;
  std::unordered_map<ArraySortCacheKey, SMTSortRef, ArraySortCacheKeyHash>
      ArraySortCache;
  std::unordered_map<SmallFunctionSortCacheKey, SMTSortRef,
                     SmallFunctionSortCacheKeyHash>
      SmallFunctionSortCache;
  std::unordered_map<FunctionSortCacheKey, SMTSortRef, FunctionSortCacheKeyHash>
      FunctionSortCache;
  std::unordered_map<SmallTupleSortCacheKey, SMTSortRef,
                     SmallTupleSortCacheKeyHash>
      SmallTupleSortCache;
  std::unordered_map<TupleSortCacheKey, SMTSortRef, TupleSortCacheKeyHash>
      TupleSortCache;
  std::shared_ptr<SMTHandleState> HandleState =
      std::make_shared<SMTHandleState>();

public:
  SMTExprRef getBVZero1Expr() const;
  SMTExprRef getBVOne1Expr() const;
  SMTExprRef getBVZero2Expr() const;
  SMTExprRef getBVZero3Expr() const;
  SMTExprRef getBVZero4Expr() const;
  SMTExprRef getRMExpr(RM R) const;
  SMTExprRef getFPSpecialExpr(unsigned ExpWidth, unsigned SigWidth,
                              FPSpecialValueKind Kind, bool Sign);

  SMTSortRef mkBoolSort() override final;
  SMTSortRef mkIntSort() override final;
  SMTSortRef mkRealSort() override final;
  SMTSortRef mkBVSort(const unsigned BitWidth) override final;
  SMTSortRef mkRMSort(FPEncoding Encoding) override final;
  SMTSortRef mkFPSort(const unsigned ExpWidth, const unsigned SigWidth,
                      FPEncoding Encoding) override final;
  SMTSortRef mkFP32Sort(FPEncoding Encoding) override final;
  SMTSortRef mkFP64Sort(FPEncoding Encoding) override final;
  SMTSortRef mkArraySort(const SMTSortRef &IndexSort,
                         const SMTSortRef &ElemSort) override final;
  SMTSortRef mkFunctionSort(const std::vector<SMTSortRef> &DomainSorts,
                            const SMTSortRef &CodomainSort) override final;
  SMTSortRef
  mkTupleSort(const std::vector<SMTSortRef> &ElementSorts) override final;
  void addConstraint(const SMTExprRef &Exp) override final;
  SMTExprRef mkBVAdd(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSub(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVMul(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSRem(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final;
  SMTExprRef mkBVURem(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSDiv(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final;
  SMTExprRef mkBVUDiv(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final;
  SMTExprRef mkBVShl(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVAshr(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final;
  SMTExprRef mkBVLshr(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final;
  SMTExprRef mkBVNeg(const SMTExprRef &Exp) override final;
  SMTExprRef mkBVNot(const SMTExprRef &Exp) override final;
  SMTExprRef mkBVXor(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVOr(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final;
  SMTExprRef mkBVAnd(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVXnor(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final;
  SMTExprRef mkBVNor(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVNand(const SMTExprRef &LHS,
                      const SMTExprRef &RHS) override final;
  SMTExprRef mkBVUlt(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSlt(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVUgt(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSgt(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVUle(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSle(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVUge(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSge(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkNot(const SMTExprRef &Exp) override final;
  SMTExprRef mkEqual(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkImplies(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final;
  SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override final;
  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override final;
  SMTExprRef mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) override final;

  SMTExprRef mkArithNeg(const SMTExprRef &Exp) override final;
  SMTExprRef mkArithAdd(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final;
  SMTExprRef mkArithSub(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final;
  SMTExprRef mkArithMul(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final;
  SMTExprRef mkArithDiv(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final;
  SMTExprRef mkArithMod(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final;
  SMTExprRef mkArithShl(const SMTExprRef &Exp, unsigned Amount) override final;
  SMTExprRef mkArithShl(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final;
  SMTExprRef mkArithLt(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final;
  SMTExprRef mkArithGt(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final;
  SMTExprRef mkArithLe(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final;
  SMTExprRef mkArithGe(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final;
  SMTExprRef mkInt2Real(const SMTExprRef &Exp) override final;
  SMTExprRef mkReal2Int(const SMTExprRef &Exp) override final;
  SMTExprRef mkIsInt(const SMTExprRef &Exp) override final;
  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) override final;
  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) override final;
  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) override final;
  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) override final;
  SMTExprRef mkBVConcat(const SMTExprRef &LHS,
                        const SMTExprRef &RHS) override final;
  SMTExprRef mkBVRedOr(const SMTExprRef &Exp) override final;
  SMTExprRef mkBVRedAnd(const SMTExprRef &Exp) override final;
  SMTExprRef mkFPAbs(const SMTExprRef &Exp) override final;
  SMTExprRef
  mkFPNeg(const SMTExprRef &Exp,
          FPNegBehavior Behavior = FPNegBehavior::FlipSignBit) override final;
  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override final;
  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override final;

  SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) override final;
  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override final;
  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override final;
  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final;
  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final;
  SMTExprRef mkFPRem(const SMTExprRef &LHS,
                     const SMTExprRef &RHS) override final;
  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final;
  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const SMTExprRef &R) override final;
  SMTExprRef mkFPSqrt(const SMTExprRef &Exp,
                      const SMTExprRef &R) override final;
  SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                     const SMTExprRef &Z, const SMTExprRef &R) override final;
  SMTExprRef mkFPLt(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final;
  SMTExprRef mkFPGt(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final;
  SMTExprRef mkFPLe(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final;
  SMTExprRef mkFPGe(const SMTExprRef &LHS,
                    const SMTExprRef &RHS) override final;
  SMTExprRef mkFPEqual(const SMTExprRef &LHS,
                       const SMTExprRef &RHS) override final;
  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                      const SMTExprRef &R) override final;
  SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const SMTExprRef &R) override final;
  SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const SMTExprRef &R) override final;
  SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) override final;
  SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) override final;
  SMTExprRef mkFPtoIntegral(const SMTExprRef &From,
                            const SMTExprRef &R) override final;
  SMTExprRef mkArraySelect(const SMTExprRef &Array,
                           const SMTExprRef &Index) override final;
  SMTExprRef mkArrayStore(const SMTExprRef &Array, const SMTExprRef &Index,
                          const SMTExprRef &Element) override final;
  SMTExprRef mkTuple(const std::vector<SMTExprRef> &Elements) override final;
  SMTExprRef mkTupleSelect(const SMTExprRef &Tuple,
                           unsigned Index) override final;
  SMTExprRef mkApply(const SMTExprRef &Function,
                     const std::vector<SMTExprRef> &Args) override final;
  SMTExprRef mkForall(const std::vector<SMTExprRef> &Vars,
                      const SMTExprRef &Body) override final;
  SMTExprRef mkExists(const std::vector<SMTExprRef> &Vars,
                      const SMTExprRef &Body) override final;
  SMTResult<bool> getBool(const SMTExprRef &Exp) override final;
  SMTResult<int64_t> getBV(const SMTExprRef &Exp) override final;
  SMTResult<std::string> getBVInBin(const SMTExprRef &Exp) override final;
  SMTResult<std::string> getInt(const SMTExprRef &Exp) override final;
  SMTResult<std::pair<std::string, std::string>>
  getRational(const SMTExprRef &Exp) override final;
  SMTResult<std::string> getRealNumerator(const SMTExprRef &Exp) override final;
  SMTResult<std::string>
  getRealDenominator(const SMTExprRef &Exp) override final;
  SMTResult<std::string> getFPInBin(const SMTExprRef &Exp) override final;
  SMTResult<float> getFP32(const SMTExprRef &Exp) override final;
  SMTResult<double> getFP64(const SMTExprRef &Exp) override final;
  SMTExprRef getArrayElement(const SMTExprRef &Array,
                             const SMTExprRef &Index) override final;
  SMTExprRef mkBool(const bool b) override final;
  SMTExprRef mkInt(int64_t v) override final;
  SMTExprRef mkInt(const std::string &v) override final;
  SMTExprRef mkReal(const std::string &v) override final;
  SMTExprRef mkReal(int64_t v) override final;
  SMTExprRef mkReal(int64_t num, int64_t den) override final;
  SMTExprRef mkBVFromDec(const int64_t Int,
                         const SMTSortRef &Sort) override final;
  SMTExprRef mkBVFromDec(const int64_t Int, unsigned BitWidth) override final;
  SMTExprRef mkBVFromBin(const std::string &Int,
                         const SMTSortRef &Sort) override final;
  SMTExprRef mkBVFromBin(const std::string &Int,
                         unsigned BitWidth) override final;
  SMTExprRef mkBVFromBin(const std::string &Int) override final;
  SMTExprRef mkSymbol(const std::string &Name,
                      const SMTSortRef &Sort) override final;
  SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth,
                         FPEncoding Encoding) override;
  SMTExprRef mkFP32(const float Float, FPEncoding Encoding) override final;
  SMTExprRef mkFP64(const double Double, FPEncoding Encoding) override final;
  SMTExprRef mkRM(const RM &R, FPEncoding Encoding) override final;
  SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth, FPEncoding Encoding) override final;
  SMTExprRef mkNaN32(const bool Sgn, FPEncoding Encoding) override final;
  SMTExprRef mkNaN64(const bool Sgn, FPEncoding Encoding) override final;
  SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth, FPEncoding Encoding) override final;
  SMTExprRef mkInf32(const bool Sgn, FPEncoding Encoding) override final;
  SMTExprRef mkInf64(const bool Sgn, FPEncoding Encoding) override final;
  SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                          const SMTExprRef &InitValue) override final;
  SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp,
                          const SMTSortRef &To) override final;
  SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) override final;
  checkResult check() override final;
  void reset() override final;
  void push(unsigned nscopes = 1) override final;
  void pop(unsigned nscopes = 1) override final;
  void dump() override final;
  void dump(std::string &Out) override final;
  void dumpModel() override final;
  void dumpModel(std::string &Out) override final;

protected:
  virtual SMTExprRef newExprRefImpl(const SMTExpr &Exp) = 0;

  // Rewrap an existing backend payload with a different Camada-facing
  // sort/kind. This is still needed for lowered/common-layer operations where
  // the semantic API node differs from the literal backend term shape, even
  // though backend-native operations should construct expressions with the
  // final kind directly.
  virtual SMTExprRef rewrapExprImpl(const SMTExpr &Exp, const SMTSortRef &Sort,
                                    SMTExprKind Kind) = 0;

  virtual SMTSortRef mkBoolSortImpl() = 0;

  virtual SMTSortRef mkIntSortImpl();

  virtual SMTSortRef mkRealSortImpl();

  virtual SMTSortRef mkBVSortImpl(const unsigned BitWidth) = 0;

  virtual SMTSortRef mkRMSortImpl();

  virtual SMTSortRef mkFPSortImpl(const unsigned ExpWidth,
                                  const unsigned SigWidth);

  virtual SMTSortRef mkArraySortImpl(const SMTSortRef &IndexSort,
                                     const SMTSortRef &ElemSort) = 0;

  virtual SMTSortRef mkFunctionSortImpl(const std::vector<SMTSortRef> &,
                                        const SMTSortRef &);

  virtual SMTSortRef mkTupleSortImpl(const std::vector<SMTSortRef> &);

  virtual void addConstraintImpl(const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVAddImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSubImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVMulImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSRemImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVURemImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSDivImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVUDivImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVShlImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVAshrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVLshrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVNegImpl(const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVNotImpl(const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVXorImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVOrImpl(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVAndImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVXnorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkBVNorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkBVNandImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkBVUltImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSltImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVUgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkBVSgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkBVUleImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVSleImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVUgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkBVSgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkNotImpl(const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkEqualImpl(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkImpliesImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkAndImpl(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkArithNegImpl(const SMTExprRef &);

  virtual SMTExprRef mkArithAddImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithSubImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithMulImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithDivImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithModImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithShlImpl(const SMTExprRef &Exp, unsigned Amount);

  virtual SMTExprRef mkArithShlImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithLtImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithGtImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithLeImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkArithGeImpl(const SMTExprRef &, const SMTExprRef &);

  virtual SMTExprRef mkInt2RealImpl(const SMTExprRef &);

  virtual SMTExprRef mkReal2IntImpl(const SMTExprRef &);

  virtual SMTExprRef mkIsIntImpl(const SMTExprRef &);

  virtual SMTExprRef mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                               const SMTExprRef &F) = 0;

  virtual SMTExprRef mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVExtractImpl(unsigned High, unsigned Low,
                                     const SMTExprRef &Exp) = 0;

  virtual SMTExprRef mkBVConcatImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) = 0;

  virtual SMTExprRef mkBVRedOrImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkBVRedAndImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPAbsImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPNegImpl(const SMTExprRef &Exp, FPNegBehavior Behavior);

  virtual SMTExprRef mkFPIsInfiniteImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsNaNImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsDenormalImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsNormalImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPIsZeroImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R);

  virtual SMTExprRef mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R);

  virtual SMTExprRef mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R);

  virtual SMTExprRef mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R);

  virtual SMTExprRef mkFPSqrtImpl(const SMTExprRef &Exp, const SMTExprRef &R);

  virtual SMTExprRef mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                 const SMTExprRef &Z, const SMTExprRef &R);

  virtual SMTExprRef mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPGtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPGeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS);

  virtual SMTExprRef mkFPEqualImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

  virtual SMTExprRef mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                  const SMTExprRef &R);

  virtual SMTExprRef mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R);

  virtual SMTExprRef mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R);

  virtual SMTExprRef mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth);

  virtual SMTExprRef mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth);

  virtual SMTExprRef mkFPtoIntegralImpl(const SMTExprRef &From,
                                        const SMTExprRef &R);

  virtual SMTExprRef mkArraySelectImpl(const SMTExprRef &Array,
                                       const SMTExprRef &Index) = 0;

  virtual SMTExprRef mkArrayStoreImpl(const SMTExprRef &Array,
                                      const SMTExprRef &Index,
                                      const SMTExprRef &Element) = 0;

  virtual SMTExprRef mkTupleImpl(const std::vector<SMTExprRef> &);

  virtual SMTExprRef mkTupleSelectImpl(const SMTExprRef &, unsigned);

  virtual SMTExprRef mkApplyImpl(const SMTExprRef &,
                                 const std::vector<SMTExprRef> &);

  virtual SMTExprRef mkForallImpl(const std::vector<SMTExprRef> &,
                                  const SMTExprRef &);

  virtual SMTExprRef mkExistsImpl(const std::vector<SMTExprRef> &,
                                  const SMTExprRef &);

  virtual SMTResult<bool> getBoolImpl(const SMTExprRef &Exp) = 0;

  SMTResult<int64_t> getBVImpl(const SMTExprRef &Exp);

  virtual SMTResult<std::string> getBVInBinImpl(const SMTExprRef &Exp) = 0;

  virtual SMTResult<std::string> getIntImpl(const SMTExprRef &);

  virtual SMTResult<std::pair<std::string, std::string>>
  getRationalImpl(const SMTExprRef &);

  virtual SMTResult<std::string> getFPInBinImpl(const SMTExprRef &Exp);

  SMTResult<float> getFP32Impl(const SMTExprRef &Exp);

  SMTResult<double> getFP64Impl(const SMTExprRef &Exp);

  virtual SMTExprRef getArrayElementImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index) = 0;

  virtual SMTExprRef mkBoolImpl(const bool b) = 0;

  virtual SMTExprRef mkIntImpl(int64_t);

  virtual SMTExprRef mkIntImpl(const std::string &);

  virtual SMTExprRef mkRealImpl(const std::string &);

  virtual SMTExprRef mkRealImpl(int64_t);

  virtual SMTExprRef mkRealImpl(int64_t, int64_t);

  virtual SMTExprRef mkBVFromDecImpl(const int64_t Int,
                                     const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkBVFromBinImpl(const std::string &Int,
                                     const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkSymbolImpl(const std::string &Name,
                                  const SMTSortRef &Sort) = 0;

  virtual SMTExprRef mkFPFromBinImpl(const std::string &FP, unsigned EWidth);

  SMTExprRef mkFP32Impl(const float Float, FPEncoding Encoding);

  SMTExprRef mkFP64Impl(const double Double, FPEncoding Encoding);

  virtual SMTExprRef mkRMImpl(const RM &R);

  virtual SMTExprRef mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth);

  virtual SMTExprRef mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth);

  virtual SMTExprRef mkArrayConstImpl(const SMTSortRef &IndexSort,
                                      const SMTExprRef &InitValue) = 0;

  virtual SMTExprRef mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                      const SMTSortRef &To);

  virtual SMTExprRef mkIEEEFPToBVImpl(const SMTExprRef &Exp);

  virtual SMTExprRef mkToBV(const SMTExprRef &Exp, bool isSigned,
                            unsigned int width);

  virtual SMTExprRef round(const SMTExprRef &R, const SMTExprRef &Sgn,
                           SMTExprRef &Sig, SMTExprRef &Exp, unsigned EWidth,
                           unsigned SWidth);

  virtual checkResult checkImpl() = 0;

  virtual void resetImpl() = 0;

  virtual void pushImpl(unsigned nscopes) = 0;

  virtual void popImpl(unsigned nscopes) = 0;

  virtual void dumpImpl();
  virtual void dumpImpl(std::string &Out);

  virtual void dumpModelImpl();
  virtual void dumpModelImpl(std::string &Out);

  virtual SMTSortRef mkBVFPSortImpl(const unsigned ExpWidth,
                                    const unsigned SigWidth) = 0;

  virtual SMTSortRef mkBVRMSortImpl() = 0;
};

} // namespace camada

#endif
