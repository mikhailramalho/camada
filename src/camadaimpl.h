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
#include <set>
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

public:
  /// Allocates an SMTExpr-derived object in the per-solver arena. Used by
  /// every backend's *Impl methods and by camadatuple.cpp to construct
  /// CamadaTupleExpr nodes. The first ctor argument of `SolverExpr` (and
  /// of CamadaTupleExpr) is `SMTExprKind` so it is forwarded explicitly
  /// rather than tucked inside ArgsV.
  template <typename SolverExpr, typename... Args>
  SMTExprRef makeExprRef(SMTExprKind Kind, Args &&...ArgsV) {
    auto *Exp =
        ExprArena.create<SolverExpr>(Kind, std::forward<Args>(ArgsV)...);
    assert(Exp->Sort->isWidthValidated());
    return SMTExprRef(Exp, HandleState, HandleState->Generation);
  }

  /// Allocates an SMTSort-derived object in the per-solver arena. Same
  /// shape as makeExprRef but takes the sort by value (each backend's
  /// SolverSort is cheap to construct in place at the call site).
  template <typename SolverSort> SMTSortRef makeSortRef(SolverSort Sort) {
    auto *OwnedSort = SortArena.create<SolverSort>(std::move(Sort));
    assert(OwnedSort->validateSortWidth());
#ifndef NDEBUG
    OwnedSort->markWidthValidated();
#endif
    return SMTSortRef(OwnedSort, HandleState, HandleState->Generation);
  }

  /// mkSymbol variant that bypasses the user-name validation. Used by
  /// internal lowerings (Camada tuple field decomposition, STP array
  /// extensionality, FP-to-BV shadowing) that mint symbols with the
  /// reserved __CAMADA_ prefix.
  SMTExprRef mkSymbolUnchecked(const std::string &Name, const SMTSortRef &Sort);

protected:
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

  // --- Lazy constant-array lowering ---
  // A lazy constant array is an ordinary backend array symbol whose
  // "every element equals Init" semantics live here, not in the backend:
  // the default axiom is instantiated as a ground constraint
  // `select(Root, i) = Init` at every index term the formula observes.
  // Derivations through store/ite are tracked so selects on derived arrays
  // reach their roots, and so model queries can resolve untouched indexes
  // to the default (the solver's model is unconstrained there).
  struct LazyConstArrayRoot {
    SMTExprRef Root;
    SMTExprRef Init;
  };
  struct LazyArrayStoreStep {
    const SMTExpr *Parent;
    SMTExprRef Index;
    SMTExprRef Value;
  };
  struct LazyArrayIteStep {
    SMTExprRef Cond;
    const SMTExpr *TrueArr;
    const SMTExpr *FalseArr;
  };
  std::unordered_map<const SMTExpr *, LazyConstArrayRoot> LazyConstArrayRoots;
  std::unordered_map<const SMTSort *, std::vector<const SMTExpr *>>
      LazyRootsByIndexSort;
  std::unordered_map<const SMTExpr *, std::vector<const SMTExpr *>>
      LazyConstArrayReach;
  std::unordered_map<const SMTExpr *, LazyArrayStoreStep> LazyArrayStores;
  std::unordered_map<const SMTExpr *, LazyArrayIteStep> LazyArrayItes;
  // Memo of instantiated (root, index term) pairs. Default axioms and
  // extensionality lemmas are scope-independent facts, so instead of
  // forgetting them when a push scope pops, pop() re-asserts the journaled
  // constraints at the outer level (see LazyConstraintLevels).
  std::set<std::pair<const SMTExpr *, const SMTExpr *>> LazyTouched;
  std::vector<std::vector<SMTExprRef>> LazyConstraintLevels{1};
  uint64_t LazyConstArrayCounter = 0;
  // Every distinct index term ever selected with, grouped by index sort.
  // Lazy default axioms and encoded-equality congruence are instantiated
  // at EVERY observed index of the matching sort — not just indexes seen
  // on the syntactic array operands — because reads can reach an array
  // through store/ite-derived terms and through terms built before an
  // equality existed. Sort-global instantiation is a superset of any
  // equivalence-class walk, so it is unconditionally sound, and complete
  // for quantifier-free formulas (only finitely many index terms exist).
  std::unordered_map<const SMTSort *, std::vector<SMTExprRef>>
      ObservedIndexesBySort;
  std::set<std::pair<const SMTSort *, const SMTExpr *>> ObservedIndexSeen;
  void observeArrayIndex(const SMTExprRef &Index);

  // Build select(Array, Index) WITHOUT registering Index as a sort-global
  // observed index. Used only for encoded-equality witnesses: a fresh
  // witness is read at exactly one syntactic position (its equality's
  // lemma), so the sort-global fan-out observeArrayIndex performs is never
  // needed for it — and for nested lazy const arrays that fan-out is
  // exactly what fails to terminate, since the witness's own observation
  // re-fires the roots it was minted under, each time at a new witness.
  SMTExprRef mkArraySelectUnobserved(const SMTExprRef &Array,
                                     const SMTExprRef &Index);
  // True while a model query (getArrayElement) is evaluating: selects
  // built for evaluation must not instantiate default axioms or count as
  // formula observations — asserting after check() invalidates the
  // backend's model.
  bool InLazyModelQuery = false;

  /// True when the backend can express `((as const ...) v)` natively.
  /// Backends without it get constant arrays through mkLazyConstArray().
  virtual bool nativeConstArraySupport() const { return true; }

  /// True when the backend decides array equality natively (extensional
  /// array theory). STP cannot: its only array predicate is select, so
  /// the common layer lowers array equality through mkEncodedArrayEqual()
  /// instead of mkEqualImpl().
  virtual bool nativeArrayExtensionality() const { return true; }

  // --- Encoded array equality (backends without native extensionality) ---
  // Each lowered equality is a fresh boolean EqVar tied to its arrays by:
  //   * the negative direction: EqVar \/ select(L,W) != select(R,W) for a
  //     fresh witness index W (a difference must be exhibitable), and
  //   * the positive direction: EqVar => select(L,i) = select(R,i) at
  //     every index i either array is observed at — replayed for past
  //     selects and hooked into mkArraySelect for future ones.
  // Sound and complete for quantifier-free formulas: only finitely many
  // index terms are ever observed.
  struct ArrayEqualLink {
    SMTExprRef EqVar;
    SMTExprRef LHS;
    SMTExprRef RHS;
  };
  std::vector<ArrayEqualLink> ArrayEqualLinks;
  std::unordered_map<const SMTSort *, std::vector<std::size_t>>
      ArrayEqualLinksByIndexSort;
  std::set<std::pair<std::size_t, const SMTExpr *>> ArrayEqualCongruenceDone;
  uint64_t ArrayEqualCounter = 0;

  SMTExprRef mkEncodedArrayEqual(const SMTExprRef &LHS, const SMTExprRef &RHS);
  void assertArrayEqualCongruence(std::size_t LinkId, const SMTExprRef &Index);

  // Enforce, at an encoded equality's fresh (non-observed) witness, exactly
  // the lazy default axioms its two operands need so a claimed difference at
  // the witness is a real one and not fabricated where a value is
  // unconstrained. Scoped to LHS/RHS only — never the sort-global root set —
  // and uses the unobserved select path so the witness is never globally
  // observed. Array-element operands are handled by the structural recursion
  // in mkEncodedArrayEqual (the inner select equality re-enters it).
  void enforceWitnessFacts(const SMTExprRef &LHS, const SMTExprRef &RHS,
                           const SMTExprRef &Witness);

  /// Lower a constant array as a fresh backend array symbol whose
  /// "every element equals InitValue" semantics are enforced lazily: the
  /// default axiom is instantiated at each index term the formula observes
  /// (see the bookkeeping above). Reached through
  /// mkArrayConst(..., ConstArrayLowering::Lazy), which is how lowerings
  /// with no backend representation for the initializer (Camada tuple
  /// decomposition) should request it. The emitted constraints go through
  /// the public mkEqual/mkArraySelect, so such initializers compose with
  /// the other Camada lowerings.
  SMTExprRef mkLazyConstArray(const SMTSortRef &IndexSort,
                              const SMTExprRef &InitValue);

  std::vector<const SMTExpr *> lazyArrayRootsOf(const SMTExprRef &Exp) const;
  bool reachesLazyArray(const SMTExprRef &Exp) const;
  void instantiateLazyDefaultAt(const SMTExpr *RootKey,
                                const SMTExprRef &Index);
  // As instantiateLazyDefaultAt, but the default's select is built on the
  // unobserved path: used for encoded-equality witnesses (see
  // enforceWitnessFacts) so the witness index is not globally observed.
  void instantiateLazyDefaultAtUnobserved(const SMTExpr *RootKey,
                                          const SMTExprRef &Index);
  SMTExprRef resolveLazyArrayElement(const SMTExprRef &Array,
                                     const SMTExprRef &Index);

  /// Wall-clock limit applied to each check, in milliseconds; 0 means no
  /// limit. Stored here so reset() can re-apply it after resetImpl()
  /// recreates backend state, and so backends that enforce the limit
  /// through per-check deadlines (termination callbacks, SIGALRM) can
  /// read the current value.
  uint64_t TimeoutMs = 0;

  // --- Assumption-based solving ---
  // The assumptions of the most recent checkSatAssuming() call, kept so
  // backends can map the solver's native unsat core back to the caller's
  // SMTExprRefs. UnsatAssumptionsValid gates getUnsatAssumptions(): it is
  // set only when that call returned UNSAT and cleared by anything that
  // invalidates the solver's core — a plain check(), addConstraint(),
  // push(), pop(), or reset().
  std::vector<SMTExprRef> LastAssumptions;
  bool UnsatAssumptionsValid = false;
  void invalidateUnsatAssumptions();

  /// Model bits of a bool/BV-sorted expression after a SAT check, used to
  /// compare index terms by model value. Empty string when the sort is
  /// unsupported or the model query fails.
  std::string lazyIndexModelBits(const SMTExprRef &Exp);

  /// Sparse model for an expression that reaches a lazily lowered constant
  /// array, built from the tracked derivation chain instead of the backend
  /// model (the backend's model is unconstrained at indexes whose defaults
  /// were never instantiated).
  SMTResult<ArrayModel> lazyArrayModel(const SMTExprRef &Array);

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
  SMTExprRef mkBVSAddOverflow(const SMTExprRef &LHS,
                              const SMTExprRef &RHS) override final;
  SMTExprRef mkBVUAddOverflow(const SMTExprRef &LHS,
                              const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSSubOverflow(const SMTExprRef &LHS,
                              const SMTExprRef &RHS) override final;
  SMTExprRef mkBVUSubOverflow(const SMTExprRef &LHS,
                              const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSMulOverflow(const SMTExprRef &LHS,
                              const SMTExprRef &RHS) override final;
  SMTExprRef mkBVUMulOverflow(const SMTExprRef &LHS,
                              const SMTExprRef &RHS) override final;
  SMTExprRef mkBVSDivOverflow(const SMTExprRef &LHS,
                              const SMTExprRef &RHS) override final;
  SMTExprRef mkBVNegOverflow(const SMTExprRef &Exp) override final;
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
  SMTResult<ArrayModel> getArrayValues(const SMTExprRef &Array) override final;
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
  SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                          const SMTExprRef &InitValue,
                          ConstArrayLowering Lowering) override final;
  SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp,
                          const SMTSortRef &To) override final;
  SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) override final;
  checkResult check() override final;
  bool setTimeout(uint64_t Milliseconds) override final;

  checkResult
  checkSatAssuming(const std::vector<SMTExprRef> &Assumptions) override final;
  SMTResult<std::vector<SMTExprRef>> getUnsatAssumptions() override final;

  bool supports(SolverFeature Feature) const override final;
  void reset() override final;
  void push(unsigned nscopes = 1) override final;
  void pop(unsigned nscopes = 1) override final;
  void dump() override final;
  void dump(std::string &Out) override final;
  void dumpModel() override final;
  void dumpModel(std::string &Out) override final;

protected:
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

  /// Backends that natively support SMT-LIB datatypes (z3, cvc5, smtlib)
  /// override this to true. Other backends (bitwuzla, mathsat, stp,
  /// yices) inherit the default false and route tuple operations through
  /// the Camada-managed lowering in camadatuple.cpp.
  virtual bool nativeTupleSupport() const { return false; }

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

  // Overflow predicates. The default implementations encode the checks with
  // ordinary BV operations; backends with native overflow predicates
  // override them.
  virtual SMTExprRef mkBVAddOverflowImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS, bool IsSigned);

  virtual SMTExprRef mkBVSubOverflowImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS, bool IsSigned);

  virtual SMTExprRef mkBVMulOverflowImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS, bool IsSigned);

  virtual SMTExprRef mkBVSDivOverflowImpl(const SMTExprRef &LHS,
                                          const SMTExprRef &RHS);

  virtual SMTExprRef mkBVNegOverflowImpl(const SMTExprRef &Exp);

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

  /// Walk the backend model's representation of Array (store chains over a
  /// constant array, function interpretations, ...) into an ArrayModel.
  /// The default returns UnsupportedOperation for backends without a
  /// walkable array model.
  virtual SMTResult<ArrayModel> getArrayValuesImpl(const SMTExprRef &Array);

  /// SMTExprKind of a model-value constant of the given sort, for backends
  /// wrapping walked model terms.
  static SMTExprKind valueKindForSort(const SMTSortRef &Sort);

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

  /// Apply a per-check wall-clock limit (milliseconds; 0 disables) to the
  /// backend. Returns false when the backend cannot enforce it — the
  /// default for backends without a native limit or interrupt mechanism.
  /// reset() re-applies the stored limit through this hook, so overrides
  /// must be idempotent and callable right after resetImpl().
  virtual bool setTimeoutImpl(uint64_t Milliseconds);

  /// Default fallback for backends without native assumption support:
  /// push a scope, assert each assumption, check, pop. Goes through the
  /// public push/pop/addConstraint so the lazy constant-array journal
  /// stays consistent.
  virtual checkResult
  checkSatAssumingImpl(const std::vector<SMTExprRef> &Assumptions);

  /// Only dispatched right after checkSatAssumingImpl returned UNSAT for a
  /// non-empty assumption set (the wrapper answers the trivial cases).
  /// Native backends map the solver's core back to the SMTExprRefs stored
  /// in LastAssumptions.
  virtual SMTResult<std::vector<SMTExprRef>> getUnsatAssumptionsImpl();

  /// Backend feature bits for everything supports() cannot answer from
  /// the existing capability hooks (nativeTupleSupport,
  /// nativeConstArraySupport). The default claims nothing; backends
  /// override with a switch over the features they implement.
  virtual bool supportsImpl(SolverFeature Feature) const;

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
