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

// Ackermann-style array encoding (ArrayEncoding::Ackermann). Array terms
// are Camada-owned nodes with no backend representation; every select on
// a symbol root becomes a fresh element variable (a "read") tied to the
// root's other reads by pairwise congruence axioms
//   i = j  =>  r(root, i) = r(root, j)
// so the theory of arrays never reaches the backend. Stores and ites are
// lowered structurally at select time; array equality goes through the
// shared mkEncodedArrayEqual machinery (witness index + observed-index
// congruence), whose selects re-enter this encoding. Sound and complete
// for quantifier-free formulas only — see the guards in camadaimpl.cpp.

#include "camadacommon.h"
#include "camadaimpl.h"

#include <set>
#include <string>
#include <utility>
#include <vector>

namespace camada {

namespace {

/// Array sort owned by the Camada layer rather than any backend. Behaves
/// as a normal array sort through the generic accessors.
class CamadaAckArraySort : public SMTSort {
public:
  CamadaAckArraySort(SMTBackendKind BackendKind, const SMTSortRef &IndexSort,
                     const SMTSortRef &ElemSort)
      : SMTSort(SMTSortKind::Array, ArraySortData{IndexSort, ElemSort}),
        BackendKind(BackendKind) {}

  SMTBackendKind getBackendKind() const override { return BackendKind; }

  unsigned getWidthFromSolver() const override {
    fatalError("Width query on Camada-managed Ackermann array sort");
  }

  void dump(std::string &Out) const override {
    Out = "(CamadaAckArray";
    std::string SubOut;
    getIndexSort()->dump(SubOut);
    if (!SubOut.empty() && SubOut.back() == '\n')
      SubOut.pop_back();
    Out += " " + SubOut;
    getElementSort()->dump(SubOut);
    if (!SubOut.empty() && SubOut.back() == '\n')
      SubOut.pop_back();
    Out += " " + SubOut + ")\n";
  }

private:
  SMTBackendKind BackendKind;
};

/// Array expression owned by the Camada layer. The SMTExpr::Kind
/// discriminates the four shapes:
///   - SMTExprKind::Symbol: a root — selects mint per-index reads with
///     congruence axioms (state lives in SMTSolverImpl::AckArrayRoots)
///   - SMTExprKind::ArrayConst: selects return the initializer
///   - SMTExprKind::ArrayStore: selects lower to ite(i = idx, elem, base[i])
///   - SMTExprKind::Ite: selects distribute over the branches
class CamadaAckArrayExpr : public SMTExpr {
public:
  // Symbol form
  CamadaAckArrayExpr(SMTExprKind ExprKind, SMTBackendKind BackendKind,
                     const SMTSortRef &Sort, std::string SymbolName)
      : SMTExpr(ExprKind, Sort), SymbolName(std::move(SymbolName)),
        BackendKind(BackendKind) {}

  // Const form
  CamadaAckArrayExpr(SMTExprKind ExprKind, SMTBackendKind BackendKind,
                     const SMTSortRef &Sort, SMTExprRef Init)
      : SMTExpr(ExprKind, Sort), Init(std::move(Init)),
        BackendKind(BackendKind) {}

  // Store form (ArrayStore: base/index/element) and Ite form (Ite:
  // cond/true/false) share an arity, so one ctor assigns by kind.
  CamadaAckArrayExpr(SMTExprKind ExprKind, SMTBackendKind BackendKind,
                     const SMTSortRef &Sort, SMTExprRef A, SMTExprRef B,
                     SMTExprRef C)
      : SMTExpr(ExprKind, Sort), BackendKind(BackendKind) {
    if (ExprKind == SMTExprKind::ArrayStore) {
      Base = std::move(A);
      Index = std::move(B);
      Element = std::move(C);
    } else {
      Cond = std::move(A);
      TrueArr = std::move(B);
      FalseArr = std::move(C);
    }
  }

  SMTBackendKind getBackendKind() const override { return BackendKind; }

  void dump(std::string &Out) const override {
    switch (getKind()) {
    case SMTExprKind::Symbol:
      Out = "(CamadaAckArraySymbol " + SymbolName + ")\n";
      return;
    case SMTExprKind::ArrayConst:
      Out = "(CamadaAckArrayConst ...)\n";
      return;
    case SMTExprKind::ArrayStore:
      Out = "(CamadaAckArrayStore ...)\n";
      return;
    case SMTExprKind::Ite:
      Out = "(CamadaAckArrayIte ...)\n";
      return;
    default:
      fatalError("Invalid CamadaAckArrayExpr SMTExprKind");
    }
  }

  std::string SymbolName;
  SMTExprRef Init;
  SMTExprRef Base;
  SMTExprRef Index;
  SMTExprRef Element;
  SMTExprRef Cond;
  SMTExprRef TrueArr;
  SMTExprRef FalseArr;

protected:
  // Structural host-side equality, matching the Camada tuple nodes'
  // convention. Nothing interns these nodes, so pointer identity is only
  // syntactic identity — no correctness argument relies on structurally
  // equal nodes being the same object. SMT-level equality goes through
  // mkEncodedArrayEqual.
  bool equal_to(SMTExpr const &Other) const override {
    if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind() ||
        getKind() != Other.getKind())
      return false;
    auto const &Rhs = static_cast<const CamadaAckArrayExpr &>(Other);
    switch (getKind()) {
    case SMTExprKind::Symbol:
      return SymbolName == Rhs.SymbolName;
    case SMTExprKind::ArrayConst:
      return *Init == *Rhs.Init;
    case SMTExprKind::ArrayStore:
      return *Base == *Rhs.Base && *Index == *Rhs.Index &&
             *Element == *Rhs.Element;
    case SMTExprKind::Ite:
      return *Cond == *Rhs.Cond && *TrueArr == *Rhs.TrueArr &&
             *FalseArr == *Rhs.FalseArr;
    default:
      return false;
    }
  }

private:
  SMTBackendKind BackendKind;
};

const CamadaAckArrayExpr *toAckArrayExpr(const SMTExprRef &Exp) {
  if (!Exp || !Exp->Sort->isArraySort())
    return nullptr;
  return dynamic_cast<const CamadaAckArrayExpr *>(Exp.get());
}

const CamadaAckArrayExpr *requireAckArrayExpr(const SMTExprRef &Exp) {
  const CamadaAckArrayExpr *AE = toAckArrayExpr(Exp);
  fatalErrorIf(AE == nullptr,
               "Native array expression reached the Ackermann array "
               "encoding; array terms must be built through this solver");
  return AE;
}

} // namespace

SMTSortRef SMTSolverImpl::mkAckArraySort(const SMTSortRef &IndexSort,
                                         const SMTSortRef &ElemSort) {
  fatalErrorIf(IndexSort->isArraySort(),
               "Array-sorted indexes are not supported with the Ackermann "
               "array encoding");
  fatalErrorIf(ElemSort->isArraySort(),
               "Nested arrays are not supported with the Ackermann array "
               "encoding");
  return makeSortRef(
      CamadaAckArraySort(IndexSort->getBackendKind(), IndexSort, ElemSort));
}

SMTExprRef SMTSolverImpl::mkAckArraySymbol(const std::string &Name,
                                           const SMTSortRef &Sort) {
  assert(dynamic_cast<const CamadaAckArraySort *>(Sort.get()) != nullptr);
  return makeExprRef<CamadaAckArrayExpr>(SMTExprKind::Symbol,
                                         Sort->getBackendKind(), Sort, Name);
}

SMTExprRef SMTSolverImpl::mkAckArrayStore(const SMTExprRef &Array,
                                          const SMTExprRef &Index,
                                          const SMTExprRef &Element) {
  requireAckArrayExpr(Array);
  return makeExprRef<CamadaAckArrayExpr>(SMTExprKind::ArrayStore,
                                         Array->getBackendKind(), Array->Sort,
                                         Array, Index, Element);
}

SMTExprRef SMTSolverImpl::mkAckArrayIte(const SMTExprRef &Cond,
                                        const SMTExprRef &T,
                                        const SMTExprRef &F) {
  requireAckArrayExpr(T);
  requireAckArrayExpr(F);
  return makeExprRef<CamadaAckArrayExpr>(SMTExprKind::Ite, T->getBackendKind(),
                                         T->Sort, Cond, T, F);
}

SMTExprRef SMTSolverImpl::mkAckArrayConst(const SMTSortRef &IndexSort,
                                          const SMTExprRef &InitValue) {
  // The public mkArraySort routes back to mkAckArraySort (and caches).
  SMTSortRef Sort = mkArraySort(IndexSort, InitValue->Sort);
  return makeExprRef<CamadaAckArrayExpr>(
      SMTExprKind::ArrayConst, Sort->getBackendKind(), Sort, InitValue);
}

SMTExprRef SMTSolverImpl::mkAckArraySelect(const SMTExprRef &Array,
                                           const SMTExprRef &Index) {
  const CamadaAckArrayExpr *AE = requireAckArrayExpr(Array);
  switch (AE->getKind()) {
  case SMTExprKind::ArrayStore:
    return mkIte(mkEqual(Index, AE->Index), AE->Element,
                 mkAckArraySelect(AE->Base, Index));
  case SMTExprKind::Ite:
    return mkIte(AE->Cond, mkAckArraySelect(AE->TrueArr, Index),
                 mkAckArraySelect(AE->FalseArr, Index));
  case SMTExprKind::ArrayConst:
    return AE->Init;
  case SMTExprKind::Symbol:
    break;
  default:
    fatalError("Invalid CamadaAckArrayExpr SMTExprKind");
  }

  // Symbol root: mint (or reuse) the Ackermann read for this index.
  // BV-constant indexes are canonicalized by value so equal constants
  // share one read; every other index term keys by object identity —
  // structurally equal terms built separately get distinct reads, which
  // is sound (their congruence guard is trivially true) if redundant.
  AckArrayRootState &Root = AckArrayRoots[&*Array];
  auto BitsIt = AckBVConstBits.find(&*Index);
  const bool IndexIsConst = BitsIt != AckBVConstBits.end();
  if (IndexIsConst) {
    if (auto It = Root.ReadsByConstBits.find(BitsIt->second);
        It != Root.ReadsByConstBits.end())
      return Root.Reads[It->second].Value;
  } else {
    if (auto It = Root.ReadsByIndex.find(&*Index);
        It != Root.ReadsByIndex.end())
      return Root.Reads[It->second].Value;
  }

  SMTExprRef Read =
      mkSymbolUnchecked("__CAMADA_ackread" + std::to_string(AckArrayCounter++),
                        Array->Sort->getElementSort());
  // Cache-insert before emitting axioms, and iterate over a copy: the
  // constraints below go through public wrappers, matching the existing
  // lazy-machinery discipline against re-entrant construction.
  const std::size_t Pos = Root.Reads.size();
  Root.Reads.push_back(
      AckArrayRead{Index, Read, IndexIsConst,
                   IndexIsConst ? BitsIt->second : std::string()});
  if (IndexIsConst)
    Root.ReadsByConstBits.emplace(BitsIt->second, Pos);
  else
    Root.ReadsByIndex.emplace(&*Index, Pos);

  const std::vector<AckArrayRead> Prior(Root.Reads.begin(),
                                        Root.Reads.end() - 1);
  for (const AckArrayRead &P : Prior) {
    // Two distinct BV-constant indexes cannot alias (equal values share
    // one read by construction), so their congruence axiom is skipped.
    if (IndexIsConst && P.IndexIsConst)
      continue;
    SMTExprRef Constraint =
        mkImplies(mkEqual(Index, P.Index), mkEqual(Read, P.Value));
    addConstraint(Constraint);
    // Congruence is a scope-independent fact; journal it so pop()
    // re-asserts it at the outer level (see LazyConstraintLevels).
    LazyConstraintLevels.back().push_back(std::move(Constraint));
  }
  return Read;
}

// --- Model queries -------------------------------------------------------
//
// Everything below runs after a SAT check and must not mint reads, emit
// axioms, or count as formula observations — the model would be
// invalidated. Resolution canonicalizes indexes by model value
// (lazyIndexModelBits), walks store/ite chains under the model, and at
// symbol roots consults the reads of the whole equality class: roots
// connected by an ArrayEqualLink whose EqVar is true in the model must
// answer consistently.

struct AckClassWalk {
  // Terminal symbol roots reached by any chain in the class.
  std::vector<const SMTExpr *> Roots;
  // First constant-root initializer reached, if any.
  SMTExprRef ConstInit;
  // Value found at the queried index by a store step, if any.
  SMTExprRef StoreHit;
  // Store entries seen along the walked chains, outermost first per
  // chain, deduped by index model value (for getArrayValues).
  std::vector<std::pair<SMTExprRef, SMTExprRef>> StoreEntries;
  std::set<std::string> SeenStoreBits;
  bool Failed = false;
};

// Walk one chain to its terminal under the current model, recording store
// entries. QueryBits is empty for getArrayValues-style walks (collect
// everything) and non-empty for point queries (stop at a store hit).
void SMTSolverImpl::ackWalkChain(const SMTExpr *Node,
                                 const std::string &QueryBits,
                                 AckClassWalk &Walk) {
  while (true) {
    const auto *AE = dynamic_cast<const CamadaAckArrayExpr *>(Node);
    if (AE == nullptr) {
      Walk.Failed = true;
      return;
    }
    switch (AE->getKind()) {
    case SMTExprKind::ArrayStore: {
      const std::string StepBits = lazyIndexModelBits(AE->Index);
      if (StepBits.empty()) {
        Walk.Failed = true;
        return;
      }
      if (!QueryBits.empty() && StepBits == QueryBits && !Walk.StoreHit) {
        Walk.StoreHit = AE->Element;
        return;
      }
      if (Walk.SeenStoreBits.insert(StepBits).second)
        Walk.StoreEntries.emplace_back(AE->Index, AE->Element);
      Node = &*AE->Base;
      continue;
    }
    case SMTExprKind::Ite: {
      SMTResult<bool> Cond = getBool(AE->Cond);
      if (!Cond) {
        Walk.Failed = true;
        return;
      }
      Node = Cond.value() ? &*AE->TrueArr : &*AE->FalseArr;
      continue;
    }
    case SMTExprKind::ArrayConst:
      if (!Walk.ConstInit)
        Walk.ConstInit = AE->Init;
      return;
    case SMTExprKind::Symbol:
      Walk.Roots.push_back(Node);
      return;
    default:
      Walk.Failed = true;
      return;
    }
  }
}

// Expand Walk to the full equality class of the array it started from:
// every ArrayEqualLink of the same sort whose EqVar is true in the model
// and whose sides reach a root already in the class pulls both sides'
// chains in. Iterates to a fixpoint.
void SMTSolverImpl::ackExpandEqualityClass(const SMTSortRef &ArraySort,
                                           const std::string &QueryBits,
                                           AckClassWalk &Walk) {
  std::set<const SMTExpr *> InClass(Walk.Roots.begin(), Walk.Roots.end());
  std::set<std::size_t> UsedLinks;
  bool Changed = true;
  while (Changed && !Walk.Failed && !Walk.StoreHit) {
    Changed = false;
    for (std::size_t LinkId = 0; LinkId < ArrayEqualLinks.size(); ++LinkId) {
      if (UsedLinks.count(LinkId) != 0)
        continue;
      const ArrayEqualLink &Link = ArrayEqualLinks[LinkId];
      if (Link.LHS->Sort != ArraySort)
        continue;
      // Roots of each side under the model, computed with a throwaway
      // walk so a side's store entries only join the class walk when the
      // link is actually taken.
      AckClassWalk L, R;
      ackWalkChain(&*Link.LHS, std::string(), L);
      ackWalkChain(&*Link.RHS, std::string(), R);
      if (L.Failed || R.Failed)
        continue;
      const auto Touches = [&InClass](const AckClassWalk &Side) {
        for (const SMTExpr *Root : Side.Roots)
          if (InClass.count(Root) != 0)
            return true;
        return false;
      };
      if (!Touches(L) && !Touches(R))
        continue;
      SMTResult<bool> EqVal = getBool(Link.EqVar);
      if (!EqVal || !EqVal.value()) {
        UsedLinks.insert(LinkId);
        continue;
      }
      UsedLinks.insert(LinkId);
      Changed = true;
      for (const SMTExprRef &Side : {Link.LHS, Link.RHS}) {
        ackWalkChain(&*Side, QueryBits, Walk);
        if (Walk.Failed || Walk.StoreHit)
          return;
      }
      for (const SMTExpr *Root : Walk.Roots)
        InClass.insert(Root);
    }
  }
}

SMTExprRef SMTSolverImpl::ackDefaultElementValue(const SMTSortRef &Sort) {
  if (Sort->isBoolSort())
    return mkBool(false);
  // FP first: BVFP sorts answer true to isBVSort() too.
  if (Sort->isFPSort())
    return mkFPFromBin(
        std::string(Sort->getWidth(), '0'), Sort->getFPExponentWidth(),
        Sort->isBVFPSort() ? FPEncoding::BV : FPEncoding::Native);
  if (Sort->isBVSort())
    return mkBVFromBin(std::string(Sort->getWidth(), '0'), Sort);
  if (Sort->isIntSort())
    return mkInt(0);
  if (Sort->isRealSort())
    return mkReal("0");
  fatalError("Cannot synthesize a default model value for this element "
             "sort under the Ackermann array encoding");
}

SMTExprRef SMTSolverImpl::resolveAckArrayElement(const SMTExprRef &Array,
                                                 const SMTExprRef &Index) {
  const std::string QueryBits = lazyIndexModelBits(Index);
  fatalErrorIf(QueryBits.empty(),
               "Cannot evaluate the queried index against the model under "
               "the Ackermann array encoding (bool/BV index sorts only)");

  AckClassWalk Walk;
  ackWalkChain(&*Array, QueryBits, Walk);
  if (!Walk.StoreHit && !Walk.Failed)
    ackExpandEqualityClass(Array->Sort, QueryBits, Walk);
  fatalErrorIf(Walk.Failed,
               "Could not walk the array derivation chain against the "
               "model under the Ackermann array encoding");
  if (Walk.StoreHit)
    return Walk.StoreHit;

  // Match the queried value against the class's reads.
  for (const SMTExpr *Root : Walk.Roots) {
    auto RootIt = AckArrayRoots.find(Root);
    if (RootIt == AckArrayRoots.end())
      continue;
    for (const AckArrayRead &R : RootIt->second.Reads) {
      const std::string ReadBits =
          R.IndexIsConst ? R.ConstBits : lazyIndexModelBits(R.Index);
      if (!ReadBits.empty() && ReadBits == QueryBits)
        return R.Value;
    }
  }

  if (Walk.ConstInit)
    return Walk.ConstInit;

  // Genuinely unconstrained: hand out a stable default, memoized per
  // (primary root, index value) for the lifetime of the current model.
  const SMTExpr *MemoKey = Walk.Roots.empty() ? &*Array : Walk.Roots.front();
  auto [It, Inserted] = AckModelDefaults.try_emplace(
      std::make_pair(MemoKey, QueryBits), SMTExprRef{});
  if (Inserted)
    It->second = ackDefaultElementValue(Array->Sort->getElementSort());
  return It->second;
}

SMTResult<ArrayModel> SMTSolverImpl::ackArrayModel(const SMTExprRef &Array) {
  AckClassWalk Walk;
  ackWalkChain(&*Array, std::string(), Walk);
  if (!Walk.Failed)
    ackExpandEqualityClass(Array->Sort, std::string(), Walk);
  if (Walk.Failed)
    return SMTError{SMTErrorCode::BackendError,
                    CachedBoolExprs[0]->getBackendKind(),
                    "Could not walk the array derivation chain against the "
                    "model under the Ackermann array encoding"};

  ArrayModel Model;
  // Store entries first (outermost first per chain, own chain walked
  // first, deduped by index value in ackWalkChain), then the class's
  // reads at still-unseen index values.
  for (auto &Entry : Walk.StoreEntries)
    Model.Entries.emplace_back(Entry.first, Entry.second);
  for (const SMTExpr *Root : Walk.Roots) {
    auto RootIt = AckArrayRoots.find(Root);
    if (RootIt == AckArrayRoots.end())
      continue;
    for (const AckArrayRead &R : RootIt->second.Reads) {
      const std::string ReadBits =
          R.IndexIsConst ? R.ConstBits : lazyIndexModelBits(R.Index);
      if (ReadBits.empty())
        return SMTError{SMTErrorCode::BackendError,
                        CachedBoolExprs[0]->getBackendKind(),
                        "Could not evaluate a read index while walking an "
                        "Ackermann array model"};
      if (Walk.SeenStoreBits.insert(ReadBits).second)
        Model.Entries.emplace_back(R.Index, R.Value);
    }
  }
  Model.Base = Walk.ConstInit; // null for symbol roots: unconstrained off
                               // the listed entries
  return Model;
}

} // namespace camada
