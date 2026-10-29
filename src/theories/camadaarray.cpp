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

#include "../camadaerrors.h"
#include "../core/camadaimpl.h"

#include <set>
#include <string>
#include <unordered_map>
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
    appendDumped(Out, *getIndexSort());
    appendDumped(Out, *getElementSort());
    Out += ")\n";
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
  auto BitsIt = AckBVConstBits.find(&*Index);
  const bool IndexIsConst = BitsIt != AckBVConstBits.end();

  switch (AE->getKind()) {
  case SMTExprKind::ArrayStore:
  case SMTExprKind::Ite: {
    // Chain nodes are shared by construction, so memoize the lowered
    // select per (node, index): repeated selects reuse one term instead
    // of rebuilding the ite cascade. Constant indexes key by value,
    // mirroring the read canonicalization at symbol roots below.
    {
      AckSelectMemoState &Memo = AckSelectMemo[&*Array];
      if (IndexIsConst) {
        if (auto It = Memo.ByConstBits.find(BitsIt->second);
            It != Memo.ByConstBits.end())
          return It->second;
      } else if (auto It = Memo.ByIndex.find(&*Index);
                 It != Memo.ByIndex.end()) {
        return It->second;
      }
    }
    SMTExprRef Result;
    if (AE->getKind() == SMTExprKind::ArrayStore) {
      // Host-side fold before emitting anything: a select whose index is
      // syntactically the stored index (same object, or equal BV-constant
      // bits) hits the store; two distinct BV constants provably miss and
      // skip the level. Only genuinely undecidable levels emit an ite.
      auto StoreBitsIt = AckBVConstBits.find(&*AE->Index);
      const bool StoreIsConst = StoreBitsIt != AckBVConstBits.end();
      if (&*Index == &*AE->Index || (IndexIsConst && StoreIsConst &&
                                     BitsIt->second == StoreBitsIt->second))
        Result = AE->Element;
      else if (IndexIsConst && StoreIsConst)
        Result = mkAckArraySelect(AE->Base, Index);
      else
        Result = mkIte(mkEqual(Index, AE->Index), AE->Element,
                       mkAckArraySelect(AE->Base, Index));
    } else {
      Result = mkIte(AE->Cond, mkAckArraySelect(AE->TrueArr, Index),
                     mkAckArraySelect(AE->FalseArr, Index));
    }
    // Fresh lookup: the recursion above inserts into AckSelectMemo, which
    // can rehash and invalidate any reference held across it.
    AckSelectMemoState &Memo = AckSelectMemo[&*Array];
    if (IndexIsConst)
      Memo.ByConstBits.emplace(BitsIt->second, Result);
    else
      Memo.ByIndex.emplace(&*Index, Result);
    return Result;
  }
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
    // Not model-preserving: Read is a fresh variable minted for this
    // select, so the backend's current model has no value for it and
    // asserting the axiom genuinely discards that model.
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
// (lazyIndexModelBits) and searches the nodes equal to the queried array
// at that index: an ite and its taken branch, a store and its base when
// the store misses the index, the two sides of an ArrayEqualLink whose
// EqVar is true in the model.

struct AckClassWalk {
  // Edges between nodes equal at the query index under the model.
  std::unordered_map<const SMTExpr *, std::vector<const SMTExpr *>> Edges;
  // Values pinned at the query index: a store hitting it, a constant
  // array's initializer, a root's read at it.
  std::unordered_map<const SMTExpr *, SMTExprRef> Pinned;
  std::set<const SMTExpr *> Walked;
  // Nodes equal to the queried array at the query index, BFS order.
  std::vector<const SMTExpr *> Component;
  // First value pinned in Component, if any.
  SMTExprRef Value;
  bool Failed = false;

  void link(const SMTExpr *A, const SMTExpr *B) {
    Edges[A].push_back(B);
    Edges[B].push_back(A);
  }
};

// Record Node's chain under the model into Walk. Returns false when the
// chain cannot be evaluated.
bool SMTSolverImpl::ackWalkChain(const SMTExpr *Node,
                                 const std::string &QueryBits,
                                 AckClassWalk &Walk) {
  while (Walk.Walked.insert(Node).second) {
    const auto *AE = dynamic_cast<const CamadaAckArrayExpr *>(Node);
    if (AE == nullptr)
      return false;
    const SMTExpr *Next = nullptr;
    switch (AE->getKind()) {
    case SMTExprKind::ArrayStore:
      Next = &*AE->Base;
      if (!QueryBits.empty()) {
        const std::string StepBits = lazyIndexModelBits(AE->Index);
        if (StepBits.empty())
          return false;
        // A store hitting the index says nothing about its base there.
        if (StepBits == QueryBits) {
          Walk.Pinned.emplace(Node, AE->Element);
          break;
        }
      }
      Walk.link(Node, Next);
      break;
    case SMTExprKind::Ite: {
      SMTResult<bool> Cond = getBool(AE->Cond);
      if (!Cond)
        return false;
      Next = Cond.value() ? &*AE->TrueArr : &*AE->FalseArr;
      Walk.link(Node, Next);
      break;
    }
    case SMTExprKind::ArrayConst:
      Walk.Pinned.emplace(Node, AE->Init);
      return true;
    case SMTExprKind::Symbol:
      if (auto RootIt = AckArrayRoots.find(Node);
          !QueryBits.empty() && RootIt != AckArrayRoots.end())
        for (const AckArrayRead &R : RootIt->second.Reads)
          if ((R.IndexIsConst ? R.ConstBits : lazyIndexModelBits(R.Index)) ==
              QueryBits) {
            Walk.Pinned.emplace(Node, R.Value);
            break;
          }
      return true;
    default:
      return false;
    }
    Node = Next;
  }
  return true;
}

// Collect the nodes equal to Array at the query index under the model:
// its chain, and the chains of every array equality true in the model.
// Empty QueryBits stands for an index that no store or read hits.
void SMTSolverImpl::ackClassValue(const SMTExprRef &Array,
                                  const std::string &QueryBits,
                                  AckClassWalk &Walk) {
  if (!ackWalkChain(&*Array, QueryBits, Walk)) {
    Walk.Failed = true;
    return;
  }
  // ponytail: walks every link of the sort per query; index the links by
  // sort if model queries get slow.
  for (const ArrayEqualLink &Link : ArrayEqualLinks) {
    if (Link.LHS->Sort != Array->Sort)
      continue;
    SMTResult<bool> Eq = getBool(Link.EqVar);
    if (Eq && Eq.value() && ackWalkChain(&*Link.LHS, QueryBits, Walk) &&
        ackWalkChain(&*Link.RHS, QueryBits, Walk))
      Walk.link(&*Link.LHS, &*Link.RHS);
  }
  std::set<const SMTExpr *> Seen{&*Array};
  Walk.Component.push_back(&*Array);
  for (std::size_t I = 0; I < Walk.Component.size(); ++I) {
    const SMTExpr *Node = Walk.Component[I];
    if (auto It = Walk.Pinned.find(Node);
        !Walk.Value && It != Walk.Pinned.end())
      Walk.Value = It->second;
    for (const SMTExpr *Next : Walk.Edges[Node])
      if (Seen.insert(Next).second)
        Walk.Component.push_back(Next);
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
  // getArrayElement screens the index sort through ackCanEvaluateIndexSort
  // and its ModelAvailable gate rejects a model-less query, so reaching
  // this with empty bits means the screen and this check disagree -- a
  // Camada bug, not a caller mistake.
  fatalErrorIf(QueryBits.empty(),
               "Cannot evaluate the queried index against the model under "
               "the Ackermann array encoding (bool/BV index sorts only)");

  AckClassWalk Walk;
  ackClassValue(Array, QueryBits, Walk);
  fatalErrorIf(Walk.Failed,
               "Could not walk the array derivation chain against the "
               "model under the Ackermann array encoding");
  if (Walk.Value)
    return Walk.Value;

  // Genuinely unconstrained: hand out a stable default, memoized per
  // (node, index value) across the class for the lifetime of the model.
  for (const SMTExpr *Node : Walk.Component)
    if (auto It = AckModelDefaults.find({Node, QueryBits});
        It != AckModelDefaults.end())
      return It->second;
  SMTExprRef Value = ackDefaultElementValue(Array->Sort->getElementSort());
  for (const SMTExpr *Node : Walk.Component)
    AckModelDefaults.emplace(std::make_pair(Node, QueryBits), Value);
  return Value;
}

SMTResult<ArrayModel> SMTSolverImpl::ackArrayModel(const SMTExprRef &Array) {
  const SMTError WalkError{SMTErrorCode::BackendError, backendKind(),
                           "Could not walk the array derivation chain "
                           "against the model under the Ackermann array "
                           "encoding"};
  AckClassWalk Walk;
  ackClassValue(Array, std::string(), Walk);
  if (Walk.Failed)
    return WalkError;

  ArrayModel Model;
  // Off every store and read index the class reaches, the value is the
  // constant initializer, if any (null: unconstrained off the entries).
  Model.Base = Walk.Value;
  std::set<std::string> Seen;
  const auto Add = [&](const SMTExprRef &Index) {
    const std::string Bits = lazyIndexModelBits(Index);
    if (Bits.empty())
      return false;
    if (!Seen.insert(Bits).second)
      return true;
    AckClassWalk At;
    ackClassValue(Array, Bits, At);
    if (At.Value)
      Model.Entries.emplace_back(Index, At.Value);
    return !At.Failed;
  };
  for (const SMTExpr *Node : Walk.Component) {
    const auto *AE = static_cast<const CamadaAckArrayExpr *>(Node);
    if (AE->getKind() == SMTExprKind::ArrayStore && !Add(AE->Index))
      return WalkError;
    if (auto RootIt = AckArrayRoots.find(Node); RootIt != AckArrayRoots.end())
      for (const AckArrayRead &R : RootIt->second.Reads)
        if (!Add(R.Index))
          return WalkError;
  }
  return Model;
}

} // namespace camada
