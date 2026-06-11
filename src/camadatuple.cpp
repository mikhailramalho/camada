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

#include "camadatuple.h"

#include "camadacommon.h"
#include "camadaimpl.h"

#include <utility>

namespace camada {

namespace {

/// Tuple sort owned by the Camada layer rather than any backend. Used by
/// the encoding for backends without native datatype support.
class CamadaTupleSort : public SMTSort {
public:
  CamadaTupleSort(SMTBackendKind BackendKind,
                  const std::vector<SMTSortRef> &ElementSorts)
      : SMTSort(SMTSortKind::Tuple, TupleSortData{ElementSorts}),
        BackendKind(BackendKind) {}

  SMTBackendKind getBackendKind() const override { return BackendKind; }

  unsigned getWidthFromSolver() const override {
    fatalError("Width query on Camada-managed tuple sort");
  }

  void dump(std::string &Out) const override {
    Out = "(CamadaTuple";
    for (const auto &E : getTupleElementSorts()) {
      Out += " ";
      std::string ElemOut;
      E->dump(ElemOut);
      if (!ElemOut.empty() && ElemOut.back() == '\n')
        ElemOut.pop_back();
      Out += ElemOut;
    }
    Out += ")\n";
  }

private:
  SMTBackendKind BackendKind;
};

/// Tuple expression owned by the Camada layer. The SMTExpr::Kind
/// discriminates between three shapes (Symbol / TupleConst / Ite) — no
/// separate NodeKind is needed:
///   - SMTExprKind::Symbol: lazy — per-field symbols minted on demand by
///     mkTupleSelect
///   - SMTExprKind::TupleConst: eager — components stored verbatim
///   - SMTExprKind::Ite: lazy — distributes over fields when selected
class CamadaTupleExpr : public SMTExpr {
public:
  // Symbol form (SMTExprKind::Symbol)
  CamadaTupleExpr(SMTExprKind ExprKind, SMTBackendKind BackendKind,
                  const SMTSortRef &Sort, std::string SymbolName)
      : SMTExpr(ExprKind, Sort), SymbolName(std::move(SymbolName)),
        BackendKind(BackendKind) {}

  // Value form (SMTExprKind::TupleConst)
  CamadaTupleExpr(SMTExprKind ExprKind, SMTBackendKind BackendKind,
                  const SMTSortRef &Sort, std::vector<SMTExprRef> Elements)
      : SMTExpr(ExprKind, Sort), Elements(std::move(Elements)),
        BackendKind(BackendKind) {}

  // Ite form (SMTExprKind::Ite)
  CamadaTupleExpr(SMTExprKind ExprKind, SMTBackendKind BackendKind,
                  const SMTSortRef &Sort, SMTExprRef Cond, SMTExprRef T,
                  SMTExprRef F)
      : SMTExpr(ExprKind, Sort), Cond(std::move(Cond)), TrueTuple(std::move(T)),
        FalseTuple(std::move(F)), BackendKind(BackendKind) {}

  SMTBackendKind getBackendKind() const override { return BackendKind; }

  void dump(std::string &Out) const override {
    switch (getKind()) {
    case SMTExprKind::Symbol:
      Out = "(CamadaTupleSymbol " + SymbolName + ")\n";
      return;
    case SMTExprKind::TupleConst: {
      Out = "(CamadaTupleValue";
      for (const auto &E : Elements) {
        Out += " ";
        std::string ElemOut;
        E->dump(ElemOut);
        if (!ElemOut.empty() && ElemOut.back() == '\n')
          ElemOut.pop_back();
        Out += ElemOut;
      }
      Out += ")\n";
      return;
    }
    case SMTExprKind::Ite:
      Out = "(CamadaTupleIte ...)\n";
      return;
    default:
      fatalError("Invalid CamadaTupleExpr SMTExprKind");
    }
  }

  std::string SymbolName;
  std::vector<SMTExprRef> Elements;
  SMTExprRef Cond;
  SMTExprRef TrueTuple;
  SMTExprRef FalseTuple;

protected:
  // Structural host-side equality. Two freshly built nodes compare equal
  // when they describe the same tuple shape with components that
  // themselves compare equal via SMTExpr::operator== — symbol vs symbol
  // matches on name; value vs value recursively compares the field
  // vector; ite vs ite recursively compares cond + branches. This is
  // host-side AST equality only; SMT-level satisfaction equality goes
  // through mkCamadaTupleEqual, which decomposes into per-field
  // mkEqual + mkAnd.
  bool equal_to(SMTExpr const &Other) const override {
    if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind() ||
        getKind() != Other.getKind())
      return false;
    auto const &Rhs = static_cast<const CamadaTupleExpr &>(Other);
    switch (getKind()) {
    case SMTExprKind::Symbol:
      return SymbolName == Rhs.SymbolName;
    case SMTExprKind::TupleConst: {
      if (Elements.size() != Rhs.Elements.size())
        return false;
      for (std::size_t I = 0; I < Elements.size(); ++I)
        if (!(*Elements[I] == *Rhs.Elements[I]))
          return false;
      return true;
    }
    case SMTExprKind::Ite:
      return *Cond == *Rhs.Cond && *TrueTuple == *Rhs.TrueTuple &&
             *FalseTuple == *Rhs.FalseTuple;
    default:
      return false;
    }
  }

private:
  SMTBackendKind BackendKind;
};

const CamadaTupleExpr *toCamadaTupleExpr(const SMTExprRef &Exp) {
  if (!Exp || !Exp->Sort->isTupleSort())
    return nullptr;
  return dynamic_cast<const CamadaTupleExpr *>(Exp.get());
}

/// Array sort whose element involves a tuple, owned by the Camada layer.
/// Behaves as a normal array sort through the generic accessors
/// (getIndexSort/getElementSort); additionally carries the flattened
/// per-leaf array sorts the bundle representation aligns with.
class CamadaTupleArraySort : public SMTSort {
public:
  CamadaTupleArraySort(SMTBackendKind BackendKind, const SMTSortRef &IndexSort,
                       const SMTSortRef &ElemSort,
                       std::vector<SMTSortRef> LeafSorts)
      : SMTSort(SMTSortKind::Array, ArraySortData{IndexSort, ElemSort}),
        LeafSorts(std::move(LeafSorts)), BackendKind(BackendKind) {}

  SMTBackendKind getBackendKind() const override { return BackendKind; }

  unsigned getWidthFromSolver() const override {
    fatalError("Width query on Camada-managed tuple-array sort");
  }

  void dump(std::string &Out) const override {
    Out = "(CamadaTupleArray";
    for (const auto &L : LeafSorts) {
      Out += " ";
      std::string LeafOut;
      L->dump(LeafOut);
      if (!LeafOut.empty() && LeafOut.back() == '\n')
        LeafOut.pop_back();
      Out += LeafOut;
    }
    Out += ")\n";
  }

  std::vector<SMTSortRef> LeafSorts;

private:
  SMTBackendKind BackendKind;
};

/// Bundle of per-leaf backend arrays representing an array of tuples.
/// LeafArrays aligns positionally with the sort's LeafSorts; every leaf
/// is an ordinary backend array expression, so the existing lazy
/// constant-array, encoded-equality, and model machinery applies per
/// leaf with no new backend code.
class CamadaTupleArrayExpr : public SMTExpr {
public:
  CamadaTupleArrayExpr(SMTExprKind ExprKind, SMTBackendKind BackendKind,
                       const SMTSortRef &Sort, std::vector<SMTExprRef> Leaves)
      : SMTExpr(ExprKind, Sort), LeafArrays(std::move(Leaves)),
        BackendKind(BackendKind) {}

  SMTBackendKind getBackendKind() const override { return BackendKind; }

  void dump(std::string &Out) const override {
    Out = "(CamadaTupleArray";
    for (const auto &L : LeafArrays) {
      Out += " ";
      std::string LeafOut;
      L->dump(LeafOut);
      if (!LeafOut.empty() && LeafOut.back() == '\n')
        LeafOut.pop_back();
      Out += LeafOut;
    }
    Out += ")\n";
  }

  std::vector<SMTExprRef> LeafArrays;

protected:
  bool equal_to(SMTExpr const &Other) const override {
    if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind() ||
        getKind() != Other.getKind())
      return false;
    auto const &Rhs = static_cast<const CamadaTupleArrayExpr &>(Other);
    if (LeafArrays.size() != Rhs.LeafArrays.size())
      return false;
    for (std::size_t I = 0; I < LeafArrays.size(); ++I)
      if (!(*LeafArrays[I] == *Rhs.LeafArrays[I]))
        return false;
    return true;
  }

private:
  SMTBackendKind BackendKind;
};

const CamadaTupleArrayExpr *toCamadaTupleArrayExpr(const SMTExprRef &Exp) {
  if (!Exp || !Exp->Sort->isArraySort())
    return nullptr;
  return dynamic_cast<const CamadaTupleArrayExpr *>(Exp.get());
}

/// Flattened per-leaf array sorts of `Array<Index, Elem>` where Elem
/// involves a tuple: one `Array<Index, L>` per scalar leaf path L
/// through Elem, built through the public mkArraySort (leaves contain no
/// tuples, so these are native sorts — possibly nested arrays).
void collectLeafSortsOf(SMTSolverImpl &Solver, const SMTSortRef &Sort,
                        std::vector<SMTSortRef> &Out) {
  if (Sort->isTupleSort()) {
    for (const auto &Elem : Sort->getTupleElementSorts())
      collectLeafSortsOf(Solver, Elem, Out);
    return;
  }
  if (Sort->isArraySort() && sortContainsTuple(Sort->getElementSort())) {
    std::vector<SMTSortRef> ElemLeaves;
    collectLeafSortsOf(Solver, Sort->getElementSort(), ElemLeaves);
    for (const auto &L : ElemLeaves)
      Out.push_back(Solver.mkArraySort(Sort->getIndexSort(), L));
    return;
  }
  Out.push_back(Sort);
}

const std::vector<SMTSortRef> &leafSortsOf(const SMTSortRef &Sort) {
  const auto *AS = dynamic_cast<const CamadaTupleArraySort *>(Sort.get());
  fatalErrorIf(AS == nullptr, "Expected a Camada-managed tuple-array sort");
  return AS->LeafSorts;
}

/// Flatten a value of a tuple-involving sort into its leaf expressions,
/// in leaf-sort order. Tuple values decompose through the public
/// mkTupleSelect (which handles symbol/value/ite shapes); tuple-array
/// values contribute their bundles; scalars and native arrays are leaves.
void collectLeafExprsOf(SMTSolverImpl &Solver, const SMTExprRef &Value,
                        std::vector<SMTExprRef> &Out) {
  if (Value->Sort->isTupleSort()) {
    const std::size_t Fields = Value->Sort->getTupleElementSorts().size();
    for (unsigned I = 0; I < Fields; ++I)
      collectLeafExprsOf(Solver, Solver.mkTupleSelect(Value, I), Out);
    return;
  }
  if (Value->Sort->isArraySort() &&
      sortContainsTuple(Value->Sort->getElementSort())) {
    const CamadaTupleArrayExpr *AE = toCamadaTupleArrayExpr(Value);
    fatalErrorIf(AE == nullptr,
                 "Tuple-array-sorted expression is not a Camada bundle");
    Out.insert(Out.end(), AE->LeafArrays.begin(), AE->LeafArrays.end());
    return;
  }
  Out.push_back(Value);
}

/// Rebuild a value of the given sort from leaf expressions (consumed in
/// order) — the inverse of collectLeafExprsOf.
SMTExprRef assembleFromLeaves(SMTSolverImpl &Solver, const SMTSortRef &Sort,
                              const std::vector<SMTExprRef> &Leaves,
                              std::size_t &Pos) {
  if (Sort->isTupleSort()) {
    std::vector<SMTExprRef> Fields;
    const auto &ElemSorts = Sort->getTupleElementSorts();
    Fields.reserve(ElemSorts.size());
    for (const auto &Elem : ElemSorts)
      Fields.push_back(assembleFromLeaves(Solver, Elem, Leaves, Pos));
    return Solver.mkTuple(Fields);
  }
  if (Sort->isArraySort() && sortContainsTuple(Sort->getElementSort())) {
    std::vector<SMTSortRef> SubLeafSorts;
    collectLeafSortsOf(Solver, Sort, SubLeafSorts);
    std::vector<SMTExprRef> SubLeaves;
    SubLeaves.reserve(SubLeafSorts.size());
    for (std::size_t I = 0; I < SubLeafSorts.size(); ++I) {
      fatalErrorIf(Pos >= Leaves.size(), "Tuple-array leaf underflow");
      SubLeaves.push_back(Leaves[Pos++]);
    }
    return Solver.makeExprRef<CamadaTupleArrayExpr>(SMTExprKind::ArrayConst,
                                                    Sort->getBackendKind(),
                                                    Sort, std::move(SubLeaves));
  }
  fatalErrorIf(Pos >= Leaves.size(), "Tuple-array leaf underflow");
  return Leaves[Pos++];
}

} // namespace

SMTSortRef mkCamadaTupleSort(SMTSolverImpl &Solver,
                             const std::vector<SMTSortRef> &ElementSorts) {
  // Pick the backend kind from the first element when available; for
  // empty tuples, the bool sort gives us the same backend kind without
  // needing a dedicated solver-level accessor.
  SMTBackendKind BackendKind = ElementSorts.empty()
                                   ? Solver.mkBoolSort()->getBackendKind()
                                   : ElementSorts.front()->getBackendKind();
  return Solver.makeSortRef(CamadaTupleSort(BackendKind, ElementSorts));
}

SMTExprRef mkCamadaTupleSymbol(SMTSolverImpl &Solver, const std::string &Name,
                               const SMTSortRef &Sort) {
  fatalErrorIf(!Sort->isTupleSort(),
               "mkCamadaTupleSymbol called on non-tuple sort");
  return Solver.makeExprRef<CamadaTupleExpr>(
      SMTExprKind::Symbol, Sort->getBackendKind(), Sort, Name);
}

SMTExprRef mkCamadaTuple(SMTSolverImpl &Solver,
                         const std::vector<SMTExprRef> &Elements) {
  std::vector<SMTSortRef> ElementSorts;
  ElementSorts.reserve(Elements.size());
  for (const auto &E : Elements)
    ElementSorts.push_back(E->Sort);
  SMTSortRef Sort = Solver.mkTupleSort(ElementSorts);
  return Solver.makeExprRef<CamadaTupleExpr>(
      SMTExprKind::TupleConst, Sort->getBackendKind(), Sort, Elements);
}

SMTExprRef mkCamadaTupleSelect(SMTSolverImpl &Solver, const SMTExprRef &Tuple,
                               unsigned Index) {
  const CamadaTupleExpr *TE = toCamadaTupleExpr(Tuple);
  fatalErrorIf(TE == nullptr,
               "mkCamadaTupleSelect on non-Camada-tuple expression");
  fatalErrorIf(Index >= Tuple->Sort->getTupleElementSorts().size(),
               "Tuple field index out of bounds");

  const SMTSortRef &FieldSort = Tuple->Sort->getTupleElementSorts()[Index];
  switch (TE->getKind()) {
  case SMTExprKind::Symbol: {
    // Synthesize a per-field symbol on demand. The reserved __CAMADA_tup_
    // name space prevents collisions with user-supplied symbol names.
    std::string FieldName =
        "__CAMADA_tup_" + TE->SymbolName + "_" + std::to_string(Index);
    return Solver.mkSymbolUnchecked(FieldName, FieldSort);
  }
  case SMTExprKind::TupleConst:
    return TE->Elements[Index];
  case SMTExprKind::Ite:
    return Solver.mkIte(TE->Cond,
                        mkCamadaTupleSelect(Solver, TE->TrueTuple, Index),
                        mkCamadaTupleSelect(Solver, TE->FalseTuple, Index));
  default:
    fatalError("Invalid CamadaTupleExpr SMTExprKind");
  }
}

SMTExprRef mkCamadaTupleEqual(SMTSolverImpl &Solver, const SMTExprRef &LHS,
                              const SMTExprRef &RHS) {
  fatalErrorIf(!LHS->Sort->isTupleSort() || !RHS->Sort->isTupleSort(),
               "mkCamadaTupleEqual on non-tuple operands");
  fatalErrorIf(LHS->Sort != RHS->Sort,
               "mkCamadaTupleEqual on tuples of different sorts");
  const auto &Fields = LHS->Sort->getTupleElementSorts();
  if (Fields.empty())
    return Solver.mkBool(true);
  SMTExprRef Acc = Solver.mkEqual(mkCamadaTupleSelect(Solver, LHS, 0),
                                  mkCamadaTupleSelect(Solver, RHS, 0));
  for (unsigned I = 1; I < Fields.size(); ++I)
    Acc =
        Solver.mkAnd(Acc, Solver.mkEqual(mkCamadaTupleSelect(Solver, LHS, I),
                                         mkCamadaTupleSelect(Solver, RHS, I)));
  return Acc;
}

SMTExprRef mkCamadaTupleIte(SMTSolverImpl &Solver, const SMTExprRef &Cond,
                            const SMTExprRef &T, const SMTExprRef &F) {
  fatalErrorIf(!T->Sort->isTupleSort() || !F->Sort->isTupleSort(),
               "mkCamadaTupleIte on non-tuple branches");
  return Solver.makeExprRef<CamadaTupleExpr>(
      SMTExprKind::Ite, T->getBackendKind(), T->Sort, Cond, T, F);
}

bool sortContainsTuple(const SMTSortRef &Sort) {
  if (Sort->isTupleSort())
    return true;
  if (Sort->isArraySort())
    return sortContainsTuple(Sort->getElementSort());
  return false;
}

SMTSortRef mkCamadaTupleArraySort(SMTSolverImpl &Solver,
                                  const SMTSortRef &IndexSort,
                                  const SMTSortRef &ElemSort) {
  fatalErrorIf(!sortContainsTuple(ElemSort),
               "mkCamadaTupleArraySort on a tuple-free element sort");
  std::vector<SMTSortRef> LeafSorts;
  collectLeafSortsOf(Solver, ElemSort, LeafSorts);
  for (auto &Leaf : LeafSorts)
    Leaf = Solver.mkArraySort(IndexSort, Leaf);
  return Solver.makeSortRef(CamadaTupleArraySort(
      IndexSort->getBackendKind(), IndexSort, ElemSort, std::move(LeafSorts)));
}

SMTExprRef mkCamadaTupleArraySymbol(SMTSolverImpl &Solver,
                                    const std::string &Name,
                                    const SMTSortRef &Sort) {
  const std::vector<SMTSortRef> &LeafSorts = leafSortsOf(Sort);
  std::vector<SMTExprRef> Leaves;
  Leaves.reserve(LeafSorts.size());
  for (std::size_t I = 0; I < LeafSorts.size(); ++I)
    Leaves.push_back(Solver.mkSymbolUnchecked(
        "__CAMADA_tuparr_" + Name + "_" + std::to_string(I), LeafSorts[I]));
  return Solver.makeExprRef<CamadaTupleArrayExpr>(
      SMTExprKind::Symbol, Sort->getBackendKind(), Sort, std::move(Leaves));
}

SMTExprRef mkCamadaTupleArraySelect(SMTSolverImpl &Solver,
                                    const SMTExprRef &Array,
                                    const SMTExprRef &Index) {
  const CamadaTupleArrayExpr *AE = toCamadaTupleArrayExpr(Array);
  fatalErrorIf(AE == nullptr,
               "mkCamadaTupleArraySelect on a non-bundle expression");
  std::vector<SMTExprRef> SelectedLeaves;
  SelectedLeaves.reserve(AE->LeafArrays.size());
  for (const auto &Leaf : AE->LeafArrays)
    SelectedLeaves.push_back(Solver.mkArraySelect(Leaf, Index));
  std::size_t Pos = 0;
  SMTExprRef Element = assembleFromLeaves(Solver, Array->Sort->getElementSort(),
                                          SelectedLeaves, Pos);
  fatalErrorIf(Pos != SelectedLeaves.size(), "Tuple-array leaf overflow");
  return Element;
}

SMTExprRef mkCamadaTupleArrayStore(SMTSolverImpl &Solver,
                                   const SMTExprRef &Array,
                                   const SMTExprRef &Index,
                                   const SMTExprRef &Element) {
  const CamadaTupleArrayExpr *AE = toCamadaTupleArrayExpr(Array);
  fatalErrorIf(AE == nullptr,
               "mkCamadaTupleArrayStore on a non-bundle expression");
  std::vector<SMTExprRef> ElementLeaves;
  collectLeafExprsOf(Solver, Element, ElementLeaves);
  fatalErrorIf(ElementLeaves.size() != AE->LeafArrays.size(),
               "Tuple-array store leaf count mismatch");
  std::vector<SMTExprRef> StoredLeaves;
  StoredLeaves.reserve(AE->LeafArrays.size());
  for (std::size_t I = 0; I < AE->LeafArrays.size(); ++I)
    StoredLeaves.push_back(
        Solver.mkArrayStore(AE->LeafArrays[I], Index, ElementLeaves[I]));
  return Solver.makeExprRef<CamadaTupleArrayExpr>(
      SMTExprKind::ArrayStore, Array->getBackendKind(), Array->Sort,
      std::move(StoredLeaves));
}

SMTExprRef mkCamadaTupleArrayConst(SMTSolverImpl &Solver,
                                   const SMTSortRef &IndexSort,
                                   const SMTExprRef &InitValue,
                                   ConstArrayLowering Lowering) {
  fatalErrorIf(!sortContainsTuple(InitValue->Sort),
               "mkCamadaTupleArrayConst on a tuple-free initializer");
  SMTSortRef Sort = Solver.mkArraySort(IndexSort, InitValue->Sort);
  std::vector<SMTExprRef> InitLeaves;
  collectLeafExprsOf(Solver, InitValue, InitLeaves);
  std::vector<SMTExprRef> Leaves;
  Leaves.reserve(InitLeaves.size());
  for (const auto &Init : InitLeaves)
    Leaves.push_back(Solver.mkArrayConst(IndexSort, Init, Lowering));
  return Solver.makeExprRef<CamadaTupleArrayExpr>(
      SMTExprKind::ArrayConst, Sort->getBackendKind(), Sort, std::move(Leaves));
}

SMTExprRef mkCamadaTupleArrayEqual(SMTSolverImpl &Solver, const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  const CamadaTupleArrayExpr *LE = toCamadaTupleArrayExpr(LHS);
  const CamadaTupleArrayExpr *RE = toCamadaTupleArrayExpr(RHS);
  fatalErrorIf(LE == nullptr || RE == nullptr,
               "mkCamadaTupleArrayEqual on a non-bundle expression");
  fatalErrorIf(LE->LeafArrays.size() != RE->LeafArrays.size(),
               "Tuple-array equality leaf count mismatch");
  if (LE->LeafArrays.empty())
    return Solver.mkBool(true);
  SMTExprRef Acc = Solver.mkEqual(LE->LeafArrays[0], RE->LeafArrays[0]);
  for (std::size_t I = 1; I < LE->LeafArrays.size(); ++I)
    Acc =
        Solver.mkAnd(Acc, Solver.mkEqual(LE->LeafArrays[I], RE->LeafArrays[I]));
  return Acc;
}

SMTExprRef mkCamadaTupleArrayIte(SMTSolverImpl &Solver, const SMTExprRef &Cond,
                                 const SMTExprRef &T, const SMTExprRef &F) {
  const CamadaTupleArrayExpr *TE = toCamadaTupleArrayExpr(T);
  const CamadaTupleArrayExpr *FE = toCamadaTupleArrayExpr(F);
  fatalErrorIf(TE == nullptr || FE == nullptr,
               "mkCamadaTupleArrayIte on a non-bundle expression");
  fatalErrorIf(TE->LeafArrays.size() != FE->LeafArrays.size(),
               "Tuple-array ite leaf count mismatch");
  std::vector<SMTExprRef> Leaves;
  Leaves.reserve(TE->LeafArrays.size());
  for (std::size_t I = 0; I < TE->LeafArrays.size(); ++I)
    Leaves.push_back(Solver.mkIte(Cond, TE->LeafArrays[I], FE->LeafArrays[I]));
  return Solver.makeExprRef<CamadaTupleArrayExpr>(
      SMTExprKind::Ite, T->getBackendKind(), T->Sort, std::move(Leaves));
}

} // namespace camada
