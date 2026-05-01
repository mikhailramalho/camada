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

/// Tuple expression owned by the Camada layer. One of three node kinds:
///   - Symbol: lazy — per-field symbols are minted on demand by mkTupleSelect
///   - Value: eager — components are stored verbatim
///   - Ite: lazy — distributes over fields when selected
class CamadaTupleExpr : public SMTExpr {
public:
  enum class NodeKind { Symbol, Value, Ite };

  // Symbol form
  CamadaTupleExpr(SMTBackendKind BackendKind, const SMTSortRef &Sort,
                  std::string SymbolName)
      : SMTExpr(SMTExprKind::Symbol, Sort), Kind(NodeKind::Symbol),
        SymbolName(std::move(SymbolName)), BackendKind(BackendKind) {}

  // Value form
  CamadaTupleExpr(SMTBackendKind BackendKind, const SMTSortRef &Sort,
                  std::vector<SMTExprRef> Elements)
      : SMTExpr(SMTExprKind::TupleConst, Sort), Kind(NodeKind::Value),
        Elements(std::move(Elements)), BackendKind(BackendKind) {}

  // Ite form
  CamadaTupleExpr(SMTBackendKind BackendKind, const SMTSortRef &Sort,
                  SMTExprRef Cond, SMTExprRef T, SMTExprRef F)
      : SMTExpr(SMTExprKind::Ite, Sort), Kind(NodeKind::Ite),
        Cond(std::move(Cond)), TrueTuple(std::move(T)),
        FalseTuple(std::move(F)), BackendKind(BackendKind) {}

  SMTBackendKind getBackendKind() const override { return BackendKind; }

  void dump(std::string &Out) const override {
    switch (Kind) {
    case NodeKind::Symbol:
      Out = "(CamadaTupleSymbol " + SymbolName + ")\n";
      return;
    case NodeKind::Value: {
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
    case NodeKind::Ite:
      Out = "(CamadaTupleIte ...)\n";
      return;
    }
    fatalError("Invalid CamadaTupleExpr NodeKind");
  }

  NodeKind Kind;
  std::string SymbolName;
  std::vector<SMTExprRef> Elements;
  SMTExprRef Cond;
  SMTExprRef TrueTuple;
  SMTExprRef FalseTuple;

protected:
  // Camada-managed tuple expressions have no shared backend identity; two
  // freshly built nodes are equal iff they are the same object. Semantic
  // equality must go through mkCamadaTupleEqual.
  bool equal_to(SMTExpr const &Other) const override { return this == &Other; }

private:
  SMTBackendKind BackendKind;
};

const CamadaTupleExpr *toCamadaTupleExpr(const SMTExprRef &Exp) {
  if (!Exp || !Exp->Sort->isTupleSort())
    return nullptr;
  return dynamic_cast<const CamadaTupleExpr *>(Exp.get());
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
  return Solver.makeCamadaSortRef<CamadaTupleSort>(BackendKind, ElementSorts);
}

SMTExprRef mkCamadaTupleSymbol(SMTSolverImpl &Solver, const std::string &Name,
                               const SMTSortRef &Sort) {
  fatalErrorIf(!Sort->isTupleSort(),
               "mkCamadaTupleSymbol called on non-tuple sort");
  return Solver.makeCamadaExprRef<CamadaTupleExpr>(Sort->getBackendKind(), Sort,
                                                   Name);
}

SMTExprRef mkCamadaTuple(SMTSolverImpl &Solver,
                         const std::vector<SMTExprRef> &Elements) {
  std::vector<SMTSortRef> ElementSorts;
  ElementSorts.reserve(Elements.size());
  for (const auto &E : Elements)
    ElementSorts.push_back(E->Sort);
  SMTSortRef Sort = Solver.mkTupleSort(ElementSorts);
  return Solver.makeCamadaExprRef<CamadaTupleExpr>(Sort->getBackendKind(), Sort,
                                                   Elements);
}

SMTExprRef mkCamadaTupleSelect(SMTSolverImpl &Solver, const SMTExprRef &Tuple,
                               unsigned Index) {
  const CamadaTupleExpr *TE = toCamadaTupleExpr(Tuple);
  fatalErrorIf(TE == nullptr,
               "mkCamadaTupleSelect on non-Camada-tuple expression");
  fatalErrorIf(Index >= Tuple->Sort->getTupleElementSorts().size(),
               "Tuple field index out of bounds");

  const SMTSortRef &FieldSort = Tuple->Sort->getTupleElementSorts()[Index];
  switch (TE->Kind) {
  case CamadaTupleExpr::NodeKind::Symbol: {
    // Synthesize a per-field symbol on demand. The reserved __CAMADA_tup_
    // name space prevents collisions with user-supplied symbol names.
    std::string FieldName =
        "__CAMADA_tup_" + TE->SymbolName + "_" + std::to_string(Index);
    return Solver.mkSymbolUnchecked(FieldName, FieldSort);
  }
  case CamadaTupleExpr::NodeKind::Value:
    return TE->Elements[Index];
  case CamadaTupleExpr::NodeKind::Ite:
    return Solver.mkIte(TE->Cond,
                        mkCamadaTupleSelect(Solver, TE->TrueTuple, Index),
                        mkCamadaTupleSelect(Solver, TE->FalseTuple, Index));
  }
  fatalError("Invalid CamadaTupleExpr NodeKind");
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
  return Solver.makeCamadaExprRef<CamadaTupleExpr>(T->getBackendKind(), T->Sort,
                                                   Cond, T, F);
}

} // namespace camada
