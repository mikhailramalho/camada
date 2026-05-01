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

} // namespace camada
