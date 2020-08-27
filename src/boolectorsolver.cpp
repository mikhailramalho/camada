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

#include "boolectorsolver.h"
#include "ac_config.h"

#include <cassert>

using namespace camada;

#ifdef SOLVER_BOOLECTOR_ENABLED

bool BtorExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
  return (boolector_get_node_id(*Context, Expr) ==
          boolector_get_node_id(*Context,
                                dynamic_cast<const BtorExpr &>(Other).Expr));
}

void BtorExpr::dump() const {
  boolector_dump_smt2_node(*Context, stderr, Expr);
}

// Function used to report errors
void BtorErrorHandler(const char *msg) { assert(0 && msg); }

BtorSolver::BtorSolver() : Context(std::make_shared<Btor *>(boolector_new())) {
  boolector_set_abort(BtorErrorHandler);
  boolector_set_opt(*Context, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt(*Context, BTOR_OPT_AUTO_CLEANUP, 1);
}

BtorSolver::~BtorSolver() {
  boolector_release_all(*Context);
  boolector_delete(*Context);
  Context = nullptr;
}

void BtorSolver::addConstraint(const SMTExprRef &Exp) {
  boolector_assert(*Context, toSolverExpr<BtorExpr>(*Exp).Expr);
}

SMTExprRef BtorSolver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<BtorExpr>(toSolverExpr<BtorExpr>(Exp));
}

SMTSortRef BtorSolver::mkBoolSort() {
  return newSortRef<SolverBoolSort<BtorSort>>(
      {Context, boolector_bool_sort(*Context)});
}

SMTSortRef BtorSolver::mkBVSort(unsigned BitWidth) {
  return newSortRef<SolverBVSort<BtorSort>>(
      {BitWidth, Context, boolector_bitvec_sort(*Context, BitWidth)});
}

SMTSortRef BtorSolver::mkBVFPSort(const unsigned ExpWidth,
                                   const unsigned SigWidth) {
  return newSortRef<SolverFPSort<BtorSort>>(
      {ExpWidth, SigWidth + 1, Context,
       boolector_bitvec_sort(*Context, ExpWidth + SigWidth + 1)});
}

SMTSortRef BtorSolver::mkBVRMSort() {
  return newSortRef<SolverRMSort<BtorSort>>(
      {Context, boolector_bitvec_sort(*Context, 3)});
}

SMTSortRef BtorSolver::mkArraySort(const SMTSortRef &IndexSort,
                                   const SMTSortRef &ElemSort) {
  return newSortRef<SolverArraySort<BtorSort>>(
      {IndexSort, ElemSort, Context,
       boolector_array_sort(*Context, toSolverSort<BtorSort>(*IndexSort).Sort,
                            toSolverSort<BtorSort>(*ElemSort).Sort)});
}

SMTExprRef BtorSolver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, Exp->Sort,
               boolector_neg(*Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, Exp->Sort,
               boolector_not(*Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, Exp->Sort,
               boolector_not(*Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_add(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sub(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_mul(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_srem(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_urem(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sdiv(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_udiv(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sll(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sra(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_srl(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_xor(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_or(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_and(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_ult(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_slt(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_ugt(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sgt(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_ulte(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_slte(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_ugte(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sgte(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_and(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_or(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_xor(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_eq(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                             const SMTExprRef &F) {
  return newExprRef(
      BtorExpr(Context, T->Sort,
               boolector_cond(*Context, toSolverExpr<BtorExpr>(*Cond).Expr,
                              toSolverExpr<BtorExpr>(*T).Expr,
                              toSolverExpr<BtorExpr>(*F).Expr)));
}

SMTExprRef BtorSolver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, mkBVSort(i + Exp->getWidth()),
               boolector_sext(*Context, toSolverExpr<BtorExpr>(*Exp).Expr, i)));
}

SMTExprRef BtorSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, mkBVSort(i + Exp->getWidth()),
               boolector_uext(*Context, toSolverExpr<BtorExpr>(*Exp).Expr, i)));
}

SMTExprRef BtorSolver::mkBVExtract(unsigned High, unsigned Low,
                                   const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, mkBVSort(High - Low + 1),
      boolector_slice(*Context, toSolverExpr<BtorExpr>(*Exp).Expr, High, Low)));
}

SMTExprRef BtorSolver::mkBVConcat(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
               boolector_concat(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                                toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkArraySelect(const SMTExprRef &Array,
                                     const SMTExprRef &Index) {
  return newExprRef(
      BtorExpr(Context, Array->Sort->getElementSort(),
               boolector_read(*Context, toSolverExpr<BtorExpr>(*Array).Expr,
                              toSolverExpr<BtorExpr>(*Index).Expr)));
}

SMTExprRef BtorSolver::mkArrayStore(const SMTExprRef &Array,
                                    const SMTExprRef &Index,
                                    const SMTExprRef &Element) {
  return newExprRef(
      BtorExpr(Context, Array->Sort,
               boolector_write(*Context, toSolverExpr<BtorExpr>(*Array).Expr,
                               toSolverExpr<BtorExpr>(*Index).Expr,
                               toSolverExpr<BtorExpr>(*Element).Expr)));
}

bool BtorSolver::getBool(const SMTExprRef &Exp) {
  const char *boolean =
      boolector_bv_assignment(*Context, toSolverExpr<BtorExpr>(*Exp).Expr);

  assert(boolean != nullptr && "Boolector returned null bv assignment string");
  bool res;
  switch (*boolean) {
  case '1':
    res = true;
    break;
  case '0':
    res = false;
    break;
  default:
    assert(0 && "Bool is neither true nor false");
    __builtin_unreachable();
  }

  boolector_free_bv_assignment(*Context, boolean);
  return res;
}

std::string BtorSolver::getBVInBin(const SMTExprRef &Exp) {
  return boolector_bv_assignment(*Context, toSolverExpr<BtorExpr>(*Exp).Expr);
}

SMTExprRef BtorSolver::getArrayElement(const SMTExprRef &Array,
                                       const SMTExprRef &Index) {
  // Boolector is weird here, it returns the elements and binary strings
  // so we need to parse the array and create the appropriate Expr
  uint32_t size;
  char **indicies, **values;
  boolector_array_assignment(*Context, toSolverExpr<BtorExpr>(*Array).Expr,
                             &indicies, &values, &size);

  std::string bv;
  if (size > 0) {
    // Index we are looking for
    auto const index = getBV(Index);

    // Iterate over all elements in the array
    for (uint32_t i = 0; i < size; i++) {
      char *foo;
      if (strtoll(indicies[i], &foo, 2) == index) {
        bv = values[i];
        break;
      }
    }
  }
  boolector_free_array_assignment(*Context, indicies, values, size);

  // Simply return zero if we couldn't get a value from boolector
  if (bv.empty())
    return mkBVFromDec(0, Array->Sort->getElementSort());

  SMTSortRef elementSort = Array->Sort->getElementSort();
  if (elementSort->isBVSort())
    return SMTFPSolver::mkBVFromBin(bv);

  if (elementSort->isBoolSort()) {
    char *foo;
    return mkBool(strtol(bv.c_str(), &foo, 2));
  }

  assert(elementSort->isFPSort() && "Unknown array element type");
  return SMTFPSolver::mkFPFromBin(bv, elementSort->getFPExponentWidth());
}

SMTExprRef BtorSolver::mkBool(const bool b) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               b ? boolector_true(*Context) : boolector_false(*Context)));
}

SMTExprRef BtorSolver::mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) {
  // Prevent creating a bitvector with size greater than the bitwidth
  uint64_t newInt =
      static_cast<uint64_t>(Int) & ((1ULL << Sort->getWidth()) - 1);

  return newExprRef(
      BtorExpr(Context, Sort,
               boolector_constd(*Context, toSolverSort<BtorSort>(*Sort).Sort,
                                std::to_string(newInt).c_str())));
}

SMTExprRef BtorSolver::mkBVFromBin(const std::string &Int,
                                   const SMTSortRef &Sort) {
  return newExprRef(
      BtorExpr(Context, Sort, boolector_const(*Context, Int.c_str())));
}

SMTExprRef BtorSolver::mkSymbol(const std::string &Name, SMTSortRef Sort) {
  auto it = SymbolTable.find(Name);
  if (it != SymbolTable.end())
    return it->second;

  SMTExprRef newSymbol =
      Sort->isArraySort()
          ? newExprRef(BtorExpr(
                Context, Sort,
                boolector_array(*Context, toSolverSort<BtorSort>(*Sort).Sort,
                                Name.c_str())))
          : newExprRef(BtorExpr(
                Context, Sort,
                boolector_var(*Context, toSolverSort<BtorSort>(*Sort).Sort,
                              Name.c_str())));

  auto inserted = SymbolTable.insert(SymbolTablet::value_type(Name, newSymbol));
  assert(inserted.second && "Could not cache new Boolector variable");

  return inserted.first->second;
}

SMTExprRef BtorSolver::mkArrayConst(const SMTSortRef &IndexSort,
                                    const SMTExprRef &InitValue) {
  SMTSortRef sort = mkArraySort(IndexSort, InitValue->Sort);
  return newExprRef(BtorExpr(
      Context, sort,
      boolector_const_array(*Context, toSolverSort<BtorSort>(*sort).Sort,
                            toSolverExpr<BtorExpr>(*InitValue).Expr)));
}

checkResult BtorSolver::check() {
  int res = boolector_sat(*Context);
  if (res == BOOLECTOR_SAT)
    return checkResult::SAT;

  if (res == BOOLECTOR_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void BtorSolver::reset() {
  // Delete
  boolector_release_all(*Context);
  boolector_delete(*Context);

  // Create new
  Context = std::make_shared<Btor *>(boolector_new());
  boolector_set_abort(BtorErrorHandler);
  boolector_set_opt(*Context, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt(*Context, BTOR_OPT_AUTO_CLEANUP, 1);
}

void BtorSolver::dump() { boolector_dump_smt2(*Context, stderr); }

void BtorSolver::dumpModel() {
  boolector_print_model(*Context, const_cast<char *>("smt2"), stderr);
}

#endif
