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

#if SOLVER_BOOLECTOR_ENABLED

#include "boolectorsolver.h"

#include <cassert>

namespace camada {

unsigned BtorSort::getWidthFromSolver() const {
  return boolector_bitvec_sort_get_width(*Context, Sort);
}

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
void BtorErrorHandler(const char *msg) {
  (void)msg;
  assert(0 && msg);
}

BtorSolver::BtorSolver()
    : SMTSolverImpl(), Context(std::make_shared<Btor *>(boolector_new())) {
  boolector_set_abort(BtorErrorHandler);
  boolector_set_opt(*Context, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt(*Context, BTOR_OPT_AUTO_CLEANUP, 1);
}

BtorSolver::~BtorSolver() {
  boolector_release_all(*Context);
  boolector_delete(*Context);
  Context = nullptr;
}

void BtorSolver::addConstraintImpl(const SMTExprRef &Exp) {
  boolector_assert(*Context, toSolverExpr<BtorExpr>(*Exp).Expr);
}

SMTExprRef BtorSolver::newExprRefImpl(const SMTExpr &Exp) const {
  return std::make_shared<BtorExpr>(toSolverExpr<BtorExpr>(Exp));
}

SMTSortRef BtorSolver::mkBoolSortImpl() {
  return newSortRef<SolverBoolSort<BtorSort>>(
      {Context, boolector_bool_sort(*Context)});
}

SMTSortRef BtorSolver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<SolverBVSort<BtorSort>>(
      {BitWidth, Context, boolector_bitvec_sort(*Context, BitWidth)});
}

SMTSortRef BtorSolver::mkBVFPSortImpl(const unsigned ExpWidth,
                                      const unsigned SigWidth) {
  return newSortRef<SolverBVFPSort<BtorSort>>(
      {ExpWidth, SigWidth + 1, Context,
       boolector_bitvec_sort(*Context, ExpWidth + SigWidth + 1)});
}

SMTSortRef BtorSolver::mkBVRMSortImpl() {
  return newSortRef<SolverBVRMSort<BtorSort>>(
      {Context, boolector_bitvec_sort(*Context, 3)});
}

SMTSortRef BtorSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                       const SMTSortRef &ElemSort) {
  return newSortRef<SolverArraySort<BtorSort>>(
      {IndexSort, ElemSort, Context,
       boolector_array_sort(*Context, toSolverSort<BtorSort>(*IndexSort).Sort,
                            toSolverSort<BtorSort>(*ElemSort).Sort)});
}

SMTExprRef BtorSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, Exp->Sort,
               boolector_neg(*Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, Exp->Sort,
               boolector_not(*Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkNotImpl(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, Exp->Sort,
               boolector_not(*Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_add(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sub(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_mul(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_srem(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_urem(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sdiv(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_udiv(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sll(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_sra(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_srl(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_xor(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVOrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_or(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_and(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_ult(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_slt(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUgtImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_ugt(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSgtImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_sgt(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_ulte(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_slte(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUgeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_ugte(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSgeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_sgte(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                              toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_and(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_or(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_xor(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                             toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkEqualImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               boolector_eq(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                 const SMTExprRef &F) {
  return newExprRef(
      BtorExpr(Context, T->Sort,
               boolector_cond(*Context, toSolverExpr<BtorExpr>(*Cond).Expr,
                              toSolverExpr<BtorExpr>(*T).Expr,
                              toSolverExpr<BtorExpr>(*F).Expr)));
}

SMTExprRef BtorSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, mkBVSort(i + Exp->getWidth()),
               boolector_sext(*Context, toSolverExpr<BtorExpr>(*Exp).Expr, i)));
}

SMTExprRef BtorSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, mkBVSort(i + Exp->getWidth()),
               boolector_uext(*Context, toSolverExpr<BtorExpr>(*Exp).Expr, i)));
}

SMTExprRef BtorSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                       const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, mkBVSort(High - Low + 1),
      boolector_slice(*Context, toSolverExpr<BtorExpr>(*Exp).Expr, High, Low)));
}

SMTExprRef BtorSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
               boolector_concat(*Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                                toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVRedOrImpl(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, mkBVSort(1),
               boolector_redor(*Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkBVRedAndImpl(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, mkBVSort(1),
               boolector_redand(*Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index) {
  return newExprRef(
      BtorExpr(Context, Array->Sort->getElementSort(),
               boolector_read(*Context, toSolverExpr<BtorExpr>(*Array).Expr,
                              toSolverExpr<BtorExpr>(*Index).Expr)));
}

SMTExprRef BtorSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                        const SMTExprRef &Index,
                                        const SMTExprRef &Element) {
  return newExprRef(
      BtorExpr(Context, Array->Sort,
               boolector_write(*Context, toSolverExpr<BtorExpr>(*Array).Expr,
                               toSolverExpr<BtorExpr>(*Index).Expr,
                               toSolverExpr<BtorExpr>(*Element).Expr)));
}

bool BtorSolver::getBoolImpl(const SMTExprRef &Exp) {
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

std::string BtorSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  return boolector_bv_assignment(*Context, toSolverExpr<BtorExpr>(*Exp).Expr);
}

SMTExprRef BtorSolver::getArrayElementImpl(const SMTExprRef &Array,
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
    return SMTSolverImpl::mkBVFromBin(bv);

  if (elementSort->isBoolSort()) {
    char *foo;
    return mkBool(strtol(bv.c_str(), &foo, 2));
  }

  assert(elementSort->isFPSort() && "Unknown array element type");
  return SMTSolverImpl::mkFPFromBin(bv, elementSort->getFPExponentWidth());
}

SMTExprRef BtorSolver::mkBoolImpl(const bool b) {
  return newExprRef(
      BtorExpr(Context, mkBoolSort(),
               b ? boolector_true(*Context) : boolector_false(*Context)));
}

SMTExprRef BtorSolver::mkBVFromDecImpl(const int64_t Int,
                                       const SMTSortRef &Sort) {
  // Prevent creating a bitvector with size greater than the bitwidth
  uint64_t newInt =
      static_cast<uint64_t>(Int) & ((1ULL << Sort->getWidth()) - 1);

  return newExprRef(
      BtorExpr(Context, Sort,
               boolector_constd(*Context, toSolverSort<BtorSort>(*Sort).Sort,
                                std::to_string(newInt).c_str())));
}

SMTExprRef BtorSolver::mkBVFromBinImpl(const std::string &Int,
                                       const SMTSortRef &Sort) {
  return newExprRef(
      BtorExpr(Context, Sort, boolector_const(*Context, Int.c_str())));
}

SMTExprRef BtorSolver::mkSymbolImpl(const std::string &Name,
                                    const SMTSortRef &Sort) {
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

SMTExprRef BtorSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                        const SMTExprRef &InitValue) {
  SMTSortRef sort = mkArraySort(IndexSort, InitValue->Sort);
  return newExprRef(BtorExpr(
      Context, sort,
      boolector_const_array(*Context, toSolverSort<BtorSort>(*sort).Sort,
                            toSolverExpr<BtorExpr>(*InitValue).Expr)));
}

checkResult BtorSolver::checkImpl() {
  int res = boolector_sat(*Context);
  if (res == BOOLECTOR_SAT)
    return checkResult::SAT;

  if (res == BOOLECTOR_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void BtorSolver::resetImpl() {
  SymbolTable.clear();

  // Delete
  boolector_release_all(*Context);
  boolector_delete(*Context);

  // Create new
  Context = std::make_shared<Btor *>(boolector_new());
  boolector_set_abort(BtorErrorHandler);
  boolector_set_opt(*Context, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt(*Context, BTOR_OPT_AUTO_CLEANUP, 1);
}

std::string BtorSolver::getSolverNameAndVersion() const {
  return std::string("Boolector v").append(boolector_version(*Context));
}

void BtorSolver::dumpImpl() { boolector_dump_smt2(*Context, stderr); }

void BtorSolver::dumpModelImpl() {
  boolector_print_model(*Context, const_cast<char *>("smt2"), stderr);
}

} // namespace camada

#endif
