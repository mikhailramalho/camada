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

#include "yicessolver.h"
#include "ac_config.h"

#include <cassert>
#include <iostream>

using namespace camada;

#ifdef SOLVER_YICES_ENABLED

void YicesSort::dump() const {
  char *ty_str = yices_type_to_string(Sort, 160, 80, 0);
  std::cerr << ty_str << '\n';
  yices_free_string(ty_str);
}

bool YicesExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
  return (Expr == dynamic_cast<const YicesExpr &>(Other).Expr);
}

void YicesExpr::dump() const {
  char *term_str = yices_term_to_string(Expr, 160, 80, 0);
  std::cerr << term_str << '\n';
  yices_free_string(term_str);
}

YicesSolver::YicesSolver() {
  yices_init();
  yices_clear_error();

  ctx_config_t *config = yices_new_config();
  yices_default_config_for_logic(config, "QF_AUFBV");

  Context = std::make_shared<context_t *>(yices_new_context(config));
  yices_free_config(config);
}

YicesSolver::~YicesSolver() {
  yices_exit();
  Context = nullptr;
}

void YicesSolver::addConstraint(const SMTExprRef &Exp) {
  Assertions.push_back(Exp);
  yices_assert_formula(*Context, toSolverExpr<YicesExpr>(*Exp).Expr);
}

SMTExprRef YicesSolver::newExprRef(const SMTExpr &Exp) const {
  assert(toSolverExpr<YicesExpr>(Exp).Expr != NULL_TERM &&
         "Error when creating Yices expr.");
  return std::make_shared<YicesExpr>(toSolverExpr<YicesExpr>(Exp));
}

SMTSortRef YicesSolver::mkBoolSort() {
  return newSortRef<SolverBoolSort<YicesSort>>({Context, yices_bool_type()});
}

SMTSortRef YicesSolver::mkBVSort(unsigned BitWidth) {
  return newSortRef<SolverBVSort<YicesSort>>(
      {BitWidth, Context, yices_bv_type(BitWidth)});
}

SMTSortRef YicesSolver::mkBVFPSort(const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  return newSortRef<SolverFPSort<YicesSort>>(
      {ExpWidth, SigWidth + 1, Context,
       yices_bv_type(ExpWidth + SigWidth + 1)});
}

SMTSortRef YicesSolver::mkBVRMSort() {
  return newSortRef<SolverRMSort<YicesSort>>({Context, yices_bv_type(3)});
}

SMTSortRef YicesSolver::mkArraySort(const SMTSortRef &IndexSort,
                                    const SMTSortRef &ElemSort) {
  return newSortRef<SolverArraySort<YicesSort>>(
      {IndexSort, ElemSort, Context,
       yices_function_type1(toSolverSort<YicesSort>(*IndexSort).Sort,
                            toSolverSort<YicesSort>(*ElemSort).Sort)});
}

SMTExprRef YicesSolver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, Exp->Sort,
                              yices_bvneg(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, Exp->Sort,
                              yices_bvnot(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, Exp->Sort,
                              yices_not(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvadd(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvsub(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvmul(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvsrem(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvrem(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvsdiv(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvdiv(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvshl(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvashr(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvlshr(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvxor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvand2(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvlt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvslt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                 toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvgt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvsgt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                 toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvle_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvsle_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                 toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvge_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvsge_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                 toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, mkBoolSort(),
                              yices_and2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                         toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, mkBoolSort(),
                              yices_or2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                        toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, mkBoolSort(),
                              yices_xor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                         toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, mkBoolSort(),
                              yices_eq(toSolverExpr<YicesExpr>(*LHS).Expr,
                                       toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                              const SMTExprRef &F) {
  return newExprRef(YicesExpr(Context, T->Sort,
                              yices_ite(toSolverExpr<YicesExpr>(*Cond).Expr,
                                        toSolverExpr<YicesExpr>(*T).Expr,
                                        toSolverExpr<YicesExpr>(*F).Expr)));
}

SMTExprRef YicesSolver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, mkBVSort(i + Exp->getWidth()),
                yices_sign_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i)));
}

SMTExprRef YicesSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, mkBVSort(i + Exp->getWidth()),
                yices_zero_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i)));
}

SMTExprRef YicesSolver::mkBVExtract(unsigned High, unsigned Low,
                                    const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(
      Context, mkBVSort(High - Low + 1),
      yices_bvextract(toSolverExpr<YicesExpr>(*Exp).Expr, Low, High)));
}

SMTExprRef YicesSolver::mkBVConcat(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
                yices_bvconcat2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArraySelect(const SMTExprRef &Array,
                                      const SMTExprRef &Index) {
  return newExprRef(
      YicesExpr(Context, Array->Sort->getElementSort(),
                yices_application1(toSolverExpr<YicesExpr>(*Array).Expr,
                                   toSolverExpr<YicesExpr>(*Index).Expr)));
}

SMTExprRef YicesSolver::mkArrayStore(const SMTExprRef &Array,
                                     const SMTExprRef &Index,
                                     const SMTExprRef &Element) {
  return newExprRef(
      YicesExpr(Context, Array->Sort,
                yices_update1(toSolverExpr<YicesExpr>(*Array).Expr,
                              toSolverExpr<YicesExpr>(*Index).Expr,
                              toSolverExpr<YicesExpr>(*Element).Expr)));
}

bool YicesSolver::getBool(const SMTExprRef &Exp) {
  int32_t val;
  auto res = yices_get_bool_value(yices_get_model(*Context, 1),
                                  toSolverExpr<YicesExpr>(*Exp).Expr, &val);
  (void)res;
  assert(res && "Can't get boolean value from Yices");
  return val ? true : false;
}

std::string YicesSolver::getBVInBin(const SMTExprRef &Exp) {
  unsigned width = Exp->getWidth();

  int32_t *data = new int32_t[width];
  yices_get_bv_value(yices_get_model(*Context, 1),
                     toSolverExpr<YicesExpr>(*Exp).Expr, data);

  std::string val;
  for (unsigned i = 0; i < width; i++)
    val.append(std::to_string(data[width - i - 1]));

  delete[] data;
  return val;
}

SMTExprRef YicesSolver::getArrayElement(const SMTExprRef &Array,
                                        const SMTExprRef &Index) {
  SMTExprRef sel = mkArraySelect(Array, Index);

  SMTSortRef elementSort = Array->Sort->getElementSort();
  if (elementSort->isBoolSort())
    return mkBool(getBool(sel));

  if (elementSort->isBVSort())
    return SMTFPSolver::mkBVFromBin(getBVInBin(sel));

  assert(elementSort->isFPSort() && "Unknown array element type");
  return SMTFPSolver::mkFPFromBin(getFPInBin(sel),
                                  elementSort->getFPExponentWidth());
}

SMTExprRef YicesSolver::mkBool(const bool b) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(), b ? yices_true() : yices_false()));
}

SMTExprRef YicesSolver::mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) {
  return newExprRef(
      YicesExpr(Context, Sort, yices_bvconst_int64(Sort->getWidth(), Int)));
}

SMTExprRef YicesSolver::mkBVFromBin(const std::string &Int,
                                    const SMTSortRef &Sort) {
  return newExprRef(YicesExpr(Context, Sort, yices_parse_bvbin(Int.c_str())));
}

SMTExprRef YicesSolver::mkSymbol(const std::string &Name, SMTSortRef Sort) {
  // We could use yices_get_term_by_name to check if the variable was already
  // created, but the we would need to create a new SMTExprRef, so use
  // this map instead
  auto it = SymbolTable.find(Name);
  if (it != SymbolTable.end())
    return it->second;

  assert(yices_get_term_by_name(Name.c_str()) == NULL_TERM &&
         "Trying to create a symbol but it already exists");

  term_t t = yices_new_uninterpreted_term(toSolverSort<YicesSort>(*Sort).Sort);
  assert(t != NULL_TERM && "Error when trying to create new a symbol");

  assert(yices_set_term_name(t, Name.c_str()) != -1 &&
         "Error when trying to set symbol name");

  auto inserted = SymbolTable.insert(
      SymbolTablet::value_type(Name, newExprRef(YicesExpr(Context, Sort, t))));

  assert(inserted.second && "Could not cache new Yices variable");
  return inserted.first->second;
}

SMTExprRef YicesSolver::mkArrayConst(const SMTSortRef &IndexSort,
                                     const SMTExprRef &InitValue) {
  const std::string name = "__CAMADA_arr" + std::to_string(ConstArrayCounter++);
  SMTExprRef arr = mkSymbol(name, mkArraySort(IndexSort, InitValue->Sort));

  uint64_t size = 1ULL << IndexSort->getWidth();
  for (uint64_t i = 0; i < size; i++)
    arr = mkArrayStore(arr, mkBVFromDec(i, IndexSort), InitValue);

  return arr;
}

checkResult YicesSolver::check() {
  smt_status_t res = yices_check_context(*Context, nullptr);
  if (res == STATUS_SAT)
    return checkResult::SAT;

  if (res == STATUS_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void YicesSolver::reset() {
  SymbolTable.clear();
  Assertions.clear();

  // Delete
  yices_exit();

  // and recreate
  yices_init();
  yices_clear_error();

  ctx_config_t *config = yices_new_config();
  yices_default_config_for_logic(config, "QF_AUFBV");

  Context = std::make_shared<context_t *>(yices_new_context(config));
  yices_free_config(config);
}

void YicesSolver::dump() {
  for (auto const &a : Assertions)
    a->dump();
}

void YicesSolver::dumpModel() {
  char *model_str =
      yices_model_to_string(yices_get_model(*Context, 1), 160, 80, 0);
  std::cerr << model_str << '\n';
  yices_free_string(model_str);
}

#endif
