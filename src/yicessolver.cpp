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

#include <fmt/printf.h>

using namespace camada;

#ifdef SOLVER_YICES_ENABLED

YicesContext::YicesContext() : Context(nullptr) { createAndConfig(); }

YicesContext::~YicesContext() {
  yices_exit();
  Context = nullptr;
}

void YicesContext::createAndConfig() {
  yices_init();
  yices_clear_error();

  ctx_config_t *config = yices_new_config();
  yices_default_config_for_logic(config, "QF_AUFBV");

  Context = yices_new_context(config);
  yices_free_config(config);
}

void YicesContext::reset() {
  yices_reset();
  Context = nullptr;
  createAndConfig();
}

void YicesSort::dump() const {
  char *ty_str = yices_type_to_string(Sort, 160, 80, 0);
  fmt::print(stderr, "{}\n", ty_str);
  yices_free_string(ty_str);
}

bool YicesExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
  return (Expr == dynamic_cast<const YicesExpr &>(Other).Expr);
}

void YicesExpr::dump() const {
  char *term_str = yices_term_to_string(Expr, 160, 80, 0);
  fmt::print(stderr, "{}\n", term_str);
  yices_free_string(term_str);
}

YicesSolver::YicesSolver() : Context(std::make_shared<YicesContext>()) {}

YicesSolver::YicesSolver(YicesContextRef C) : Context(std::move(C)) {}

void YicesSolver::addConstraint(const SMTExprRef &Exp) {
  yices_assert_formula(Context->Context, toSolverExpr<YicesExpr>(*Exp).Expr);
}

SMTExprRef YicesSolver::newExprRef(const SMTExpr &Exp) const {
  abortCondWithMessage(toSolverExpr<YicesExpr>(Exp).Expr != NULL_TERM,
                       "Error when creating Yices expr.");
  return std::make_shared<YicesExpr>(toSolverExpr<YicesExpr>(Exp));
}

SMTSortRef YicesSolver::getBoolSort() {
  return newSortRef<camada::SolverBoolSort<YicesSort>>(
      camada::SolverBoolSort<YicesSort>(Context, yices_bool_type()));
}

SMTSortRef YicesSolver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef<camada::SolverBVSort<YicesSort>>(
      camada::SolverBVSort<YicesSort>(BitWidth, Context,
                                      yices_bv_type(BitWidth)));
}

SMTSortRef YicesSolver::getRoundingModeSort() {
  abortWithMessage("Yices does not support fp");
}

SMTSortRef YicesSolver::getFloatSort(const unsigned, const unsigned) {
  abortWithMessage("Yices does not support fp");
}

SMTSortRef YicesSolver::getBVRoundingModeSort() {
  return newSortRef<camada::SolverRMSort<YicesSort>>(
      camada::SolverRMSort<YicesSort>(Context, yices_bv_type(3)));
}

SMTSortRef YicesSolver::getBVFloatSort(const unsigned ExpWidth,
                                       const unsigned SigWidth) {
  return newSortRef<camada::SolverFPSort<YicesSort>>(
      camada::SolverFPSort<YicesSort>(ExpWidth, SigWidth + 1, Context,
                                      yices_bv_type(ExpWidth + SigWidth + 1)));
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
  return newExprRef(YicesExpr(Context, getBoolSort(),
                              yices_and2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                         toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, getBoolSort(),
                              yices_or2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                        toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, getBoolSort(),
                              yices_xor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                         toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, getBoolSort(),
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
      YicesExpr(Context, getBitvectorSort(i + Exp->getWidth()),
                yices_sign_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i)));
}

SMTExprRef YicesSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, getBitvectorSort(i + Exp->getWidth()),
                yices_zero_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i)));
}

SMTExprRef YicesSolver::mkBVExtract(unsigned High, unsigned Low,
                                    const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(
      Context, getBitvectorSort(High - Low + 1),
      yices_bvextract(toSolverExpr<YicesExpr>(*Exp).Expr, Low, High)));
}

SMTExprRef YicesSolver::mkBVConcat(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, getBitvectorSort(LHS->getWidth() + RHS->getWidth()),
                yices_bvconcat2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkFPAbs(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPNeg(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPIsInfinite(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPIsNaN(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPIsDenormal(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPIsNormal(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPIsZero(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPMul(const SMTExprRef &, const SMTExprRef &,
                                const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPDiv(const SMTExprRef &, const SMTExprRef &,
                                const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPRem(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPAdd(const SMTExprRef &, const SMTExprRef &,
                                const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPSub(const SMTExprRef &, const SMTExprRef &,
                                const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPSqrt(const SMTExprRef &, const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPFMA(const SMTExprRef &, const SMTExprRef &,
                                const SMTExprRef &, const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPLt(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPGt(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPLe(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPGe(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPEqual(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPtoFP(const SMTExprRef &, const SMTSortRef &,
                                 const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkSBVtoFP(const SMTExprRef &, const SMTSortRef &,
                                  const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkUBVtoFP(const SMTExprRef &, const SMTSortRef &,
                                  const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPtoSBV(const SMTExprRef &, unsigned) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPtoUBV(const SMTExprRef &, unsigned) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkFPtoIntegral(const SMTExprRef &, RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

bool YicesSolver::getBoolean(const SMTExprRef &Exp) {
  int32_t val;
  auto res = yices_get_bool_value(yices_get_model(Context->Context, 1),
                                  toSolverExpr<YicesExpr>(*Exp).Expr, &val);
  abortCondWithMessage(res, "Can't get boolean value from Yices");
  return val ? true : false;
}

int64_t YicesSolver::getBitvector(const SMTExprRef &Exp) {
  unsigned width = Exp->getWidth();

  int32_t data[width];
  yices_get_bv_value(yices_get_model(Context->Context, 1),
                     toSolverExpr<YicesExpr>(*Exp).Expr, data);

  int64_t val = 0;
  for (int i = width - 1; i >= 0; i--) {
    val <<= 1;
    val |= data[i];
  }

  return val;
}

float YicesSolver::getFloat(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

double YicesSolver::getDouble(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

bool YicesSolver::getInterpretation(const SMTExprRef &Exp, int64_t &Inter) {
  // TODO: Boolector never fails?
  Inter = getBitvector(Exp);
  return true;
}

bool YicesSolver::getInterpretation(const SMTExprRef &, float &) {
  abortWithMessage("Yices does not support fp");
}

bool YicesSolver::getInterpretation(const SMTExprRef &, double &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkBoolean(const bool b) {
  return newExprRef(
      YicesExpr(Context, getBoolSort(), b ? yices_true() : yices_false()));
}

SMTExprRef YicesSolver::mkBitvector(const int64_t Int, const SMTSortRef &Sort) {
  return newExprRef(
      YicesExpr(Context, Sort, yices_bvconst_int64(Sort->getWidth(), Int)));
}

SMTExprRef YicesSolver::mkSymbol(const char *Name, SMTSortRef Sort) {
  // We could use yices_get_term_by_name to check if the variable was already
  // created, but the we would need to create a new SMTExprRef, so use
  // this map instead
  auto it = SymbolTable.find(Name);
  if (it != SymbolTable.end())
    return it->second;

  abortCondWithMessage(yices_get_term_by_name(Name) == NULL_TERM,
                       "Trying to create a symbol but it already exists");

  term_t t = yices_new_uninterpreted_term(toSolverSort<YicesSort>(*Sort).Sort);
  abortCondWithMessage(t != NULL_TERM,
                       "Error when trying to create new a symbol");

  abortCondWithMessage(yices_set_term_name(t, Name) != -1,
                       "Error when trying to set symbol name");

  auto inserted = SymbolTable.insert(
      SymbolTablet::value_type(Name, newExprRef(YicesExpr(Context, Sort, t))));

  abortCondWithMessage(inserted.second, "Could not cache new Yices variable");

  return inserted.first->second;
}

SMTExprRef YicesSolver::mkFloat(const float) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkDouble(const double) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkRoundingMode(const RoundingMode) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkNaN(const bool, const unsigned, const unsigned) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkInf(const bool, const unsigned, const unsigned) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkBVToIEEEFP(const SMTExprRef &, const SMTSortRef &) {
  abortWithMessage("Yices does not support fp");
}

SMTExprRef YicesSolver::mkIEEEFPToBV(const SMTExprRef &) {
  abortWithMessage("Yices does not support fp");
}

checkResult YicesSolver::check() {
  smt_status_t res = yices_check_context(Context->Context, nullptr);
  if (res == STATUS_SAT)
    return checkResult::SAT;

  if (res == STATUS_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void YicesSolver::reset() { Context->reset(); }

void YicesSolver::dumpModel() {
  char *model_str =
      yices_model_to_string(yices_get_model(Context->Context, 1), 160, 80, 0);
  fmt::print(stderr, "{}\n", model_str);
  yices_free_string(model_str);
}

#endif
