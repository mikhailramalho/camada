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

bool YicesSort::isBitvectorSortImpl() const {
  return yices_type_is_bitvector(Sort);
}

bool YicesSort::isBooleanSortImpl() const { return yices_type_is_bool(Sort); }

bool YicesSort::isFloatSortImpl() const {
  // Always false: yices does not support fp
  return false;
}

bool YicesSort::isRoundingModeSortImpl() const {
  // Always false: yices does not support fp
  return false;
}

unsigned YicesSort::getBitvectorSortSizeImpl() const {
  return yices_bvtype_size(Sort);
}

unsigned YicesSort::getFloatSortSizeImpl() const {
  // Returning 0 should trigger a failure in camada::getFloatSortSize()
  return 0;
}

bool YicesSort::equal_to(SMTSort const &Other) const {
  // yices does not provide equality function for types,
  // but subtipe relations, so x == y <==> (x <= y /\ y <= x)

  type_t x = Sort;
  type_t y = static_cast<const YicesSort &>(Other).Sort;

  return yices_test_subtype(x, y) && yices_test_subtype(y, x);
}

void YicesSort::dump() const {
  char *ty_str = yices_type_to_string(Sort, 160, 80, 0);
  fmt::print(stderr, "{}\n", ty_str);
  yices_free_string(ty_str);
}

bool YicesExpr::equal_to(SMTExpr const &Other) const {
  camada::abortCondWithMessage(
      YicesSort(Context, yices_type_of_term(AST))
          .equal_to(YicesSort(
              Context,
              yices_type_of_term(static_cast<const YicesExpr &>(Other).AST))),
      "AST's must have the same sort");
  return (AST == dynamic_cast<const YicesExpr &>(Other).AST);
}

void YicesExpr::dump() const {
  char *term_str = yices_term_to_string(AST, 160, 80, 0);
  fmt::print(stderr, "{}\n", term_str);
  yices_free_string(term_str);
}

YicesSolver::YicesSolver() : Context(std::make_shared<YicesContext>()) {}

// YicesSolver::YicesSolver(YicesContextRef C) : Context(std::move(C)) {}

void YicesSolver::addConstraint(const SMTExprRef &Exp) {
  yices_assert_formula(Context->Context, toYicesExpr(*Exp).AST);
}

SMTSortRef YicesSolver::newSortRef(const SMTSort &Sort) const {
  abortCondWithMessage(toYicesSort(Sort).Sort != NULL_TYPE,
                       "Error when creating Yices sort.");
  return std::make_shared<YicesSort>(toYicesSort(Sort));
}

SMTExprRef YicesSolver::newExprRef(const SMTExpr &Exp) const {
  abortCondWithMessage(toYicesExpr(Exp).AST != NULL_TERM,
                       "Error when creating Yices expr.");
  return std::make_shared<YicesExpr>(toYicesExpr(Exp));
}

SMTSortRef YicesSolver::getBoolSort() {
  return newSortRef(YicesSort(Context, yices_bool_type()));
}

SMTSortRef YicesSolver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef(YicesSort(Context, yices_bv_type(BitWidth)));
}

SMTSortRef YicesSolver::getRoundingModeSort() {
  abortWithMessage("Yices does not support fp");
}

SMTSortRef YicesSolver::getFloatSort(const unsigned, const unsigned) {
  abortWithMessage("Yices does not support fp");
}

SMTSortRef YicesSolver::getSort(const SMTExprRef &Exp) {
  return newSortRef(
      YicesSort(Context, yices_type_of_term(toYicesExpr(*Exp).AST)));
}

SMTExprRef YicesSolver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, yices_neg(toYicesExpr(*Exp).AST)));
}

SMTExprRef YicesSolver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, yices_bvnot(toYicesExpr(*Exp).AST)));
}

SMTExprRef YicesSolver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, yices_not(toYicesExpr(*Exp).AST)));
}

SMTExprRef YicesSolver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvadd(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvsub(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvmul(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvsrem(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvrem(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvsdiv(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvdiv(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvshl(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvashr(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvlshr(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvxor2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvor2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvand2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvlt_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvslt_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvgt_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvsgt_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvle_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvsle_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvge_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvsge_atom(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_and2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_or2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_eq(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
}

SMTExprRef YicesSolver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                              const SMTExprRef &F) {
  return newExprRef(
      YicesExpr(Context, yices_ite(toYicesExpr(*Cond).AST, toYicesExpr(*T).AST,
                                   toYicesExpr(*F).AST)));
}

SMTExprRef YicesSolver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, yices_sign_extend(toYicesExpr(*Exp).AST, i)));
}

SMTExprRef YicesSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, yices_zero_extend(toYicesExpr(*Exp).AST, i)));
}

SMTExprRef YicesSolver::mkBVExtract(unsigned High, unsigned Low,
                                    const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, yices_bvextract(toYicesExpr(*Exp).AST, Low, High)));
}

SMTExprRef YicesSolver::mkBVConcat(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, yices_bvconcat2(toYicesExpr(*LHS).AST, toYicesExpr(*RHS).AST)));
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
};

bool YicesSolver::getBoolean(const SMTExprRef &Exp) {
  int32_t val;
  auto res = yices_get_bool_value(yices_get_model(Context->Context, 1),
                                  toYicesExpr(*Exp).AST, &val);
  abortCondWithMessage(res, "Can't get boolean value from Yices");
  return val ? true : false;
}

int64_t YicesSolver::getBitvector(const SMTExprRef &Exp) {
  unsigned width = yices_term_bitsize(toYicesExpr(*Exp).AST);

  int32_t data[width];
  yices_get_bv_value(yices_get_model(Context->Context, 1),
                     toYicesExpr(*Exp).AST, data);

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
  return newExprRef(YicesExpr(Context, b ? yices_true() : yices_false()));
}

SMTExprRef YicesSolver::mkBitvector(const int64_t Int, unsigned BitWidth) {
  return newExprRef(YicesExpr(Context, yices_bvconst_int64(BitWidth, Int)));
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

  term_t t = yices_new_uninterpreted_term(toYicesSort(*Sort).Sort);
  abortCondWithMessage(t != NULL_TERM,
                       "Error when trying to create new a symbol");

  abortCondWithMessage(yices_set_term_name(t, Name) != -1,
                       "Error when trying to set symbol name");

  auto inserted = SymbolTable.insert(
      SymbolTablet::value_type(Name, newExprRef(YicesExpr(Context, t))));

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

checkResult YicesSolver::check() {
  smt_status_t res = yices_check_context(Context->Context, nullptr);
  if (res == STATUS_SAT)
    return checkResult::SAT;

  if (res == STATUS_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void YicesSolver::push() { yices_push(Context->Context); }

void YicesSolver::pop(unsigned NumStates) {
  while (NumStates--)
    yices_pop(Context->Context);
}

void YicesSolver::reset() { Context->reset(); }

void YicesSolver::dumpModel() {
  char *model_str =
      yices_model_to_string(yices_get_model(Context->Context, 1), 160, 80, 0);
  fmt::print(stderr, "{}\n", model_str);
  yices_free_string(model_str);
}

#endif
