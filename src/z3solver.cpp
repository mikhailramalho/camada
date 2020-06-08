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

#include "z3solver.h"
#include "ac_config.h"

#include <fmt/printf.h>

using namespace camada;

#ifdef SOLVER_Z3_ENABLED

bool Z3Sort::equal_to(SMTSort const &Other) const {
  return Z3_is_eq_sort(*Context, Sort,
                       dynamic_cast<const Z3Sort &>(Other).Sort);
}

void Z3Sort::dump() const {
  fmt::print(stderr, "{}\n", Z3_sort_to_string(*Context, Sort));
}

bool Z3Expr::equal_to(SMTExpr const &Other) const {
  camada::abortCondWithMessage(
      Z3_is_eq_sort(*Context, Expr.get_sort(),
                    dynamic_cast<const Z3Expr &>(Other).Expr.get_sort()),
      "AST's must have the same sort");
  return z3::eq(Expr, dynamic_cast<const Z3Expr &>(Other).Expr);
}

void Z3Expr::dump() const {
  fmt::print(stderr, "{}\n", Z3_ast_to_string(*Context, Expr));
}

// Function used to report errors
void Z3ErrorHandler(Z3_context Context, Z3_error_code Error) {
  fmt::print(stderr, "Z3 error: {}\n",
             std::string(Z3_get_error_msg(Context, Error)));
}

Z3Solver::Z3Solver()
    : Context(std::make_shared<z3::context>()), Solver(*Context) {
  Z3_set_error_handler(*Context, Z3ErrorHandler);
}

Z3Solver::Z3Solver(Z3ContextRef C, const z3::solver &S)
    : Context(std::move(C)), Solver(S) {
  Z3_set_error_handler(*Context, Z3ErrorHandler);
}

void Z3Solver::addConstraint(const SMTExprRef &Exp) {
  Solver.add(toZ3Expr(*Exp).Expr);
}

SMTExprRef Z3Solver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<Z3Expr>(toZ3Expr(Exp));
}

SMTSortRef Z3Solver::getBoolSort() {
  return newSortRef<camada::SolverBoolSort<Z3Sort>>(
      camada::SolverBoolSort<Z3Sort>(Context, Context->bool_sort()));
}

SMTSortRef Z3Solver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef<camada::SolverBVSort<Z3Sort>>(camada::SolverBVSort<Z3Sort>(
      BitWidth, Context, Context->bv_sort(BitWidth)));
}

SMTSortRef Z3Solver::getRoundingModeSort() {
  return newSortRef<camada::SolverRMSort<Z3Sort>>(camada::SolverRMSort<Z3Sort>(
      Context, z3::to_sort(*Context, Z3_mk_fpa_rounding_mode_sort(*Context))));
}

SMTSortRef Z3Solver::getFloatSort(const unsigned ExpWidth,
                                  const unsigned SigWidth) {
  return newSortRef<camada::SolverFPSort<Z3Sort>>(camada::SolverFPSort<Z3Sort>(
      ExpWidth, SigWidth, Context, Context->fpa_sort(ExpWidth, SigWidth)));
}

SMTSortRef Z3Solver::getSort(const SMTExprRef &Exp) {
  abortWithMessage("Currently unimplemented");
  return nullptr;
}

SMTExprRef Z3Solver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, -toZ3Expr(*Exp).Expr));
}

SMTExprRef Z3Solver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, ~toZ3Expr(*Exp).Expr));
}

SMTExprRef Z3Solver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, !toZ3Expr(*Exp).Expr));
}

SMTExprRef Z3Solver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr + toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr - toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr * toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::srem(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::urem(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr / toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::udiv(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::shl(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ashr(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::lshr(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr ^ toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr | toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr & toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ult(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::slt(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ugt(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr > toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ule(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::sle(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::uge(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, toZ3Expr(*LHS).Expr >= toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, toZ3Expr(*LHS).Expr && toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, toZ3Expr(*LHS).Expr || toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, toZ3Expr(*LHS).Expr == toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                           const SMTExprRef &F) {
  return newExprRef(
      Z3Expr(Context, z3::ite(toZ3Expr(*Cond).Expr, toZ3Expr(*T).Expr,
                              toZ3Expr(*F).Expr)));
}

SMTExprRef Z3Solver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, z3::sext(toZ3Expr(*Exp).Expr, i)));
}

SMTExprRef Z3Solver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, z3::zext(toZ3Expr(*Exp).Expr, i)));
}

SMTExprRef Z3Solver::mkBVExtract(unsigned High, unsigned Low,
                                 const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*Exp).Expr.extract(High, Low)));
}

SMTExprRef Z3Solver::mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::concat(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkFPNeg(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, -toZ3Expr(*Exp).Expr));
}

SMTExprRef Z3Solver::mkFPIsInfinite(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_is_infinite(
                                         *Context, toZ3Expr(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsNaN(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_is_nan(*Context, toZ3Expr(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsNormal(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_is_normal(
                                         *Context, toZ3Expr(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsZero(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_is_zero(*Context, toZ3Expr(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_mul(*Context, toZ3Expr(*roundingMode).Expr,
                                toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_div(*Context, toZ3Expr(*roundingMode).Expr,
                                toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::rem(toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_add(*Context, toZ3Expr(*roundingMode).Expr,
                                toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_sub(*Context, toZ3Expr(*roundingMode).Expr,
                                toZ3Expr(*LHS).Expr, toZ3Expr(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPSqrt(const SMTExprRef &Exp, const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_sqrt(
                                         *Context, toZ3Expr(*roundingMode).Expr,
                                         toZ3Expr(*Exp).Expr))));
};

SMTExprRef Z3Solver::mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z, const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context,
                           Z3_mk_fpa_fma(*Context, toZ3Expr(*roundingMode).Expr,
                                         toZ3Expr(*X).Expr, toZ3Expr(*Y).Expr,
                                         toZ3Expr(*Z).Expr))));
};

SMTExprRef Z3Solver::mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr < toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).Expr > toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, toZ3Expr(*LHS).Expr <= toZ3Expr(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context,
             z3::to_expr(*Context, Z3_mk_fpa_geq(*Context, toZ3Expr(*LHS).Expr,
                                                 toZ3Expr(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_eq(*Context, toZ3Expr(*LHS).Expr,
                                                  toZ3Expr(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_fp_float(
                                         *Context, toZ3Expr(*roundingMode).Expr,
                                         toZ3Expr(*From).Expr,
                                         toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_fp_signed(
                                         *Context, toZ3Expr(*roundingMode).Expr,
                                         toZ3Expr(*From).Expr,
                                         toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_fp_unsigned(
                                         *Context, toZ3Expr(*roundingMode).Expr,
                                         toZ3Expr(*From).Expr,
                                         toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_sbv(
                                         *Context, toZ3Expr(*roundingMode).Expr,
                                         toZ3Expr(*From).Expr, ToWidth))));
}

SMTExprRef Z3Solver::mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_ubv(
                                         *Context, toZ3Expr(*roundingMode).Expr,
                                         toZ3Expr(*From).Expr, ToWidth))));
}

SMTExprRef Z3Solver::mkFPtoIntegral(const SMTExprRef &From, RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_round_to_integral(
                                         *Context, toZ3Expr(*roundingMode).Expr,
                                         toZ3Expr(*From).Expr))));
};

bool Z3Solver::getBoolean(const SMTExprRef &Exp) {
  return toZ3Expr(*Exp).Expr.bool_value();
}

int64_t Z3Solver::getBitvector(const SMTExprRef &Exp) {
  int64_t bv;
  bool is_num = toZ3Expr(*Exp).Expr.is_numeral_i64(bv);
  camada::abortCondWithMessage(is_num, "Failed to get bitvector from Z3");
  return bv;
}

template <typename FPType, typename IntType,
          bool (*Z3Func)(Z3_context c, Z3_ast v, IntType *i)>
static inline FPType getFP(const Z3ContextRef &C, const z3::model &Model,
                           const SMTExprRef &Exp) {
  // TODO: what about negative NaN?
  if (Z3_fpa_is_numeral_nan(*C, toZ3Expr(*Exp).Expr))
    return NAN;

  if (Z3_fpa_is_numeral_inf(*C, toZ3Expr(*Exp).Expr))
    return Z3_fpa_is_numeral_positive(*C, toZ3Expr(*Exp).Expr) ? INFINITY
                                                               : -INFINITY;

  // Convert the float to bv
  Z3_ast fp_value;
  bool eval =
      Z3_model_eval(*C, Model, Z3_mk_fpa_to_ieee_bv(*C, toZ3Expr(*Exp).Expr),
                    true, &fp_value);
  camada::abortCondWithMessage(eval, "Failed to convert FP to BV in Z3");

  IntType FP_as_int;
  (*Z3Func)(*C, fp_value, &FP_as_int);

  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  camada::abortCondWithMessage(sizeof(FPType) == sizeof(IntType),
                               "Cannot convert int to floating-point");

  FPType result;
  memcpy(&result, &FP_as_int, sizeof(FPType));
  return result;
}

float Z3Solver::getFloat(const SMTExprRef &Exp) {
  return getFP<float, int32_t, Z3_get_numeral_int>(Context, Solver.get_model(),
                                                   Exp);
}

double Z3Solver::getDouble(const SMTExprRef &Exp) {
  return getFP<double, int64_t, Z3_get_numeral_int64>(Context,
                                                      Solver.get_model(), Exp);
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, int64_t &Inter) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).Expr.decl()))
    return false;

  Inter = getBitvector(newExprRef(
      Z3Expr(Context,
             Solver.get_model().get_const_interp(toZ3Expr(*Exp).Expr.decl()))));
  return true;
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, float &Float) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).Expr.decl()))
    return false;

  Float =
      getFloat(newExprRef(Z3Expr(Context, Solver.get_model().get_const_interp(
                                              toZ3Expr(*Exp).Expr.decl()))));
  return true;
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, double &Double) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).Expr.decl()))
    return false;

  Double =
      getDouble(newExprRef(Z3Expr(Context, Solver.get_model().get_const_interp(
                                               toZ3Expr(*Exp).Expr.decl()))));
  return true;
}

SMTExprRef Z3Solver::mkBoolean(const bool b) {
  return newExprRef(Z3Expr(Context, Context->bool_val(b)));
}

SMTExprRef Z3Solver::mkBitvector(const int64_t Int, unsigned BitWidth) {
  return newExprRef(Z3Expr(Context, Context->bv_val(Int, BitWidth)));
}

SMTExprRef Z3Solver::mkSymbol(const char *Name, SMTSortRef Sort) {
  return newExprRef(Z3Expr(
      Context, Context->constant(Name, toSolverSort<Z3Sort>(*Sort).Sort)));
}

SMTExprRef Z3Solver::mkFloat(const float Float) {
  return newExprRef(Z3Expr(Context, Context->fpa_val(Float)));
}

SMTExprRef Z3Solver::mkDouble(const double Double) {
  return newExprRef(Z3Expr(Context, Context->fpa_val(Double)));
}

SMTExprRef Z3Solver::mkRoundingMode(const RoundingMode R) {
  switch (R) {
  case RoundingMode::ROUND_TO_EVEN:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rne(*Context))));
  case RoundingMode::ROUND_TO_AWAY:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rna(*Context))));
  case RoundingMode::ROUND_TO_PLUS_INF:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rtp(*Context))));
  case RoundingMode::ROUND_TO_MINUS_INF:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rtn(*Context))));
  case RoundingMode::ROUND_TO_ZERO:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rtz(*Context))));
  default:;
  }
  camada::abortWithMessage("Unsupported floating-point semantics.");
}

SMTExprRef Z3Solver::mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  SMTExprRef theNaN = newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_nan(*Context, toSolverSort<Z3Sort>(*sort).Sort))));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef Z3Solver::mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(
          *Context,
          Z3_mk_fpa_inf(*Context, toSolverSort<Z3Sort>(*sort).Sort, Sgn))));
}

checkResult Z3Solver::check() {
  z3::check_result res = Solver.check();
  if (res == z3::check_result::sat)
    return checkResult::SAT;

  if (res == z3::check_result::unsat)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void Z3Solver::push() { Solver.push(); }

void Z3Solver::pop(unsigned NumStates) { Solver.pop(NumStates); }

void Z3Solver::reset() { Solver.reset(); }

void Z3Solver::dump() {
  fmt::print(stderr, "{}\n", Z3_solver_to_string(*Context, Solver));
}

void Z3Solver::dumpModel() {
  fmt::print(stderr, "{}\n", Z3_model_to_string(*Context, Solver.get_model()));
}

#endif
