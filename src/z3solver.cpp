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

void Z3Sort::dump() const {
  fmt::print(stderr, "{}\n", Z3_sort_to_string(*Context, Sort));
}

bool Z3Expr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
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
  Solver.add(toSolverExpr<Z3Expr>(*Exp).Expr);
}

SMTExprRef Z3Solver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<Z3Expr>(toSolverExpr<Z3Expr>(Exp));
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

SMTExprRef Z3Solver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, -toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, ~toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, !toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr +
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr -
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr *
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::srem(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::urem(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr /
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::udiv(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::shl(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::ashr(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::lshr(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr ^
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr |
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr &
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::ult(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::slt(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::ugt(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr >
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::ule(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::sle(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::uge(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr >=
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, getBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr &&
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, getBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr ||
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, getBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr ==
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                           const SMTExprRef &F) {
  return newExprRef(Z3Expr(Context, T->Sort,
                           z3::ite(toSolverExpr<Z3Expr>(*Cond).Expr,
                                   toSolverExpr<Z3Expr>(*T).Expr,
                                   toSolverExpr<Z3Expr>(*F).Expr)));
}

SMTExprRef Z3Solver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, getBitvectorSort(i + Exp->Sort->getBitvectorSortSize()),
             z3::sext(toSolverExpr<Z3Expr>(*Exp).Expr, i)));
}

SMTExprRef Z3Solver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, getBitvectorSort(i + Exp->Sort->getBitvectorSortSize()),
             z3::zext(toSolverExpr<Z3Expr>(*Exp).Expr, i)));
}

SMTExprRef Z3Solver::mkBVExtract(unsigned High, unsigned Low,
                                 const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, getBitvectorSort(High - Low + 1),
                           toSolverExpr<Z3Expr>(*Exp).Expr.extract(High, Low)));
}

SMTExprRef Z3Solver::mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context,
                           getBitvectorSort(LHS->Sort->getBitvectorSortSize() +
                                            RHS->Sort->getBitvectorSortSize()),
                           z3::concat(toSolverExpr<Z3Expr>(*LHS).Expr,
                                      toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkFPNeg(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, -toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkFPIsInfinite(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, getBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_infinite(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsNaN(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, getBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_nan(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsNormal(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, getBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_normal(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsZero(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, getBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_zero(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, LHS->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_mul(*Context,
                                       toSolverExpr<Z3Expr>(*roundingMode).Expr,
                                       toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, LHS->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_div(*Context,
                                       toSolverExpr<Z3Expr>(*roundingMode).Expr,
                                       toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::rem(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, LHS->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_add(*Context,
                                       toSolverExpr<Z3Expr>(*roundingMode).Expr,
                                       toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, LHS->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_sub(*Context,
                                       toSolverExpr<Z3Expr>(*roundingMode).Expr,
                                       toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPSqrt(const SMTExprRef &Exp, const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, Exp->Sort,
      z3::to_expr(*Context,
                  Z3_mk_fpa_sqrt(*Context,
                                 toSolverExpr<Z3Expr>(*roundingMode).Expr,
                                 toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z, const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, X->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_fma(*Context,
                                       toSolverExpr<Z3Expr>(*roundingMode).Expr,
                                       toSolverExpr<Z3Expr>(*X).Expr,
                                       toSolverExpr<Z3Expr>(*Y).Expr,
                                       toSolverExpr<Z3Expr>(*Z).Expr))));
}

SMTExprRef Z3Solver::mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, getBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr <
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, getBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr >
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, getBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr <=
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, getBoolSort(),
      z3::to_expr(*Context,
                  Z3_mk_fpa_geq(*Context, toSolverExpr<Z3Expr>(*LHS).Expr,
                                toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, getBoolSort(),
             z3::to_expr(*Context,
                         Z3_mk_fpa_eq(*Context, toSolverExpr<Z3Expr>(*LHS).Expr,
                                      toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, To,
             z3::to_expr(*Context,
                         Z3_mk_fpa_to_fp_float(
                             *Context, toSolverExpr<Z3Expr>(*roundingMode).Expr,
                             toSolverExpr<Z3Expr>(*From).Expr,
                             toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, To,
             z3::to_expr(*Context,
                         Z3_mk_fpa_to_fp_signed(
                             *Context, toSolverExpr<Z3Expr>(*roundingMode).Expr,
                             toSolverExpr<Z3Expr>(*From).Expr,
                             toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, To,
             z3::to_expr(*Context,
                         Z3_mk_fpa_to_fp_unsigned(
                             *Context, toSolverExpr<Z3Expr>(*roundingMode).Expr,
                             toSolverExpr<Z3Expr>(*From).Expr,
                             toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(
      Z3Expr(Context, getBitvectorSort(ToWidth),
             z3::to_expr(*Context,
                         Z3_mk_fpa_to_sbv(
                             *Context, toSolverExpr<Z3Expr>(*roundingMode).Expr,
                             toSolverExpr<Z3Expr>(*From).Expr, ToWidth))));
}

SMTExprRef Z3Solver::mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(
      Z3Expr(Context, getBitvectorSort(ToWidth),
             z3::to_expr(*Context,
                         Z3_mk_fpa_to_ubv(
                             *Context, toSolverExpr<Z3Expr>(*roundingMode).Expr,
                             toSolverExpr<Z3Expr>(*From).Expr, ToWidth))));
}

SMTExprRef Z3Solver::mkFPtoIntegral(const SMTExprRef &From, RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      Z3Expr(Context, From->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_round_to_integral(
                             *Context, toSolverExpr<Z3Expr>(*roundingMode).Expr,
                             toSolverExpr<Z3Expr>(*From).Expr))));
}

bool Z3Solver::getBoolean(const SMTExprRef &Exp) {
  return toSolverExpr<Z3Expr>(*Exp).Expr.bool_value();
}

int64_t Z3Solver::getBitvector(const SMTExprRef &Exp) {
  int64_t bv;
  bool is_num = toSolverExpr<Z3Expr>(*Exp).Expr.is_numeral_i64(bv);
  camada::abortCondWithMessage(is_num, "Failed to get bitvector from Z3");
  return bv;
}

template <typename FPType, typename IntType,
          bool (*Z3Func)(Z3_context c, Z3_ast v, IntType *i)>
static inline FPType getFP(const Z3ContextRef &C, const z3::model &Model,
                           const SMTExprRef &Exp) {
  // TODO: what about negative NaN?
  if (Z3_fpa_is_numeral_nan(*C, toSolverExpr<Z3Expr>(*Exp).Expr))
    return NAN;

  if (Z3_fpa_is_numeral_inf(*C, toSolverExpr<Z3Expr>(*Exp).Expr))
    return Z3_fpa_is_numeral_positive(*C, toSolverExpr<Z3Expr>(*Exp).Expr)
               ? INFINITY
               : -INFINITY;

  // Convert the float to bv
  Z3_ast fp_value;
  bool eval = Z3_model_eval(
      *C, Model, Z3_mk_fpa_to_ieee_bv(*C, toSolverExpr<Z3Expr>(*Exp).Expr),
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

static inline SMTExprRef getZ3Interp(const Z3Solver &S, const SMTExprRef &Exp) {
  return S.newExprRef(Z3Expr(S.Context, Exp->Sort,
                             S.Solver.get_model().get_const_interp(
                                 toSolverExpr<Z3Expr>(*Exp).Expr.decl())));
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, int64_t &Inter) {
  if (!Solver.get_model().has_interp(toSolverExpr<Z3Expr>(*Exp).Expr.decl()))
    return false;

  Inter = getBitvector(getZ3Interp(*this, Exp));
  return true;
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, float &Float) {
  if (!Solver.get_model().has_interp(toSolverExpr<Z3Expr>(*Exp).Expr.decl()))
    return false;

  Float = getFloat(getZ3Interp(*this, Exp));
  return true;
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, double &Double) {
  if (!Solver.get_model().has_interp(toSolverExpr<Z3Expr>(*Exp).Expr.decl()))
    return false;

  Double = getDouble(getZ3Interp(*this, Exp));
  return true;
}

SMTExprRef Z3Solver::mkBoolean(const bool b) {
  return newExprRef(Z3Expr(Context, getBoolSort(), Context->bool_val(b)));
}

SMTExprRef Z3Solver::mkBitvector(const int64_t Int, unsigned BitWidth) {
  const SMTSortRef sort = getBitvectorSort(BitWidth);
  return newExprRef(Z3Expr(Context, sort, Context->bv_val(Int, BitWidth)));
}

SMTExprRef Z3Solver::mkSymbol(const char *Name, SMTSortRef Sort) {
  return newExprRef(
      Z3Expr(Context, Sort,
             Context->constant(Name, toSolverSort<Z3Sort>(*Sort).Sort)));
}

SMTExprRef Z3Solver::mkFloat(const float Float) {
  return newExprRef(Z3Expr(Context, getFloat32Sort(), Context->fpa_val(Float)));
}

SMTExprRef Z3Solver::mkDouble(const double Double) {
  return newExprRef(
      Z3Expr(Context, getFloat64Sort(), Context->fpa_val(Double)));
}

SMTExprRef Z3Solver::mkRoundingMode(const RoundingMode R) {
  z3::expr e(*Context);
  switch (R) {
  default:
    camada::abortWithMessage("Unsupported floating-point semantics.");
  case RoundingMode::ROUND_TO_EVEN:
    e = z3::to_expr(*Context, Z3_mk_fpa_rne(*Context));
    break;
  case RoundingMode::ROUND_TO_AWAY:
    e = z3::to_expr(*Context, Z3_mk_fpa_rna(*Context));
    break;
  case RoundingMode::ROUND_TO_PLUS_INF:
    e = z3::to_expr(*Context, Z3_mk_fpa_rtp(*Context));
    break;
  case RoundingMode::ROUND_TO_MINUS_INF:
    e = z3::to_expr(*Context, Z3_mk_fpa_rtn(*Context));
    break;
  case RoundingMode::ROUND_TO_ZERO:
    e = z3::to_expr(*Context, Z3_mk_fpa_rtz(*Context));
    break;
  }
  return newExprRef(Z3Expr(Context, getRoundingModeSort(), e));
}

SMTExprRef Z3Solver::mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  SMTExprRef theNaN = newExprRef(Z3Expr(
      Context, sort,
      z3::to_expr(*Context,
                  Z3_mk_fpa_nan(*Context, toSolverSort<Z3Sort>(*sort).Sort))));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef Z3Solver::mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  return newExprRef(Z3Expr(
      Context, sort,
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
