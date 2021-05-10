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

#include "ac_config.h"
#if SOLVER_Z3_ENABLED

#include "z3solver.h"

namespace camada {

unsigned Z3Sort::getWidthFromSolver() const {
  if (Sort.is_bv())
    return Sort.bv_size();

  if (Sort.is_bool())
    return 1;

  if (Sort.is_fpa())
    return Sort.fpa_ebits() + Sort.fpa_sbits();

  assert(Sort.sort_kind() == Z3_ROUNDING_MODE_SORT);
  return 3;
}

void Z3Sort::dump() const {
  std::cerr << Z3_sort_to_string(*Context, Sort) << '\n';
}

bool Z3Expr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
  return z3::eq(Expr, dynamic_cast<const Z3Expr &>(Other).Expr);
}

void Z3Expr::dump() const {
  std::cerr << Z3_ast_to_string(*Context, Expr) << '\n';
}

Z3Solver::Z3Solver()
    : SMTSolverImpl(), Context(std::make_shared<z3::context>()),
      Solver(*Context) {
  // Needs to be set in order to convert NaN to bitvector
  z3::set_param("rewriter.hi_fp_unspecified", true);
}

Z3Solver::Z3Solver(Z3ContextRef C, const z3::solver &S)
    : SMTSolverImpl(), Context(std::move(C)), Solver(S) {
  // Needs to be set in order to convert NaN to bitvector
  z3::set_param("rewriter.hi_fp_unspecified", true);
}

void Z3Solver::addConstraintImpl(const SMTExprRef &Exp) {
  Solver.add(toSolverExpr<Z3Expr>(*Exp).Expr);
}

SMTExprRef Z3Solver::newExprRefImpl(const SMTExpr &Exp) const {
  return std::make_shared<Z3Expr>(toSolverExpr<Z3Expr>(Exp));
}

SMTSortRef Z3Solver::mkBoolSortImpl() {
  return newSortRef<SolverBoolSort<Z3Sort>>({Context, Context->bool_sort()});
}

SMTSortRef Z3Solver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<SolverBVSort<Z3Sort>>(
      {BitWidth, Context, Context->bv_sort(BitWidth)});
}

SMTSortRef Z3Solver::mkRMSortImpl() {
  return newSortRef<SolverRMSort<Z3Sort>>(
      {Context, z3::to_sort(*Context, Z3_mk_fpa_rounding_mode_sort(*Context))});
}

SMTSortRef Z3Solver::mkFPSortImpl(const unsigned ExpWidth,
                                  const unsigned SigWidth) {
  return newSortRef<SolverFPSort<Z3Sort>>(
      {ExpWidth, SigWidth, Context, Context->fpa_sort(ExpWidth, SigWidth + 1)});
}

SMTSortRef Z3Solver::mkBVFPSortImpl(const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  return newSortRef<SolverBVFPSort<Z3Sort>>(
      {ExpWidth, SigWidth + 1, Context,
       Context->bv_sort(ExpWidth + SigWidth + 1)});
}

SMTSortRef Z3Solver::mkBVRMSortImpl() {
  return newSortRef<SolverBVRMSort<Z3Sort>>({Context, Context->bv_sort(3)});
}

SMTSortRef Z3Solver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                     const SMTSortRef &ElemSort) {
  return newSortRef<SolverArraySort<Z3Sort>>(
      {IndexSort, ElemSort, Context,
       Context->array_sort(toSolverSort<Z3Sort>(*IndexSort).Sort,
                           toSolverSort<Z3Sort>(*ElemSort).Sort)});
}

SMTExprRef Z3Solver::mkBVNegImpl(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, -toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkBVNotImpl(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, ~toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkNotImpl(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, !toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkBVAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr +
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr -
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr *
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVSRemImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::srem(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVURemImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::urem(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSDivImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr /
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUDivImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::udiv(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVShlImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::shl(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVAshrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::ashr(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVLshrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::lshr(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr ^
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr |
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr &
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           z3::ult(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           z3::slt(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVUgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           z3::ugt(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr >
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkBVUleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           z3::ule(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           z3::sle(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVUgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           z3::uge(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVSgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr >=
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr &&
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr ||
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, LHS->Sort,
      z3::to_expr(*Context, Z3_mk_xor(*Context, toSolverExpr<Z3Expr>(*LHS).Expr,
                                      toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkEqualImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr ==
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                               const SMTExprRef &F) {
  return newExprRef(Z3Expr(Context, T->Sort,
                           z3::ite(toSolverExpr<Z3Expr>(*Cond).Expr,
                                   toSolverExpr<Z3Expr>(*T).Expr,
                                   toSolverExpr<Z3Expr>(*F).Expr)));
}

SMTExprRef Z3Solver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBVSort(i + Exp->getWidth()),
                           z3::sext(toSolverExpr<Z3Expr>(*Exp).Expr, i)));
}

SMTExprRef Z3Solver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBVSort(i + Exp->getWidth()),
                           z3::zext(toSolverExpr<Z3Expr>(*Exp).Expr, i)));
}

SMTExprRef Z3Solver::mkBVExtractImpl(unsigned High, unsigned Low,
                                     const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBVSort(High - Low + 1),
                           toSolverExpr<Z3Expr>(*Exp).Expr.extract(High, Low)));
}

SMTExprRef Z3Solver::mkBVConcatImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
                           z3::concat(toSolverExpr<Z3Expr>(*LHS).Expr,
                                      toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVRedOrImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, mkBVSort(1),
      z3::to_expr(*Context,
                  Z3_mk_bvredor(*Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkBVRedAndImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, mkBVSort(1),
      z3::to_expr(*Context,
                  Z3_mk_bvredand(*Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkArraySelectImpl(const SMTExprRef &Array,
                                       const SMTExprRef &Index) {
  return newExprRef(Z3Expr(Context, Array->Sort->getElementSort(),
                           z3::select(toSolverExpr<Z3Expr>(*Array).Expr,
                                      toSolverExpr<Z3Expr>(*Index).Expr)));
}

SMTExprRef Z3Solver::mkArrayStoreImpl(const SMTExprRef &Array,
                                      const SMTExprRef &Index,
                                      const SMTExprRef &Element) {
  return newExprRef(Z3Expr(Context, Array->Sort,
                           z3::store(toSolverExpr<Z3Expr>(*Array).Expr,
                                     toSolverExpr<Z3Expr>(*Index).Expr,
                                     toSolverExpr<Z3Expr>(*Element).Expr)));
}

SMTExprRef Z3Solver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, mkBoolSort(),
      z3::to_expr(*Context,
                  Z3_mk_fpa_abs(*Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPNegImpl(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, -toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, mkBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_infinite(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, mkBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_nan(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, mkBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_subnormal(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, mkBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_normal(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, mkBoolSort(),
      z3::to_expr(*Context, Z3_mk_fpa_is_zero(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, LHS->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_mul(*Context, toSolverExpr<Z3Expr>(*R).Expr,
                                       toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, LHS->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_div(*Context, toSolverExpr<Z3Expr>(*R).Expr,
                                       toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::rem(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, LHS->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_add(*Context, toSolverExpr<Z3Expr>(*R).Expr,
                                       toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, LHS->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_sub(*Context, toSolverExpr<Z3Expr>(*R).Expr,
                                       toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPSqrtImpl(const SMTExprRef &Exp, const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_sqrt(*Context, toSolverExpr<Z3Expr>(*R).Expr,
                                        toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                 const SMTExprRef &Z, const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, X->Sort,
             z3::to_expr(*Context,
                         Z3_mk_fpa_fma(*Context, toSolverExpr<Z3Expr>(*R).Expr,
                                       toSolverExpr<Z3Expr>(*X).Expr,
                                       toSolverExpr<Z3Expr>(*Y).Expr,
                                       toSolverExpr<Z3Expr>(*Z).Expr))));
}

SMTExprRef Z3Solver::mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr <
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPGtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr >
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr <=
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPGeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*LHS).Expr >=
                               toSolverExpr<Z3Expr>(*RHS).Expr));
}

SMTExprRef Z3Solver::mkFPEqualImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, mkBoolSort(),
             z3::to_expr(*Context,
                         Z3_mk_fpa_eq(*Context, toSolverExpr<Z3Expr>(*LHS).Expr,
                                      toSolverExpr<Z3Expr>(*RHS).Expr))));
}

SMTExprRef Z3Solver::mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                  const SMTExprRef &R) {
  return newExprRef(Z3Expr(
      Context, To,
      z3::to_expr(*Context,
                  Z3_mk_fpa_to_fp_float(*Context, toSolverExpr<Z3Expr>(*R).Expr,
                                        toSolverExpr<Z3Expr>(*From).Expr,
                                        toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, To,
             z3::to_expr(*Context, Z3_mk_fpa_to_fp_signed(
                                       *Context, toSolverExpr<Z3Expr>(*R).Expr,
                                       toSolverExpr<Z3Expr>(*From).Expr,
                                       toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, To,
             z3::to_expr(*Context, Z3_mk_fpa_to_fp_unsigned(
                                       *Context, toSolverExpr<Z3Expr>(*R).Expr,
                                       toSolverExpr<Z3Expr>(*From).Expr,
                                       toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRM(RM::ROUND_TO_ZERO);
  return newExprRef(
      Z3Expr(Context, mkBVSort(ToWidth),
             z3::to_expr(*Context,
                         Z3_mk_fpa_to_sbv(
                             *Context, toSolverExpr<Z3Expr>(*roundingMode).Expr,
                             toSolverExpr<Z3Expr>(*From).Expr, ToWidth))));
}

SMTExprRef Z3Solver::mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRM(RM::ROUND_TO_ZERO);
  return newExprRef(
      Z3Expr(Context, mkBVSort(ToWidth),
             z3::to_expr(*Context,
                         Z3_mk_fpa_to_ubv(
                             *Context, toSolverExpr<Z3Expr>(*roundingMode).Expr,
                             toSolverExpr<Z3Expr>(*From).Expr, ToWidth))));
}

SMTExprRef Z3Solver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                        const SMTExprRef &R) {
  return newExprRef(
      Z3Expr(Context, From->Sort,
             z3::to_expr(*Context, Z3_mk_fpa_round_to_integral(
                                       *Context, toSolverExpr<Z3Expr>(*R).Expr,
                                       toSolverExpr<Z3Expr>(*From).Expr))));
}

bool Z3Solver::getBoolImpl(const SMTExprRef &Exp) {
  return toSolverExpr<Z3Expr>(*Exp).Expr.bool_value();
}

static inline bool hasZ3Interp(const Z3Solver &S, const SMTExprRef &Exp) {
  return S.Solver.get_model().has_interp(
      toSolverExpr<Z3Expr>(*Exp).Expr.decl());
}

static inline SMTExprRef getZ3Interp(const Z3Solver &S, const SMTExprRef &Exp) {
  return S.newExprRef(Z3Expr(S.Context, Exp->Sort,
                             S.Solver.get_model().get_const_interp(
                                 toSolverExpr<Z3Expr>(*Exp).Expr.decl())));
}

std::string Z3Solver::getBVInBinImpl(const SMTExprRef &Exp) {
  SMTExprRef value = hasZ3Interp(*this, Exp) ? getZ3Interp(*this, Exp) : Exp;
  std::string bv;
  bool is_num = toSolverExpr<Z3Expr>(*value).Expr.as_binary(bv);
  (void)is_num;
  assert(is_num && "Failed to get bitvector from Z3");
  return bv;
}

std::string Z3Solver::getFPInBinImpl(const SMTExprRef &Exp) {
  SMTExprRef value = hasZ3Interp(*this, Exp) ? getZ3Interp(*this, Exp) : Exp;

  // Convert the float to bv
  Z3_ast fp_value;
  bool eval = Z3_model_eval(
      *Context, Solver.get_model(),
      Z3_mk_fpa_to_ieee_bv(*Context, toSolverExpr<Z3Expr>(*value).Expr), true,
      &fp_value);
  (void)eval;
  assert(eval && "Failed to convert FP to BV in Z3");
  return Z3_get_numeral_binary_string(*Context, fp_value);
}

SMTExprRef Z3Solver::getArrayElementImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index) {
  SMTExprRef sel = mkArraySelect(Array, Index);
  SMTExprRef value = hasZ3Interp(*this, sel) ? getZ3Interp(*this, sel) : sel;

  return newExprRef(
      Z3Expr(Context, sel->Sort,
             Solver.get_model().eval(toSolverExpr<Z3Expr>(*value).Expr)));
}

SMTExprRef Z3Solver::mkBoolImpl(const bool b) {
  return newExprRef(Z3Expr(Context, mkBoolSort(), Context->bool_val(b)));
}

SMTExprRef Z3Solver::mkBVFromDecImpl(const int64_t Int,
                                     const SMTSortRef &Sort) {
  return newExprRef(
      Z3Expr(Context, Sort, Context->bv_val(Int, Sort->getWidth())));
}

SMTExprRef Z3Solver::mkBVFromBinImpl(const std::string &Int,
                                     const SMTSortRef &Sort) {
  std::size_t s = Sort->getWidth();
  bool *newInt = new bool[s];
  for (unsigned int i = 0; i < s; ++i)
    newInt[s - i - 1] = (Int[i] == '1');

  SMTExprRef bv = newExprRef(Z3Expr(Context, Sort, Context->bv_val(s, newInt)));
  delete[] newInt;
  return bv;
}

SMTExprRef Z3Solver::mkSymbolImpl(const std::string &Name,
                                  const SMTSortRef &Sort) {
  return newExprRef(Z3Expr(
      Context, Sort,
      Context->constant(Name.c_str(), toSolverSort<Z3Sort>(*Sort).Sort)));
}

SMTExprRef Z3Solver::mkFPFromBinImpl(const std::string &FP, unsigned EWidth) {
  SMTExprRef sgn = SMTSolverImpl::mkBVFromBin({FP[0]});
  SMTExprRef exp = SMTSolverImpl::mkBVFromBin(FP.substr(1, EWidth));
  SMTExprRef sig = SMTSolverImpl::mkBVFromBin(FP.substr(1 + EWidth));

  return newExprRef(
      Z3Expr(Context, mkFPSort(EWidth, FP.length() - EWidth - 1),
             z3::to_expr(*Context,
                         Z3_mk_fpa_fp(*Context, toSolverExpr<Z3Expr>(*sgn).Expr,
                                      toSolverExpr<Z3Expr>(*exp).Expr,
                                      toSolverExpr<Z3Expr>(*sig).Expr))));
}

SMTExprRef Z3Solver::mkRMImpl(const RM &R) {
  z3::expr e(*Context);
  switch (R) {
  default:
    assert(0 && "Unsupported floating-point semantics.");
    __builtin_unreachable();
  case RM::ROUND_TO_EVEN:
    e = z3::to_expr(*Context, Z3_mk_fpa_rne(*Context));
    break;
  case RM::ROUND_TO_AWAY:
    e = z3::to_expr(*Context, Z3_mk_fpa_rna(*Context));
    break;
  case RM::ROUND_TO_PLUS_INF:
    e = z3::to_expr(*Context, Z3_mk_fpa_rtp(*Context));
    break;
  case RM::ROUND_TO_MINUS_INF:
    e = z3::to_expr(*Context, Z3_mk_fpa_rtn(*Context));
    break;
  case RM::ROUND_TO_ZERO:
    e = z3::to_expr(*Context, Z3_mk_fpa_rtz(*Context));
    break;
  }
  return newExprRef(Z3Expr(Context, mkRMSort(), e));
}

SMTExprRef Z3Solver::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth) {
  SMTSortRef sort = mkFPSort(ExpWidth, SigWidth - 1);
  SMTExprRef theNaN = newExprRef(Z3Expr(
      Context, sort,
      z3::to_expr(*Context,
                  Z3_mk_fpa_nan(*Context, toSolverSort<Z3Sort>(*sort).Sort))));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef Z3Solver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth) {
  SMTSortRef sort = mkFPSort(ExpWidth, SigWidth - 1);
  return newExprRef(Z3Expr(
      Context, sort,
      z3::to_expr(
          *Context,
          Z3_mk_fpa_inf(*Context, toSolverSort<Z3Sort>(*sort).Sort, Sgn))));
}

SMTExprRef Z3Solver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                      const SMTSortRef &To) {
  return newExprRef(Z3Expr(
      Context, To,
      z3::to_expr(*Context,
                  Z3_mk_fpa_to_fp_bv(*Context, toSolverExpr<Z3Expr>(*Exp).Expr,
                                     toSolverSort<Z3Sort>(*To).Sort))));
}

SMTExprRef Z3Solver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  SMTSortRef to = mkBVFPSort(Exp->Sort->getFPExponentWidth(),
                             Exp->Sort->getFPSignificandWidth());
  return newExprRef(Z3Expr(
      Context, to,
      z3::to_expr(*Context, Z3_mk_fpa_to_ieee_bv(
                                *Context, toSolverExpr<Z3Expr>(*Exp).Expr))));
}

SMTExprRef Z3Solver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                      const SMTExprRef &InitValue) {
  SMTSortRef sort = mkArraySort(IndexSort, InitValue->Sort);
  return newExprRef(
      Z3Expr(Context, sort,
             z3::const_array(toSolverSort<Z3Sort>(*IndexSort).Sort,
                             toSolverExpr<Z3Expr>(*InitValue).Expr)));
}

checkResult Z3Solver::checkImpl() {
  z3::check_result res = Solver.check();
  if (res == z3::check_result::sat)
    return checkResult::SAT;

  if (res == z3::check_result::unsat)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void Z3Solver::resetImpl() { Solver.reset(); }

std::string Z3Solver::getSolverNameAndVersion() const {
  unsigned int major, minor, build, revision;
  Z3_get_version(&major, &minor, &build, &revision);
  return std::string("Z3 v")
      .append(std::to_string(major))
      .append(".")
      .append(std::to_string(minor))
      .append(".")
      .append(std::to_string(revision));
}

void Z3Solver::dumpImpl() {
  std::cerr << Z3_solver_to_string(*Context, Solver) << '\n';
}

void Z3Solver::dumpModelImpl() {
  std::cerr << Z3_model_to_string(*Context, Solver.get_model()) << '\n';
}

} // namespace camada

#endif
