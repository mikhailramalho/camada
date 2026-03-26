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

#include <iostream>

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

void Z3Sort::dump() const { std::cerr << Sort << '\n'; }

bool Z3Expr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return z3::eq(Expr, static_cast<const Z3Expr &>(Other).Expr);
}

void Z3Expr::dump() const { std::cerr << Expr << '\n'; }

Z3Solver::Z3Solver()
    : SMTSolverImpl(), OwnedContext(std::make_unique<z3::context>()),
      Context(OwnedContext.get()), Solver(*Context) {
  // Needs to be set in order to convert NaN to bitvector
  z3::set_param("rewriter.hi_fp_unspecified", true);
  initializeCommonSingletons();
}

Z3Solver::Z3Solver(std::unique_ptr<z3::context> C)
    : SMTSolverImpl(), OwnedContext(std::move(C)), Context(OwnedContext.get()),
      Solver(*Context) {
  z3::set_param("rewriter.hi_fp_unspecified", true);
  initializeCommonSingletons();
}

Z3Solver::Z3Solver(std::unique_ptr<z3::context> C, z3::solver S)
    : SMTSolverImpl(), OwnedContext(std::move(C)), Context(OwnedContext.get()),
      Solver(std::move(S)) {
  // Needs to be set in order to convert NaN to bitvector
  z3::set_param("rewriter.hi_fp_unspecified", true);
  initializeCommonSingletons();
}

Z3Solver::~Z3Solver() { invalidateGeneratedObjects(); }

void Z3Solver::addConstraintImpl(const SMTExprRef &Exp) {
  Solver.add(toSolverExpr<Z3Expr>(*Exp).Expr);
}

SMTExprRef Z3Solver::newExprRefImpl(const SMTExpr &Exp) const {
  return storeExprRef(toSolverExpr<Z3Expr>(Exp));
}

SMTExprRef Z3Solver::cloneExprWithSortImpl(const SMTExpr &Exp,
                                           const SMTSortRef &Sort) const {
  Z3Expr Retagged = toSolverExpr<Z3Expr>(Exp);
  Retagged.Sort = Sort;
  return storeExprRef(Retagged);
}

SMTSortRef Z3Solver::mkBoolSortImpl() {
  return newSortRef<Z3Sort>(
      Z3Sort(SMTSortKind::Bool, Context, Context->bool_sort(), 1));
}

SMTSortRef Z3Solver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<Z3Sort>(
      Z3Sort(SMTSortKind::BV, Context, Context->bv_sort(BitWidth), BitWidth));
}

SMTSortRef Z3Solver::mkRMSortImpl() {
  return newSortRef<Z3Sort>(
      Z3Sort(SMTSortKind::RM, Context, Context->fpa_rounding_mode_sort(), 3));
}

SMTSortRef Z3Solver::mkFPSortImpl(const unsigned ExpWidth,
                                  const unsigned SigWidth) {
  return newSortRef<Z3Sort>(Z3Sort(
      SMTSortKind::FP, Context, Context->fpa_sort(ExpWidth, SigWidth + 1),
      ExpWidth + SigWidth + 1, ExpWidth, SigWidth));
}

SMTSortRef Z3Solver::mkBVFPSortImpl(const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  return newSortRef<Z3Sort>(Z3Sort(
      SMTSortKind::BVFP, Context, Context->bv_sort(ExpWidth + SigWidth + 1),
      ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1));
}

SMTSortRef Z3Solver::mkBVRMSortImpl() {
  return newSortRef<Z3Sort>(
      Z3Sort(SMTSortKind::BVRM, Context, Context->bv_sort(3), 3));
}

SMTSortRef Z3Solver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                     const SMTSortRef &ElemSort) {
  return newSortRef<Z3Sort>(
      Z3Sort(SMTSortKind::Array, Context,
             Context->array_sort(toSolverSort<Z3Sort>(*IndexSort).Sort,
                                 toSolverSort<Z3Sort>(*ElemSort).Sort),
             0, 0, 0, IndexSort, ElemSort));
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

SMTExprRef Z3Solver::mkBVXnorImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::xnor(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVNorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::nor(toSolverExpr<Z3Expr>(*LHS).Expr,
                                   toSolverExpr<Z3Expr>(*RHS).Expr)));
}

SMTExprRef Z3Solver::mkBVNandImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           z3::nand(toSolverExpr<Z3Expr>(*LHS).Expr,
                                    toSolverExpr<Z3Expr>(*RHS).Expr)));
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

SMTExprRef Z3Solver::mkImpliesImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           z3::implies(toSolverExpr<Z3Expr>(*LHS).Expr,
                                       toSolverExpr<Z3Expr>(*RHS).Expr)));
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
  return newExprRef(Z3Expr(Context, LHS->Sort,
                           toSolverExpr<Z3Expr>(*LHS).Expr ^
                               toSolverExpr<Z3Expr>(*RHS).Expr));
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
  return newExprRef(Z3Expr(Context, mkBVSort(1),
                           z3::bvredor(toSolverExpr<Z3Expr>(*Exp).Expr)));
}

SMTExprRef Z3Solver::mkBVRedAndImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBVSort(1),
                           z3::bvredand(toSolverExpr<Z3Expr>(*Exp).Expr)));
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
  return newExprRef(
      Z3Expr(Context, Exp->Sort, z3::abs(toSolverExpr<Z3Expr>(*Exp).Expr)));
}

SMTExprRef Z3Solver::mkFPNegImpl(const SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Exp->Sort, -toSolverExpr<Z3Expr>(*Exp).Expr));
}

SMTExprRef Z3Solver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*Exp).Expr.mk_is_inf()));
}

SMTExprRef Z3Solver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*Exp).Expr.mk_is_nan()));
}

SMTExprRef Z3Solver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*Exp).Expr.mk_is_subnormal()));
}

SMTExprRef Z3Solver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*Exp).Expr.mk_is_normal()));
}

SMTExprRef Z3Solver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           toSolverExpr<Z3Expr>(*Exp).Expr.mk_is_zero()));
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
  return newExprRef(Z3Expr(Context, Exp->Sort,
                           z3::sqrt(toSolverExpr<Z3Expr>(*Exp).Expr,
                                    toSolverExpr<Z3Expr>(*R).Expr)));
}

SMTExprRef Z3Solver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                 const SMTExprRef &Z, const SMTExprRef &R) {
  return newExprRef(Z3Expr(
      Context, X->Sort,
      z3::fma(toSolverExpr<Z3Expr>(*X).Expr, toSolverExpr<Z3Expr>(*Y).Expr,
              toSolverExpr<Z3Expr>(*Z).Expr, toSolverExpr<Z3Expr>(*R).Expr)));
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
  return newExprRef(Z3Expr(Context, mkBoolSort(),
                           z3::fp_eq(toSolverExpr<Z3Expr>(*LHS).Expr,
                                     toSolverExpr<Z3Expr>(*RHS).Expr)));
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
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO);
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
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO);
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
  switch (toSolverExpr<Z3Expr>(*Exp).Expr.bool_value()) {
  case Z3_L_TRUE:
    return true;
  case Z3_L_FALSE:
    return false;
  case Z3_L_UNDEF:
    break;
  }
  assert(0 && "Bool is neither true nor false");
  __builtin_unreachable();
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
  const SMTExprRef &value =
      hasZ3Interp(*this, Exp) ? getZ3Interp(*this, Exp) : Exp;
  std::string bv;
  bool is_num = toSolverExpr<Z3Expr>(*value).Expr.as_binary(bv);
  (void)is_num;
  assert(is_num && "Failed to get bitvector from Z3");
  return bv;
}

std::string Z3Solver::getFPInBinImpl(const SMTExprRef &Exp) {
  const SMTExprRef &value =
      hasZ3Interp(*this, Exp) ? getZ3Interp(*this, Exp) : Exp;

  // Convert the float to bv
  z3::expr fp_value = Solver.get_model().eval(
      toSolverExpr<Z3Expr>(*value).Expr.mk_to_ieee_bv(), true);
  std::string bv;
  bool is_num = fp_value.as_binary(bv);
  (void)is_num;
  assert(is_num && "Failed to convert FP to BV in Z3");
  return bv;
}

SMTExprRef Z3Solver::getArrayElementImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index) {
  const SMTExprRef &sel = mkArraySelect(Array, Index);
  return newExprRef(
      Z3Expr(Context, sel->Sort,
             Solver.get_model().eval(toSolverExpr<Z3Expr>(*sel).Expr, true)));
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

  const SMTExprRef &bv =
      newExprRef(Z3Expr(Context, Sort, Context->bv_val(s, newInt)));
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
  const SMTExprRef &sgn = SMTSolverImpl::mkBVFromBin({FP[0]});
  const SMTExprRef &exp = SMTSolverImpl::mkBVFromBin(FP.substr(1, EWidth));
  const SMTExprRef &sig = SMTSolverImpl::mkBVFromBin(FP.substr(1 + EWidth));

  return newExprRef(Z3Expr(Context, mkFPSort(EWidth, FP.length() - EWidth - 1),
                           z3::fpa_fp(toSolverExpr<Z3Expr>(*sgn).Expr,
                                      toSolverExpr<Z3Expr>(*exp).Expr,
                                      toSolverExpr<Z3Expr>(*sig).Expr)));
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
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1);
  const SMTExprRef &theNaN = newExprRef(Z3Expr(
      Context, sort, Context->fpa_nan(toSolverSort<Z3Sort>(*sort).Sort)));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef Z3Solver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1);
  return newExprRef(Z3Expr(
      Context, sort, Context->fpa_inf(toSolverSort<Z3Sort>(*sort).Sort, Sgn)));
}

SMTExprRef Z3Solver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                      const SMTSortRef &To) {
  return newExprRef(Z3Expr(Context, To,
                           toSolverExpr<Z3Expr>(*Exp).Expr.mk_from_ieee_bv(
                               toSolverSort<Z3Sort>(*To).Sort)));
}

SMTExprRef Z3Solver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  const SMTSortRef &to = mkBVFPSort(Exp->Sort->getFPExponentWidth(),
                                    Exp->Sort->getFPSignificandWidth());
  return newExprRef(
      Z3Expr(Context, to, toSolverExpr<Z3Expr>(*Exp).Expr.mk_to_ieee_bv()));
}

SMTExprRef Z3Solver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                      const SMTExprRef &InitValue) {
  const SMTSortRef &sort = mkArraySort(IndexSort, InitValue->Sort);
  return newExprRef(
      Z3Expr(Context, sort,
             z3::const_array(toSolverSort<Z3Sort>(*IndexSort).Sort,
                             toSolverExpr<Z3Expr>(*InitValue).Expr)));
}

SMTExprRef Z3Solver::mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                  const SMTExprRef &Body) {
  z3::expr_vector bound_vars(*Context);
  for (auto const &Var : Vars)
    bound_vars.push_back(toSolverExpr<Z3Expr>(*Var).Expr);
  return newExprRef(
      Z3Expr(Context, mkBoolSort(),
             z3::forall(bound_vars, toSolverExpr<Z3Expr>(*Body).Expr)));
}

SMTExprRef Z3Solver::mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                  const SMTExprRef &Body) {
  z3::expr_vector bound_vars(*Context);
  for (auto const &Var : Vars)
    bound_vars.push_back(toSolverExpr<Z3Expr>(*Var).Expr);
  return newExprRef(
      Z3Expr(Context, mkBoolSort(),
             z3::exists(bound_vars, toSolverExpr<Z3Expr>(*Body).Expr)));
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

void Z3Solver::pushImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i)
    Solver.push();
}

void Z3Solver::popImpl(unsigned nscopes) { Solver.pop(nscopes); }

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

void Z3Solver::dumpImpl() { std::cerr << Solver << '\n'; }

void Z3Solver::dumpModelImpl() { std::cerr << Solver.get_model() << '\n'; }

} // namespace camada

#endif
