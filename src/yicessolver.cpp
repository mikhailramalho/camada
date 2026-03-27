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
#if SOLVER_YICES_ENABLED

#include "yicessolver.h"

#include <cassert>
#include <iostream>

namespace camada {

void YicesContextDeleter::operator()(context_t *Ctx) const {
  if (Ctx)
    yices_free_context(Ctx);
}

unsigned YicesSort::getWidthFromSolver() const {
  if (yices_type_is_bool(Sort))
    return 1;

  if (yices_type_is_int(Sort) || yices_type_is_real(Sort))
    return 0;

  assert(yices_type_is_bitvector(Sort));
  return yices_bvtype_size(Sort);
}

void YicesSort::dump() const {
  char *ty_str = yices_type_to_string(Sort, 160, 80, 0);
  std::cerr << ty_str << '\n';
  yices_free_string(ty_str);
}

bool YicesExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return (Expr == static_cast<const YicesExpr &>(Other).Expr);
}

void YicesExpr::dump() const {
  char *term_str = yices_term_to_string(Expr, 160, 80, 0);
  std::cerr << term_str << '\n';
  yices_free_string(term_str);
}

YicesSolver::YicesSolver() : SMTSolverImpl() {
  yices_init();
  yices_clear_error();

  ctx_config_t *config = yices_new_config();
  yices_default_config_for_logic(config, "QF_AUFBV");

  OwnedContext.reset(yices_new_context(config));
  Context = OwnedContext.get();
  yices_free_config(config);
  initializeCommonSingletons();
}

YicesSolver::~YicesSolver() {
  invalidateGeneratedObjects();
  OwnedContext.reset();
  Context = nullptr;
  yices_exit();
}

void YicesSolver::addConstraintImpl(const SMTExprRef &Exp) {
  Assertions.push_back(Exp);
  yices_assert_formula(Context, toSolverExpr<YicesExpr>(*Exp).Expr);
}

SMTExprRef YicesSolver::newExprRefImpl(const SMTExpr &Exp) const {
  assert(toSolverExpr<YicesExpr>(Exp).Expr != NULL_TERM &&
         "Error when creating Yices expr.");
  return storeExprRef(toSolverExpr<YicesExpr>(Exp));
}

SMTExprRef YicesSolver::cloneExprWithSortImpl(const SMTExpr &Exp,
                                              const SMTSortRef &Sort) const {
  assert(toSolverExpr<YicesExpr>(Exp).Expr != NULL_TERM &&
         "Error when creating Yices expr.");
  YicesExpr Retagged = toSolverExpr<YicesExpr>(Exp);
  Retagged.Sort = Sort;
  return storeExprRef(Retagged);
}

SMTSortRef YicesSolver::mkBoolSortImpl() {
  return newSortRef<YicesSort>(
      YicesSort(SMTSortKind::Bool, Context, yices_bool_type(), 1));
}

SMTSortRef YicesSolver::mkIntSortImpl() {
  return newSortRef<YicesSort>(
      YicesSort(SMTSortKind::Int, Context, yices_int_type()));
}

SMTSortRef YicesSolver::mkRealSortImpl() {
  return newSortRef<YicesSort>(
      YicesSort(SMTSortKind::Real, Context, yices_real_type()));
}

SMTSortRef YicesSolver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<YicesSort>(
      YicesSort(SMTSortKind::BV, Context, yices_bv_type(BitWidth), BitWidth));
}

SMTSortRef YicesSolver::mkBVFPSortImpl(const unsigned ExpWidth,
                                       const unsigned SigWidth) {
  return newSortRef<YicesSort>(YicesSort(
      SMTSortKind::BVFP, Context, yices_bv_type(ExpWidth + SigWidth + 1),
      ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1));
}

SMTSortRef YicesSolver::mkBVRMSortImpl() {
  return newSortRef<YicesSort>(
      YicesSort(SMTSortKind::BVRM, Context, yices_bv_type(3), 3));
}

SMTSortRef YicesSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                        const SMTSortRef &ElemSort) {
  return newSortRef<YicesSort>(
      YicesSort(SMTSortKind::Array, Context,
                yices_function_type1(toSolverSort<YicesSort>(*IndexSort).Sort,
                                     toSolverSort<YicesSort>(*ElemSort).Sort),
                0, 0, 0, IndexSort, ElemSort));
}

SMTSortRef
YicesSolver::mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                                const SMTSortRef &CodomainSort) {
  std::vector<type_t> Domain;
  Domain.reserve(DomainSorts.size());
  for (const auto &Sort : DomainSorts)
    Domain.push_back(toSolverSort<YicesSort>(*Sort).Sort);
  return newSortRef<YicesSort>(YicesSort(
      SMTSortKind::Function, Context,
      yices_function_type(Domain.size(), Domain.data(),
                          toSolverSort<YicesSort>(*CodomainSort).Sort),
      0, 0, 0, {}, {}, DomainSorts, CodomainSort));
}

SMTExprRef YicesSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, Exp->Sort,
                              yices_bvneg(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, Exp->Sort,
                              yices_bvnot(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkNotImpl(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, Exp->Sort,
                              yices_not(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvadd(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvsub(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvmul(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvsrem(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvrem(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvsdiv(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvdiv(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvshl(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvashr(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvlshr(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvxor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVOrImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvand2(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVXnorImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvxnor(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVNorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, LHS->Sort,
                              yices_bvnor(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVNandImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, LHS->Sort,
                yices_bvnand(toSolverExpr<YicesExpr>(*LHS).Expr,
                             toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_bvlt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_bvslt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                 toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUgtImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_bvgt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSgtImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_bvsgt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                 toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_bvle_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_bvsle_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                 toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVUgeImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_bvge_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVSgeImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_bvsge_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                                 toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkImpliesImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(),
                yices_implies(toSolverExpr<YicesExpr>(*LHS).Expr,
                              toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkAndImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, mkBoolSort(),
                              yices_and2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                         toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, mkBoolSort(),
                              yices_or2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                        toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkXorImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, mkBoolSort(),
                              yices_xor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                         toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArithNegImpl(const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, Exp->Sort, yices_neg(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkArithAddImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, LHS->Sort,
      yices_add(toSolverExpr<YicesExpr>(*LHS).Expr,
                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArithSubImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, LHS->Sort,
      yices_sub(toSolverExpr<YicesExpr>(*LHS).Expr,
                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArithMulImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, LHS->Sort,
      yices_mul(toSolverExpr<YicesExpr>(*LHS).Expr,
                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArithDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, LHS->Sort,
      yices_division(toSolverExpr<YicesExpr>(*LHS).Expr,
                     toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArithLtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, mkBoolSort(),
      yices_arith_lt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArithGtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, mkBoolSort(),
      yices_arith_gt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                          toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArithLeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, mkBoolSort(),
      yices_arith_leq_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                           toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkArithGeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(
      Context, mkBoolSort(),
      yices_arith_geq_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                           toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkEqualImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(YicesExpr(Context, mkBoolSort(),
                              yices_eq(toSolverExpr<YicesExpr>(*LHS).Expr,
                                       toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                  const SMTExprRef &F) {
  return newExprRef(YicesExpr(Context, T->Sort,
                              yices_ite(toSolverExpr<YicesExpr>(*Cond).Expr,
                                        toSolverExpr<YicesExpr>(*T).Expr,
                                        toSolverExpr<YicesExpr>(*F).Expr)));
}

SMTExprRef YicesSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, mkBVSort(i + Exp->getWidth()),
                yices_sign_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i)));
}

SMTExprRef YicesSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      YicesExpr(Context, mkBVSort(i + Exp->getWidth()),
                yices_zero_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i)));
}

SMTExprRef YicesSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                        const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(
      Context, mkBVSort(High - Low + 1),
      yices_bvextract(toSolverExpr<YicesExpr>(*Exp).Expr, Low, High)));
}

SMTExprRef YicesSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(
      YicesExpr(Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
                yices_bvconcat2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                toSolverExpr<YicesExpr>(*RHS).Expr)));
}

SMTExprRef YicesSolver::mkBVRedOrImpl(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(Context, mkBVSort(1),
                              yices_redor(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkBVRedAndImpl(const SMTExprRef &Exp) {
  return newExprRef(YicesExpr(
      Context, mkBVSort(1), yices_redand(toSolverExpr<YicesExpr>(*Exp).Expr)));
}

SMTExprRef YicesSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                          const SMTExprRef &Index) {
  return newExprRef(
      YicesExpr(Context, Array->Sort->getElementSort(),
                yices_application1(toSolverExpr<YicesExpr>(*Array).Expr,
                                   toSolverExpr<YicesExpr>(*Index).Expr)));
}

SMTExprRef YicesSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index,
                                         const SMTExprRef &Element) {
  return newExprRef(
      YicesExpr(Context, Array->Sort,
                yices_update1(toSolverExpr<YicesExpr>(*Array).Expr,
                              toSolverExpr<YicesExpr>(*Index).Expr,
                              toSolverExpr<YicesExpr>(*Element).Expr)));
}

SMTExprRef YicesSolver::mkApplyImpl(const SMTExprRef &Function,
                                    const std::vector<SMTExprRef> &Args) {
  std::vector<term_t> ApplyArgs;
  ApplyArgs.reserve(Args.size());
  for (const auto &Arg : Args)
    ApplyArgs.push_back(toSolverExpr<YicesExpr>(*Arg).Expr);
  return newExprRef(
      YicesExpr(Context, Function->Sort->getCodomainSort(),
                yices_application(toSolverExpr<YicesExpr>(*Function).Expr,
                                  ApplyArgs.size(), ApplyArgs.data())));
}

bool YicesSolver::getBoolImpl(const SMTExprRef &Exp) {
  int32_t val;
  auto res = yices_get_bool_value(yices_get_model(Context, 1),
                                  toSolverExpr<YicesExpr>(*Exp).Expr, &val);
  (void)res;
  assert(!res && "Can't get boolean value from Yices");
  return val ? true : false;
}

std::string YicesSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  unsigned width = Exp->getWidth();

  int32_t *data = new int32_t[width];
  auto res = yices_get_bv_value(yices_get_model(Context, 1),
                                toSolverExpr<YicesExpr>(*Exp).Expr, data);
  (void)res;
  assert(!res && "Can't get boolean value from Yices");

  std::string val;
  for (unsigned i = 0; i < width; i++)
    val.append(std::to_string(data[width - i - 1]));

  delete[] data;
  return val;
}

SMTExprRef YicesSolver::getArrayElementImpl(const SMTExprRef &Array,
                                            const SMTExprRef &Index) {
  const SMTExprRef &sel = mkArraySelect(Array, Index);

  const SMTSortRef &elementSort = Array->Sort->getElementSort();
  if (elementSort->isBoolSort())
    return mkBool(getBool(sel));

  if (elementSort->isBVSort())
    return SMTSolverImpl::mkBVFromBin(getBVInBin(sel));

  assert(elementSort->isFPSort() && "Unknown array element type");
  return SMTSolverImpl::mkFPFromBin(getFPInBin(sel),
                                    elementSort->getFPExponentWidth());
}

SMTExprRef YicesSolver::mkBoolImpl(const bool b) {
  return newExprRef(
      YicesExpr(Context, mkBoolSort(), b ? yices_true() : yices_false()));
}

SMTExprRef YicesSolver::mkIntImpl(int64_t v) {
  return newExprRef(YicesExpr(Context, mkIntSort(), yices_int64(v)));
}

SMTExprRef YicesSolver::mkRealImpl(const std::string &v) {
  return newExprRef(
      YicesExpr(Context, mkRealSort(), yices_parse_rational(v.c_str())));
}

SMTExprRef YicesSolver::mkRealImpl(int64_t v) {
  return mkRealImpl(std::to_string(v));
}

SMTExprRef YicesSolver::mkRealImpl(int64_t num, int64_t den) {
  return mkRealImpl(std::to_string(num) + "/" + std::to_string(den));
}

SMTExprRef YicesSolver::mkBVFromDecImpl(const int64_t Int,
                                        const SMTSortRef &Sort) {
  return newExprRef(
      YicesExpr(Context, Sort, yices_bvconst_int64(Sort->getWidth(), Int)));
}

SMTExprRef YicesSolver::mkBVFromBinImpl(const std::string &Int,
                                        const SMTSortRef &Sort) {
  return newExprRef(YicesExpr(Context, Sort, yices_parse_bvbin(Int.c_str())));
}

SMTExprRef YicesSolver::mkSymbolImpl(const std::string &Name,
                                     const SMTSortRef &Sort) {
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

SMTExprRef YicesSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                         const SMTExprRef &InitValue) {
  const SMTSortRef &sort = mkArraySort(IndexSort, InitValue->Sort);
  term_t index_var =
      yices_new_variable(toSolverSort<YicesSort>(*IndexSort).Sort);
  return newExprRef(YicesExpr(
      Context, sort,
      yices_lambda(1, &index_var, toSolverExpr<YicesExpr>(*InitValue).Expr)));
}

SMTExprRef YicesSolver::mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                     const SMTExprRef &Body) {
  (void)Vars;
  (void)Body;
  std::cerr << "Quantifiers are not supported by the Yices backend\n";
  std::abort();
}

SMTExprRef YicesSolver::mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                     const SMTExprRef &Body) {
  (void)Vars;
  (void)Body;
  std::cerr << "Quantifiers are not supported by the Yices backend\n";
  std::abort();
}

checkResult YicesSolver::checkImpl() {
  smt_status_t res = yices_check_context(Context, nullptr);
  if (res == YICES_STATUS_SAT)
    return checkResult::SAT;

  if (res == YICES_STATUS_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void YicesSolver::resetImpl() {
  SymbolTable.clear();
  Assertions.clear();
  AssertionScopeSizes.clear();

  // Delete
  OwnedContext.reset();
  Context = nullptr;
  yices_exit();

  // and recreate
  yices_init();
  yices_clear_error();

  ctx_config_t *config = yices_new_config();
  yices_default_config_for_logic(config, "QF_AUFBV");

  OwnedContext.reset(yices_new_context(config));
  Context = OwnedContext.get();
  yices_free_config(config);
}

void YicesSolver::pushImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i) {
    AssertionScopeSizes.push_back(Assertions.size());
    int32_t res = yices_push(Context);
    assert(!res && "Could not push Yices context");
  }
}

void YicesSolver::popImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i) {
    assert(!AssertionScopeSizes.empty() && "Could not pop empty Yices scope");
    int32_t res = yices_pop(Context);
    assert(!res && "Could not pop Yices context");
    Assertions.resize(AssertionScopeSizes.back());
    AssertionScopeSizes.pop_back();
  }
}

std::string YicesSolver::getSolverNameAndVersion() const {
  return std::string("Yices v").append(yices_version);
}

void YicesSolver::dumpImpl() {
  for (auto const &a : Assertions)
    a->dump();
}

void YicesSolver::dumpModelImpl() {
  char *model_str =
      yices_model_to_string(yices_get_model(Context, 1), 160, 80, 0);
  std::cerr << model_str << '\n';
  yices_free_string(model_str);
}

} // namespace camada

#endif
