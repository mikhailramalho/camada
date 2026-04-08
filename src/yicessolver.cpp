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
#include <cstdio>
#include <gmp.h>

namespace camada {

namespace {

static inline void yicesCheckError(int32_t Res, const char *Message) {
  if (Res == 0)
    return;

  char *Err = yices_error_string();
  if (Err == nullptr)
    fatalError(Message);

  std::string FullMessage = std::string(Message) + ": " + Err;
  yices_free_string(Err);
  fatalError(FullMessage.c_str());
}

static inline context_t *yicesCheckContext(context_t *Ctx,
                                           const char *Message) {
  if (Ctx != nullptr)
    return Ctx;

  yicesCheckError(-1, Message);
  return nullptr;
}

static inline term_t yicesCheckTerm(term_t Term, const char *Message) {
  if (Term != NULL_TERM)
    return Term;

  yicesCheckError(-1, Message);
  return NULL_TERM;
}

} // namespace

unsigned YicesSort::getWidthFromSolver() const {
  if (yices_type_is_bool(Sort))
    return 1;

  if (yices_type_is_int(Sort) || yices_type_is_real(Sort))
    return 0;

  assert(yices_type_is_bitvector(Sort));
  return yices_bvtype_size(Sort);
}

void YicesSort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void YicesSort::dump(std::string &Out) const {
  char *ty_str = yices_type_to_string(Sort, 160, 80, 0);
  Out = ty_str;
  Out += "\n";
  yices_free_string(ty_str);
}

bool YicesExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return (Expr == static_cast<const YicesExpr &>(Other).Expr);
}

void YicesExpr::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void YicesExpr::dump(std::string &Out) const {
  char *term_str = yices_term_to_string(Expr, 160, 80, 0);
  Out = term_str;
  Out += "\n";
  yices_free_string(term_str);
}

YicesSolver::YicesSolver() : SMTSolverImpl() {
  yices_init();
  yices_clear_error();

  ctx_config_t *config = yices_new_config();
  yices_default_config_for_logic(config, "QF_AUFBV");

  Context = yicesCheckContext(yices_new_context(config),
                              "Could not create Yices context");
  yices_free_config(config);
  initializeCommonSingletons();
}

YicesSolver::~YicesSolver() {
  invalidateGeneratedObjects();
  if (Context)
    yices_free_context(Context);
  Context = nullptr;
  yices_exit();
}

void YicesSolver::addConstraintImpl(const SMTExprRef &Exp) {
  Assertions.push_back(Exp);
  yices_assert_formula(Context, toSolverExpr<YicesExpr>(*Exp).Expr);
}

SMTExprRef YicesSolver::newExprRefImpl(const SMTExpr &Exp) const {
  yicesCheckTerm(toSolverExpr<YicesExpr>(Exp).Expr,
                 "Error when creating Yices expr");
  return storeExprRef(toSolverExpr<YicesExpr>(Exp));
}

SMTExprRef YicesSolver::rewrapExprImpl(const SMTExpr &Exp,
                                       const SMTSortRef &Sort,
                                       SMTExprKind Kind) const {
  const auto &Wrapped = toSolverExpr<YicesExpr>(Exp);
  yicesCheckTerm(Wrapped.Expr, "Error when creating Yices expr");
  return storeExprRef(YicesExpr(Kind, Wrapped.Context, Sort, Wrapped.Expr));
}

SMTSortRef YicesSolver::mkBoolSortImpl() {
  return newSortRef<YicesSort>(YicesSort(SMTSortKind::Bool, Context,
                                         yices_bool_type(),
                                         SMTSort::ScalarSortData{1}));
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
  return newSortRef<YicesSort>(YicesSort(SMTSortKind::BV, Context,
                                         yices_bv_type(BitWidth),
                                         SMTSort::ScalarSortData{BitWidth}));
}

SMTSortRef YicesSolver::mkBVFPSortImpl(const unsigned ExpWidth,
                                       const unsigned SigWidth) {
  return newSortRef<YicesSort>(YicesSort(
      SMTSortKind::BVFP, Context, yices_bv_type(ExpWidth + SigWidth + 1),
      SMTSort::FPSortData{ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1}));
}

SMTSortRef YicesSolver::mkBVRMSortImpl() {
  return newSortRef<YicesSort>(YicesSort(SMTSortKind::BVRM, Context,
                                         yices_bv_type(3),
                                         SMTSort::ScalarSortData{3}));
}

SMTSortRef YicesSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                        const SMTSortRef &ElemSort) {
  return newSortRef<YicesSort>(
      YicesSort(SMTSortKind::Array, Context,
                yices_function_type1(toSolverSort<YicesSort>(*IndexSort).Sort,
                                     toSolverSort<YicesSort>(*ElemSort).Sort),
                SMTSort::ArraySortData{IndexSort, ElemSort}));
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
      SMTSort::FunctionSortData{DomainSorts, CodomainSort}));
}

SMTExprRef YicesSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVNeg, Context, Exp->Sort,
      yices_bvneg(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVNot, Context, Exp->Sort,
      yices_bvnot(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(SMTExprKind::Not, Context, Exp->Sort,
                                yices_not(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkArithNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithNeg, Context, Exp->Sort,
                                yices_neg(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkReal2IntImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::Real2Int, Context, mkIntSort(),
      yices_floor(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkIsIntImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::IsInt, Context, mkBoolSort(),
      yices_is_int_atom(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVAdd, Context, LHS->Sort,
      yices_bvadd(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSub, Context, LHS->Sort,
      yices_bvsub(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVMul, Context, LHS->Sort,
      yices_bvmul(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSRem, Context, LHS->Sort,
      yices_bvsrem(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVURem, Context, LHS->Sort,
      yices_bvrem(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSDiv, Context, LHS->Sort,
      yices_bvsdiv(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUDiv, Context, LHS->Sort,
      yices_bvdiv(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVShl, Context, LHS->Sort,
      yices_bvshl(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVAshr, Context, LHS->Sort,
      yices_bvashr(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVLshr, Context, LHS->Sort,
      yices_bvlshr(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVXor, Context, LHS->Sort,
      yices_bvxor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVOrImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVOr, Context, LHS->Sort,
      yices_bvor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVAnd, Context, LHS->Sort,
      yices_bvand2(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVXnorImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVXnor, Context, LHS->Sort,
      yices_bvxnor(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVNorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVNor, Context, LHS->Sort,
      yices_bvnor(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVNandImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVNand, Context, LHS->Sort,
      yices_bvnand(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUlt, Context, mkBoolSort(),
      yices_bvlt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSlt, Context, mkBoolSort(),
      yices_bvslt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                       toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUgtImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUgt, Context, mkBoolSort(),
      yices_bvgt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSgtImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSgt, Context, mkBoolSort(),
      yices_bvsgt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                       toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUle, Context, mkBoolSort(),
      yices_bvle_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSle, Context, mkBoolSort(),
      yices_bvsle_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                       toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUgeImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUge, Context, mkBoolSort(),
      yices_bvge_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSgeImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSge, Context, mkBoolSort(),
      yices_bvsge_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                       toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkImpliesImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::Implies, Context, mkBoolSort(),
      yices_implies(toSolverExpr<YicesExpr>(*LHS).Expr,
                    toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkAndImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::And, Context, mkBoolSort(),
                                yices_and2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::Or, Context, mkBoolSort(),
                                yices_or2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkXorImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::Xor, Context, mkBoolSort(),
                                yices_xor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithAddImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithAdd, Context, LHS->Sort,
                                yices_add(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithSubImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithSub, Context, LHS->Sort,
                                yices_sub(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithMulImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithMul, Context, LHS->Sort,
                                yices_mul(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithDiv, Context, LHS->Sort,
      yices_division(toSolverExpr<YicesExpr>(*LHS).Expr,
                     toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithLtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithLt, Context, mkBoolSort(),
      yices_arith_lt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithGtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithGt, Context, mkBoolSort(),
      yices_arith_gt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithLeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithLe, Context, mkBoolSort(),
      yices_arith_leq_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithGeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithGe, Context, mkBoolSort(),
      yices_arith_geq_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkEqualImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::Equal, Context, mkBoolSort(),
                                yices_eq(toSolverExpr<YicesExpr>(*LHS).Expr,
                                         toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVConcat, Context,
      mkBVSort(LHS->getWidth() + RHS->getWidth()),
      yices_bvconcat2(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithModImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithMod, Context, mkIntSort(),
                                yices_imod(toSolverExpr<YicesExpr>(*LHS).Expr,
                                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkInt2RealImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::Int2Real, Context, mkRealSort(),
      yices_division(toSolverExpr<YicesExpr>(*Exp).Expr,
                     toSolverExpr<YicesExpr>(*mkReal(1)).Expr));
}

SMTExprRef YicesSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                  const SMTExprRef &F) {
  return makeExprRef<YicesExpr>(SMTExprKind::Ite, Context, T->Sort,
                                yices_ite(toSolverExpr<YicesExpr>(*Cond).Expr,
                                          toSolverExpr<YicesExpr>(*T).Expr,
                                          toSolverExpr<YicesExpr>(*F).Expr));
}

SMTExprRef YicesSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSignExt, Context, mkBVSort(i + Exp->getWidth()),
      yices_sign_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i));
}

SMTExprRef YicesSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVZeroExt, Context, mkBVSort(i + Exp->getWidth()),
      yices_zero_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i));
}

SMTExprRef YicesSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                        const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVExtract, Context, mkBVSort(High - Low + 1),
      yices_bvextract(toSolverExpr<YicesExpr>(*Exp).Expr, Low, High));
}

SMTExprRef YicesSolver::mkBVRedOrImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVRedOr, Context, mkBVSort(1),
      yices_redor(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkBVRedAndImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVRedAnd, Context, mkBVSort(1),
      yices_redand(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                          const SMTExprRef &Index) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArraySelect, Context, Array->Sort->getElementSort(),
      yices_application1(toSolverExpr<YicesExpr>(*Array).Expr,
                         toSolverExpr<YicesExpr>(*Index).Expr));
}

SMTExprRef YicesSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index,
                                         const SMTExprRef &Element) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArrayStore, Context, Array->Sort,
      yices_update1(toSolverExpr<YicesExpr>(*Array).Expr,
                    toSolverExpr<YicesExpr>(*Index).Expr,
                    toSolverExpr<YicesExpr>(*Element).Expr));
}

SMTExprRef YicesSolver::mkApplyImpl(const SMTExprRef &Function,
                                    const std::vector<SMTExprRef> &Args) {
  std::vector<term_t> ApplyArgs;
  ApplyArgs.reserve(Args.size());
  for (const auto &Arg : Args)
    ApplyArgs.push_back(toSolverExpr<YicesExpr>(*Arg).Expr);
  return makeExprRef<YicesExpr>(
      SMTExprKind::Apply, Context, Function->Sort->getCodomainSort(),
      yices_application(toSolverExpr<YicesExpr>(*Function).Expr,
                        ApplyArgs.size(), ApplyArgs.data()));
}

bool YicesSolver::getBoolImpl(const SMTExprRef &Exp) {
  int32_t val;
  auto res = yices_get_bool_value(yices_get_model(Context, 1),
                                  toSolverExpr<YicesExpr>(*Exp).Expr, &val);
  yicesCheckError(res, "Can't get boolean value from Yices");
  return val ? true : false;
}

static inline void getYicesMPQValue(context_t *Context, term_t Expr,
                                    mpq_t Val) {
  auto res = yices_get_mpq_value(yices_get_model(Context, 1), Expr, Val);
  yicesCheckError(res, "Can't get rational value from Yices");
}

std::string YicesSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  unsigned width = Exp->getWidth();

  int32_t *data = new int32_t[width];
  auto res = yices_get_bv_value(yices_get_model(Context, 1),
                                toSolverExpr<YicesExpr>(*Exp).Expr, data);
  if (res != 0) {
    delete[] data;
    yicesCheckError(res, "Can't get bitvector value from Yices");
  }

  std::string val;
  for (unsigned i = 0; i < width; i++)
    val.append(std::to_string(data[width - i - 1]));

  delete[] data;
  return val;
}

std::string YicesSolver::getIntImpl(const SMTExprRef &Exp) {
  if (Exp->isRealSort()) {
    std::string Num, Den;
    getRationalImpl(Exp, Num, Den);
    assert(Den == "1" && "Real value is not integral");
    return Num;
  }

  int64_t val;
  auto res = yices_get_int64_value(yices_get_model(Context, 1),
                                   toSolverExpr<YicesExpr>(*Exp).Expr, &val);
  yicesCheckError(res, "Can't get integer value from Yices");
  return std::to_string(val);
}

void YicesSolver::getRationalImpl(const SMTExprRef &Exp, std::string &Num,
                                  std::string &Den) {
  mpq_t val;
  mpq_init(val);
  getYicesMPQValue(Context, toSolverExpr<YicesExpr>(*Exp).Expr, val);
  char *raw_num = mpz_get_str(nullptr, 10, mpq_numref(val));
  char *raw_den = mpz_get_str(nullptr, 10, mpq_denref(val));
  Num = raw_num;
  Den = raw_den;
  void (*gmp_free)(void *, std::size_t);
  mp_get_memory_functions(nullptr, nullptr, &gmp_free);
  gmp_free(raw_num, Num.size() + 1);
  gmp_free(raw_den, Den.size() + 1);
  mpq_clear(val);
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
  return SMTSolverImpl::mkFPFromBin(
      getFPInBin(sel), elementSort->getFPExponentWidth(), FPEncoding::BV);
}

SMTExprRef YicesSolver::mkBoolImpl(const bool b) {
  return makeExprRef<YicesExpr>(SMTExprKind::BoolConst, Context, mkBoolSort(),
                                b ? yices_true() : yices_false());
}

SMTExprRef YicesSolver::mkIntImpl(int64_t v) {
  return makeExprRef<YicesExpr>(SMTExprKind::IntConst, Context, mkIntSort(),
                                yices_int64(v));
}

SMTExprRef YicesSolver::mkIntImpl(const std::string &v) {
  mpz_t val;
  mpz_init_set_str(val, v.c_str(), 10);
  term_t term = yices_mpz(val);
  mpz_clear(val);
  return makeExprRef<YicesExpr>(SMTExprKind::IntConst, Context, mkIntSort(),
                                term);
}

SMTExprRef YicesSolver::mkRealImpl(const std::string &v) {
  return makeExprRef<YicesExpr>(SMTExprKind::RealConst, Context, mkRealSort(),
                                yices_parse_rational(v.c_str()));
}

SMTExprRef YicesSolver::mkRealImpl(int64_t v) {
  return mkRealImpl(std::to_string(v));
}

SMTExprRef YicesSolver::mkRealImpl(int64_t num, int64_t den) {
  return mkRealImpl(std::to_string(num) + "/" + std::to_string(den));
}

SMTExprRef YicesSolver::mkBVFromDecImpl(const int64_t Int,
                                        const SMTSortRef &Sort) {
  return makeExprRef<YicesExpr>(SMTExprKind::BVConst, Context, Sort,
                                yices_bvconst_int64(Sort->getWidth(), Int));
}

SMTExprRef YicesSolver::mkBVFromBinImpl(const std::string &Int,
                                        const SMTSortRef &Sort) {
  return makeExprRef<YicesExpr>(SMTExprKind::BVConst, Context, Sort,
                                yices_parse_bvbin(Int.c_str()));
}

SMTExprRef YicesSolver::mkSymbolImpl(const std::string &Name,
                                     const SMTSortRef &Sort) {
  // We could use yices_get_term_by_name to check if the variable was already
  // created, but the we would need to create a new SMTExprRef, so use
  // this map instead
  auto it = SymbolTable.find(Name);
  if (it != SymbolTable.end())
    return it->second;

  if (yices_get_term_by_name(Name.c_str()) != NULL_TERM)
    fatalError("Trying to create a symbol but it already exists");

  term_t t = yicesCheckTerm(
      yices_new_uninterpreted_term(toSolverSort<YicesSort>(*Sort).Sort),
      "Error when trying to create a new Yices symbol");

  yicesCheckError(yices_set_term_name(t, Name.c_str()),
                  "Error when trying to set Yices symbol name");

  auto inserted = SymbolTable.insert(SymbolTablet::value_type(
      Name, makeExprRef<YicesExpr>(SMTExprKind::Symbol, Context, Sort, t)));

  assert(inserted.second && "Could not cache new Yices variable");
  return inserted.first->second;
}

SMTExprRef YicesSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                         const SMTExprRef &InitValue) {
  const SMTSortRef &sort = mkArraySort(IndexSort, InitValue->Sort);
  term_t index_var = yicesCheckTerm(
      yices_new_variable(toSolverSort<YicesSort>(*IndexSort).Sort),
      "Error when trying to create a Yices lambda variable");
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArrayConst, Context, sort,
      yicesCheckTerm(
          yices_lambda(1, &index_var, toSolverExpr<YicesExpr>(*InitValue).Expr),
          "Error when trying to create a Yices lambda"));
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
  if (Context)
    yices_free_context(Context);
  Context = nullptr;
  yices_exit();

  // and recreate
  yices_init();
  yices_clear_error();

  ctx_config_t *config = yices_new_config();
  yices_default_config_for_logic(config, "QF_AUFBV");

  Context = yicesCheckContext(yices_new_context(config),
                              "Could not create Yices context");
  yices_free_config(config);
}

void YicesSolver::pushImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i) {
    AssertionScopeSizes.push_back(Assertions.size());
    yicesCheckError(yices_push(Context), "Could not push Yices context");
  }
}

void YicesSolver::popImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i) {
    assert(!AssertionScopeSizes.empty() && "Could not pop empty Yices scope");
    yicesCheckError(yices_pop(Context), "Could not pop Yices context");
    Assertions.resize(AssertionScopeSizes.back());
    AssertionScopeSizes.pop_back();
  }
}

std::string YicesSolver::getSolverNameAndVersion() const {
  return std::string("Yices v").append(yices_version);
}

void YicesSolver::dumpImpl() {
  std::string Out;
  dumpImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void YicesSolver::dumpImpl(std::string &Out) {
  Out.clear();
  for (auto const &a : Assertions) {
    std::string Assertion;
    a->dump(Assertion);
    Out += Assertion;
  }
}

void YicesSolver::dumpModelImpl() {
  std::string Out;
  dumpModelImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void YicesSolver::dumpModelImpl(std::string &Out) {
  char *model_str =
      yices_model_to_string(yices_get_model(Context, 1), 160, 80, 0);
  Out = model_str;
  Out += "\n";
  yices_free_string(model_str);
}

} // namespace camada

#endif
