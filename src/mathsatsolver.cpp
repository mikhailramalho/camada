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
#ifdef SOLVER_MATHSAT_ENABLED

#include "mathsatsolver.h"

#include <cassert>
#include <gmp.h>
#include <iostream>

namespace camada {

unsigned MathSATSort::getWidthFromSolver() const {
  std::size_t w;
  if (msat_is_bv_type(*Context, Sort, &w))
    return w;

  std::size_t exp, sig;
  int isFP = msat_is_fp_type(*Context, Sort, &exp, &sig);
  assert(isFP);
  (void)isFP;
  return 1 + exp + sig;
}

void MathSATSort::dump() const {
  char *s = msat_type_repr(Sort);
  std::cerr << s << '\n';
  msat_free(s);
}

bool MathSATExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
  return (msat_term_id(Expr) ==
          msat_term_id(dynamic_cast<const MathSATExpr &>(Other).Expr));
}

void MathSATExpr::dump() const {
  char *ast = msat_to_smtlib2(*Context, Expr);
  std::cerr << ast << '\n';
  msat_free(ast);
}

MathSATSolver::MathSATSolver() {
  msat_config cfg = msat_create_config();
  msat_set_option(cfg, "model_generation", "true");
  Context = std::make_shared<msat_env>(msat_create_env(cfg));
  msat_destroy_config(cfg);
}

MathSATSolver::MathSATSolver(const msat_config &Config)
    : Context(std::make_shared<msat_env>(msat_create_env(Config))) {}

MathSATSolver::~MathSATSolver() {
  msat_destroy_env(*Context);
  Context = nullptr;
}

void MathSATSolver::addConstraintImpl(const SMTExprRef &Exp) {
  msat_assert_formula(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr);
}

static inline bool checkExprError(const SMTExpr &Exp) {
  auto const &exp = toSolverExpr<MathSATExpr>(Exp);
  if (MSAT_ERROR_TERM(exp.Expr)) {
    std::cerr << "MathSAT Error " << msat_last_error_message(*exp.Context)
              << '\n';
    return true;
  }
  return false;
}

SMTExprRef MathSATSolver::newExprRefImpl(const SMTExpr &Exp) const {
  assert(!checkExprError(Exp) && "Error when creating MathSAT expr.");
  return std::make_shared<MathSATExpr>(toSolverExpr<MathSATExpr>(Exp));
}

SMTSortRef MathSATSolver::mkBoolSortImpl() {
  return newSortRef<SolverBoolSort<MathSATSort>>(
      {Context, msat_get_bool_type(*Context)});
}

SMTSortRef MathSATSolver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<SolverBVSort<MathSATSort>>(
      {BitWidth, Context, msat_get_bv_type(*Context, BitWidth)});
}

SMTSortRef MathSATSolver::mkRMSortImpl() {
  return newSortRef<SolverRMSort<MathSATSort>>(
      {Context, msat_get_fp_roundingmode_type(*Context)});
}

SMTSortRef MathSATSolver::mkFPSortImpl(const unsigned ExpWidth,
                                       const unsigned SigWidth) {
  return newSortRef<SolverFPSort<MathSATSort>>(
      {ExpWidth, SigWidth + 1, Context,
       msat_get_fp_type(*Context, ExpWidth, SigWidth)});
}

SMTSortRef MathSATSolver::mkBVFPSortImpl(const unsigned ExpWidth,
                                         const unsigned SigWidth) {
  return newSortRef<SolverBVFPSort<MathSATSort>>(
      {ExpWidth, SigWidth, Context,
       msat_get_bv_type(*Context, ExpWidth + SigWidth + 1)});
}

SMTSortRef MathSATSolver::mkBVRMSortImpl() {
  return newSortRef<SolverBVRMSort<MathSATSort>>(
      {Context, msat_get_bv_type(*Context, 3)});
}

SMTSortRef MathSATSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                          const SMTSortRef &ElemSort) {
  return newSortRef<SolverArraySort<MathSATSort>>(
      {IndexSort, ElemSort, Context,
       msat_get_array_type(*Context, toSolverSort<MathSATSort>(*IndexSort).Sort,
                           toSolverSort<MathSATSort>(*ElemSort).Sort)});
}

SMTExprRef MathSATSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_bv_neg(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_bv_not(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkNotImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_not(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_plus(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_minus(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                         toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_times(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                      toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_srem(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_urem(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_sdiv(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_udiv(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_lshl(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_ashr(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_lshr(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_xor(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVOrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_or(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                      toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_and(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_bv_ult(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_bv_slt(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_bv_uleq(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_bv_sleq(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkAndImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  msat_make_and(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                                toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkOrImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  msat_make_or(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                               toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkEqualImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  msat_make_eq(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                               toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                    const SMTExprRef &F) {
  if (T->isBoolSort())
    return mkOr(mkAnd(Cond, T), mkAnd(mkNot(Cond), F));

  return newExprRef(MathSATExpr(
      Context, T->Sort,
      msat_make_term_ite(*Context, toSolverExpr<MathSATExpr>(*Cond).Expr,
                         toSolverExpr<MathSATExpr>(*T).Expr,
                         toSolverExpr<MathSATExpr>(*F).Expr)));
}

SMTExprRef MathSATSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBVSort(i + Exp->getWidth()),
      msat_make_bv_sext(*Context, i, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBVSort(i + Exp->getWidth()),
      msat_make_bv_zext(*Context, i, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                          const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, mkBVSort(High - Low + 1),
                  msat_make_bv_extract(*Context, High, Low,
                                       toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
      msat_make_bv_concat(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                          toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                            const SMTExprRef &Index) {
  return newExprRef(MathSATExpr(
      Context, Array->Sort->getElementSort(),
      msat_make_array_read(*Context, toSolverExpr<MathSATExpr>(*Array).Expr,
                           toSolverExpr<MathSATExpr>(*Index).Expr)));
}

SMTExprRef MathSATSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                           const SMTExprRef &Index,
                                           const SMTExprRef &Element) {
  return newExprRef(MathSATExpr(
      Context, Array->Sort,
      msat_make_array_write(*Context, toSolverExpr<MathSATExpr>(*Array).Expr,
                            toSolverExpr<MathSATExpr>(*Index).Expr,
                            toSolverExpr<MathSATExpr>(*Element).Expr)));
}

SMTExprRef MathSATSolver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_fp_abs(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPNegImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_fp_neg(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_isinf(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_isnan(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  msat_make_fp_issubnormal(
                      *Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_isnormal(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_iszero(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPMulImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS, const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_fp_times(*Context,
                         toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                         toSolverExpr<MathSATExpr>(*LHS).Expr,
                         toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPDivImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS, const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_fp_div(*Context, toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                       toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPRemImpl(const SMTExprRef &, const SMTExprRef &) {
  assert(0 && "MathSAT does not implement fp.rem");
  __builtin_unreachable();
}

SMTExprRef MathSATSolver::mkFPAddImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS, const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_fp_plus(*Context, toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                        toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPSubImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS, const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_fp_minus(*Context,
                         toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                         toSolverExpr<MathSATExpr>(*LHS).Expr,
                         toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPSqrtImpl(const SMTExprRef &Exp, const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_fp_sqrt(*Context, toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                        toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPFMAImpl(const SMTExprRef &, const SMTExprRef &,
                                      const SMTExprRef &, const RM &) {
  assert(0 && "MathSAT does not implement fp.fma");
  __builtin_unreachable();
}

SMTExprRef MathSATSolver::mkFPLtImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_lt(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                      toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPLeImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_leq(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPEqualImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_equal(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                         toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPtoFPImpl(const SMTExprRef &From,
                                       const SMTSortRef &To, const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_cast(*Context, To->getFPExponentWidth(),
                        To->getFPSignificandWidth(),
                        toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                        toSolverExpr<MathSATExpr>(*From).Expr)));
}

SMTExprRef MathSATSolver::mkSBVtoFPImpl(const SMTExprRef &From,
                                        const SMTSortRef &To, const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_from_sbv(*Context, To->getFPExponentWidth(),
                            To->getFPSignificandWidth(),
                            toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                            toSolverExpr<MathSATExpr>(*From).Expr)));
}

SMTExprRef MathSATSolver::mkUBVtoFPImpl(const SMTExprRef &From,
                                        const SMTSortRef &To, const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_from_ubv(*Context, To->getFPExponentWidth(),
                            To->getFPSignificandWidth(),
                            toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                            toSolverExpr<MathSATExpr>(*From).Expr)));
}

SMTExprRef MathSATSolver::mkFPtoSBVImpl(const SMTExprRef &From,
                                        unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRM(RM::ROUND_TO_ZERO);
  return newExprRef(MathSATExpr(
      Context, mkBVSort(ToWidth),
      msat_make_fp_to_bv(*Context, ToWidth,
                         toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                         toSolverExpr<MathSATExpr>(*From).Expr)));
}

SMTExprRef MathSATSolver::mkFPtoUBVImpl(const SMTExprRef &From,
                                        unsigned ToWidth) {
  // We just need to call mkFPtoSBV
  return mkFPtoSBV(From, ToWidth);
}

SMTExprRef MathSATSolver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                             const RM &R) {
  SMTExprRef roundingMode = mkRM(R);
  return newExprRef(MathSATExpr(
      Context, From->Sort,
      msat_make_fp_round_to_int(*Context,
                                toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                                toSolverExpr<MathSATExpr>(*From).Expr)));
}

bool MathSATSolver::getBoolImpl(const SMTExprRef &Exp) {
  if (msat_term_is_true(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr))
    return true;

  if (msat_term_is_false(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr))
    return false;

  assert(0 && "Bool is neither true nor false");
  __builtin_unreachable();
}

static inline std::string getGMPVal(MathSATSolver &S, const SMTExprRef &Exp) {
  SMTExprRef t = S.newExprRef(MathSATExpr(
      S.Context, Exp->Sort,
      msat_get_model_value(*S.Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));

  // GMP rational value object.
  mpq_t val;
  mpq_init(val);
  msat_term_to_number(*toSolverExpr<MathSATExpr>(*t).Context,
                      toSolverExpr<MathSATExpr>(*t).Expr, val);

  std::string bv = mpq_get_str(nullptr, 2, val);
  mpq_clear(val);
  return bv;
}

std::string MathSATSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  std::string val = getGMPVal(*this, Exp);
  if (val.length() < Exp->getWidth())
    val = std::string(Exp->getWidth() - val.length(), '0') + val;
  return val;
}

std::string MathSATSolver::getFPInBinImpl(const SMTExprRef &Exp) {
  return getBVInBin(Exp);
}

SMTExprRef MathSATSolver::getArrayElementImpl(const SMTExprRef &Array,
                                              const SMTExprRef &Index) {
  SMTExprRef sel = mkArraySelect(Array, Index);
  return newExprRef(MathSATExpr(
      Context, sel->Sort,
      msat_get_model_value(*Context, toSolverExpr<MathSATExpr>(*sel).Expr)));
}

SMTExprRef MathSATSolver::mkBoolImpl(const bool Bool) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  Bool ? msat_make_true(*Context) : msat_make_false(*Context)));
}

SMTExprRef MathSATSolver::mkBVFromDecImpl(const int64_t Int,
                                          const SMTSortRef &Sort) {
  // Set upper bits to zero because MathSAT refuses to parse negative numbers
  uint64_t newInt =
      static_cast<uint64_t>(Int) & ((1ULL << Sort->getWidth()) - 1);

  return newExprRef(
      MathSATExpr(Context, Sort,
                  msat_make_bv_number(*Context, std::to_string(newInt).c_str(),
                                      Sort->getWidth(), 10)));
}

SMTExprRef MathSATSolver::mkBVFromBinImpl(const std::string &Int,
                                          const SMTSortRef &Sort) {
  return newExprRef(MathSATExpr(
      Context, Sort,
      msat_make_bv_number(*Context, Int.c_str(), Sort->getWidth(), 2)));
}

SMTExprRef MathSATSolver::mkSymbolImpl(const std::string &Name,
                                       SMTSortRef Sort) {
  msat_decl d = msat_declare_function(*Context, Name.c_str(),
                                      toSolverSort<MathSATSort>(*Sort).Sort);
  assert(!MSAT_ERROR_DECL(d) && "Invalid function symbol declaration sort");
  return newExprRef(
      MathSATExpr(Context, Sort, msat_make_constant(*Context, d)));
}

SMTExprRef MathSATSolver::mkFPFromBinImpl(const std::string &FP,
                                          unsigned EWidth) {
  std::string fpSMTStr;
  fpSMTStr.append("(fp #b")
      .append({FP[0]})
      .append(" #b")
      .append(FP.substr(1, EWidth))
      .append(" #b")
      .append(FP.substr(1 + EWidth))
      .append(")");

  return newExprRef(MathSATExpr(Context,
                                mkFPSort(EWidth, FP.length() - EWidth - 1),
                                msat_from_string(*Context, fpSMTStr.c_str())));
}

SMTExprRef MathSATSolver::mkRMImpl(const RM &R) {
  msat_term e;
  switch (R) {
  default:
    assert(0 && "Unsupported floating-point semantics.");
    __builtin_unreachable();
  case RM::ROUND_TO_EVEN:
    e = msat_make_fp_roundingmode_nearest_even(*Context);
    break;
  case RM::ROUND_TO_PLUS_INF:
    e = msat_make_fp_roundingmode_plus_inf(*Context);
    break;
  case RM::ROUND_TO_MINUS_INF:
    e = msat_make_fp_roundingmode_minus_inf(*Context);
    break;
  case RM::ROUND_TO_ZERO:
    e = msat_make_fp_roundingmode_zero(*Context);
    break;
  }
  return newExprRef(MathSATExpr(Context, mkRMSort(), e));
}

SMTExprRef MathSATSolver::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  SMTSortRef sort = mkFPSort(ExpWidth, SigWidth);
  SMTExprRef theNaN = newExprRef(MathSATExpr(
      Context, sort, msat_make_fp_nan(*Context, ExpWidth, SigWidth)));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef MathSATSolver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  SMTSortRef sort = mkFPSort(ExpWidth, SigWidth);
  return newExprRef(
      MathSATExpr(Context, sort,
                  Sgn ? msat_make_fp_minus_inf(*Context, ExpWidth, SigWidth)
                      : msat_make_fp_plus_inf(*Context, ExpWidth, SigWidth)));
}

SMTExprRef MathSATSolver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                           const SMTSortRef &To) {
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_from_ieeebv(*Context, To->getFPExponentWidth(),
                               To->getFPSignificandWidth() - 1,
                               toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  SMTSortRef to = mkBVSort(Exp->getWidth());
  return newExprRef(MathSATExpr(
      Context, to,
      msat_make_fp_as_ieeebv(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                           const SMTExprRef &InitValue) {
  SMTSortRef sort = mkArraySort(IndexSort, InitValue->Sort);
  return newExprRef(MathSATExpr(
      Context, sort,
      msat_make_array_const(*Context, toSolverSort<MathSATSort>(*sort).Sort,
                            toSolverExpr<MathSATExpr>(*InitValue).Expr)));
}

checkResult MathSATSolver::checkImpl() {
  msat_result res = msat_solve(*Context);
  if (res == MSAT_SAT)
    return checkResult::SAT;

  if (res == MSAT_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void MathSATSolver::resetImpl() { msat_reset_env(*Context); }

void MathSATSolver::dumpImpl() {
  size_t num_of_asserted;
  msat_term *asserted_formulas =
      msat_get_asserted_formulas(*Context, &num_of_asserted);

  for (unsigned i = 0; i < num_of_asserted; i++)
    std::cerr << msat_to_smtlib2(*Context, asserted_formulas[i]) << '\n';
  msat_free(asserted_formulas);
}

void MathSATSolver::dumpModelImpl() {
  // we use a model iterator to retrieve the model values for all the
  // variables, and the necessary function instantiations
  msat_model_iterator iter = msat_create_model_iterator(*Context);
  assert(!MSAT_ERROR_MODEL_ITERATOR(iter) &&
         "Error when getting model iterator");

  while (msat_model_iterator_has_next(iter)) {
    msat_term t, v;
    char *s;
    msat_model_iterator_next(iter, &t, &v);
    s = msat_term_repr(t);
    assert(s && "Error when getting variable from model");
    std::cerr << s << " = ";
    msat_free(s);
    s = msat_term_repr(v);
    assert(s && "Error when getting variable value from model");
    std::cerr << s << '\n';
    msat_free(s);
  }
  msat_destroy_model_iterator(iter);
}

} // namespace camada

#endif
