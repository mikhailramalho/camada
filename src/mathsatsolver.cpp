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
#if SOLVER_MATHSAT_ENABLED

#include "mathsatsolver.h"

#include <cassert>
#include <cstddef>
#include <cstdlib>
#include <gmp.h>
#include <iostream>

namespace camada {

static inline const msat_term &toMathSATTerm(const SMTExpr &Exp) {
  auto const &ME = toSolverExpr<MathSATExpr>(Exp);
  assert(!ME.IsDecl && "Expected MathSAT term, got declaration");
  return ME.Expr;
}

static inline const msat_term &toMathSATTerm(const SMTExprRef &Exp) {
  return toMathSATTerm(*Exp);
}

static inline msat_decl toMathSATDecl(const SMTExpr &Exp) {
  auto const &ME = toSolverExpr<MathSATExpr>(Exp);
  assert(ME.IsDecl && "Expected MathSAT declaration, got term");
  return ME.Decl;
}

static inline msat_decl toMathSATDecl(const SMTExprRef &Exp) {
  return toMathSATDecl(*Exp);
}

void MathSATContextOwner::reset() {
  if (Valid) {
    msat_destroy_env(Context);
    Valid = false;
  }
}

unsigned MathSATSort::getWidthFromSolver() const {
  std::size_t w;
  if (msat_is_bv_type(*Context, Sort, &w))
    return w;

  if (msat_is_bool_type(*Context, Sort))
    return 1;

  if (msat_is_integer_type(*Context, Sort) || msat_is_rational_type(*Context, Sort))
    return 0;

  if (msat_is_fp_roundingmode_type(*Context, Sort))
    return 3;

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
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  auto const &OtherExpr = static_cast<const MathSATExpr &>(Other);
  if (IsDecl != OtherExpr.IsDecl)
    return false;
  if (IsDecl)
    return msat_decl_id(Decl) == msat_decl_id(OtherExpr.Decl);
  return msat_term_id(Expr) == msat_term_id(OtherExpr.Expr);
}

void MathSATExpr::dump() const {
  if (IsDecl) {
    char *name = msat_decl_get_name(Decl);
    std::cerr << "(declare-fun " << name << " ...)\n";
    msat_free(name);
    return;
  }
  char *ast = msat_to_smtlib2(*Context, Expr);
  std::cerr << ast << '\n';
  msat_free(ast);
}

MathSATSolver::MathSATSolver() : SMTSolverImpl() {
  msat_config cfg = msat_create_default_config("AUFBV");
  msat_set_option(cfg, "model_generation", "true");
  OwnedContext.reset(msat_create_env(cfg));
  msat_destroy_config(cfg);
  Context = OwnedContext.get();
  initializeCommonSingletons();
}

MathSATSolver::MathSATSolver(const msat_config &Config) : SMTSolverImpl() {
  OwnedContext.reset(msat_create_env(Config));
  Context = OwnedContext.get();
  initializeCommonSingletons();
}

MathSATSolver::~MathSATSolver() {
  invalidateGeneratedObjects();
  OwnedContext.reset();
  Context = nullptr;
}

void MathSATSolver::addConstraintImpl(const SMTExprRef &Exp) {
  msat_assert_formula(*Context, toMathSATTerm(Exp));
}

static inline bool checkExprError(const SMTExpr &Exp) {
  auto const &exp = toSolverExpr<MathSATExpr>(Exp);
  if (exp.IsDecl)
    return false;
  if (MSAT_ERROR_TERM(exp.Expr)) {
    std::cerr << "MathSAT Error " << msat_last_error_message(*exp.Context)
              << '\n';
    return true;
  }
  return false;
}

SMTExprRef MathSATSolver::newExprRefImpl(const SMTExpr &Exp) const {
  assert(!checkExprError(Exp) && "Error when creating MathSAT expr.");
  return storeExprRef(toSolverExpr<MathSATExpr>(Exp));
}

SMTExprRef MathSATSolver::cloneExprWithSortImpl(const SMTExpr &Exp,
                                                const SMTSortRef &Sort) const {
  assert(!checkExprError(Exp) && "Error when creating MathSAT expr.");
  MathSATExpr Retagged = toSolverExpr<MathSATExpr>(Exp);
  Retagged.Sort = Sort;
  return storeExprRef(Retagged);
}

SMTSortRef MathSATSolver::mkBoolSortImpl() {
  return newSortRef<MathSATSort>(
      MathSATSort(SMTSortKind::Bool, Context, msat_get_bool_type(*Context), 1));
}

SMTSortRef MathSATSolver::mkIntSortImpl() {
  return newSortRef<MathSATSort>(
      MathSATSort(SMTSortKind::Int, Context, msat_get_integer_type(*Context)));
}

SMTSortRef MathSATSolver::mkRealSortImpl() {
  return newSortRef<MathSATSort>(MathSATSort(SMTSortKind::Real, Context,
                                             msat_get_rational_type(*Context)));
}

SMTSortRef MathSATSolver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<MathSATSort>(
      MathSATSort(SMTSortKind::BV, Context,
                  msat_get_bv_type(*Context, BitWidth), BitWidth));
}

SMTSortRef MathSATSolver::mkRMSortImpl() {
  return newSortRef<MathSATSort>(MathSATSort(
      SMTSortKind::RM, Context, msat_get_fp_roundingmode_type(*Context), 3));
}

SMTSortRef MathSATSolver::mkFPSortImpl(const unsigned ExpWidth,
                                       const unsigned SigWidth) {
  return newSortRef<MathSATSort>(MathSATSort(
      SMTSortKind::FP, Context, msat_get_fp_type(*Context, ExpWidth, SigWidth),
      1 + ExpWidth + SigWidth, ExpWidth, SigWidth));
}

SMTSortRef MathSATSolver::mkBVFPSortImpl(const unsigned ExpWidth,
                                         const unsigned SigWidth) {
  return newSortRef<MathSATSort>(
      MathSATSort(SMTSortKind::BVFP, Context,
                  msat_get_bv_type(*Context, ExpWidth + SigWidth + 1),
                  ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1));
}

SMTSortRef MathSATSolver::mkBVRMSortImpl() {
  return newSortRef<MathSATSort>(MathSATSort(SMTSortKind::BVRM, Context,
                                             msat_get_bv_type(*Context, 3), 3));
}

SMTSortRef MathSATSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                          const SMTSortRef &ElemSort) {
  const SMTSortRef &backend_elem_sort =
      ElemSort->isBoolSort() ? mkBVSort(1) : ElemSort;
  return newSortRef<MathSATSort>(MathSATSort(
      SMTSortKind::Array, Context,
      msat_get_array_type(*Context, toSolverSort<MathSATSort>(*IndexSort).Sort,
                          toSolverSort<MathSATSort>(*backend_elem_sort).Sort),
      0, 0, 0, IndexSort, ElemSort));
}

SMTSortRef
MathSATSolver::mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                                  const SMTSortRef &CodomainSort) {
  std::vector<msat_type> Domain;
  Domain.reserve(DomainSorts.size());
  for (const auto &Sort : DomainSorts)
    Domain.push_back(toSolverSort<MathSATSort>(*Sort).Sort);
  return newSortRef<MathSATSort>(MathSATSort(
      SMTSortKind::Function, Context,
      msat_get_function_type(*Context, Domain.data(), Domain.size(),
                             toSolverSort<MathSATSort>(*CodomainSort).Sort),
      0, 0, 0, {}, {}, DomainSorts, CodomainSort));
}

SMTExprRef MathSATSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort, msat_make_bv_neg(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort, msat_make_bv_not(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkNotImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(Context, Exp->Sort,
                                msat_make_not(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_plus(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_minus(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_times(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_srem(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_urem(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_sdiv(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_udiv(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_lshl(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_ashr(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_lshr(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_xor(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVOrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_or(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_and(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_bv_ult(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_bv_slt(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_bv_uleq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_bv_sleq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkAndImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_and(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkOrImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_or(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkArithNegImpl(const SMTExprRef &Exp) {
  const SMTExprRef &minus_one = Exp->isIntSort() ? mkInt(-1) : mkReal(-1);
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_times(*Context, toMathSATTerm(minus_one), toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkArithAddImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_plus(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkArithSubImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return mkArithAdd(LHS, mkArithNeg(RHS));
}

SMTExprRef MathSATSolver::mkArithMulImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_times(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkArithDivImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_divide(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkArithLtImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return mkNot(mkArithGe(LHS, RHS));
}

SMTExprRef MathSATSolver::mkArithGtImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return mkNot(mkArithLe(LHS, RHS));
}

SMTExprRef MathSATSolver::mkArithLeImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_leq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkArithGeImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_leq(*Context, toMathSATTerm(RHS), toMathSATTerm(LHS))));
}

SMTExprRef MathSATSolver::mkEqualImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_eq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                    const SMTExprRef &F) {
  if (T->isBoolSort())
    return mkOr(mkAnd(Cond, T), mkAnd(mkNot(Cond), F));

  return newExprRef(
      MathSATExpr(Context, T->Sort,
                  msat_make_term_ite(*Context, toMathSATTerm(Cond),
                                     toMathSATTerm(T), toMathSATTerm(F))));
}

SMTExprRef MathSATSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, mkBVSort(i + Exp->getWidth()),
                  msat_make_bv_sext(*Context, i, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, mkBVSort(i + Exp->getWidth()),
                  msat_make_bv_zext(*Context, i, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                          const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBVSort(High - Low + 1),
      msat_make_bv_extract(*Context, High, Low, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
      msat_make_bv_concat(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                            const SMTExprRef &Index) {
  msat_term read = msat_make_array_read(*Context, toMathSATTerm(Array),
                                        toMathSATTerm(Index));
  if (Array->Sort->getElementSort()->isBoolSort()) {
    const SMTExprRef &one = mkBVFromDec(1, mkBVSort(1));
    return newExprRef(
        MathSATExpr(Context, mkBoolSort(),
                    msat_make_eq(*Context, read, toMathSATTerm(one))));
  }

  return newExprRef(MathSATExpr(Context, Array->Sort->getElementSort(), read));
}

SMTExprRef MathSATSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                           const SMTExprRef &Index,
                                           const SMTExprRef &Element) {
  msat_term backend_element = toMathSATTerm(Element);
  if (Array->Sort->getElementSort()->isBoolSort()) {
    const SMTExprRef &zero = mkBVFromDec(0, mkBVSort(1));
    const SMTExprRef &one = mkBVFromDec(1, mkBVSort(1));
    backend_element =
        msat_make_term_ite(*Context, toMathSATTerm(Element), toMathSATTerm(one),
                           toMathSATTerm(zero));
  }

  return newExprRef(MathSATExpr(
      Context, Array->Sort,
      msat_make_array_write(*Context, toMathSATTerm(Array),
                            toMathSATTerm(Index), backend_element)));
}

SMTExprRef MathSATSolver::mkApplyImpl(const SMTExprRef &Function,
                                      const std::vector<SMTExprRef> &Args) {
  std::vector<msat_term> ApplyArgs;
  ApplyArgs.reserve(Args.size());
  for (const auto &Arg : Args)
    ApplyArgs.push_back(toMathSATTerm(Arg));
  return newExprRef(MathSATExpr(
      Context, Function->Sort->getCodomainSort(),
      msat_make_term(*Context, toMathSATDecl(Function), ApplyArgs.data())));
}

SMTExprRef MathSATSolver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort, msat_make_fp_abs(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkFPNegImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort, msat_make_fp_neg(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(), msat_make_fp_isinf(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(), msat_make_fp_isnan(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  msat_make_fp_issubnormal(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  msat_make_fp_isnormal(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  msat_make_fp_iszero(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkFPMulImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS,
                                      const SMTExprRef &R) {
  return newExprRef(
      MathSATExpr(Context, LHS->Sort,
                  msat_make_fp_times(*Context, toMathSATTerm(R),
                                     toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkFPDivImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS,
                                      const SMTExprRef &R) {
  return newExprRef(
      MathSATExpr(Context, LHS->Sort,
                  msat_make_fp_div(*Context, toMathSATTerm(R),
                                   toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkFPRemImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  // MathSAT does not support rem, so convert to BVFP and call the fp_api

  // Save camada flag
  bool oldUseCamadaFP = useCamadaFP;

  // Enable fp conversion API
  useCamadaFP = true;

  // We can call the conversion API directly here because the arguments were
  // already checked
  const SMTExprRef &rem =
      SMTSolverImpl::mkFPRemImpl(mkIEEEFPToBVImpl(LHS), mkIEEEFPToBVImpl(RHS));

  // Restore camada flag
  useCamadaFP = oldUseCamadaFP;

  // And convert it back the right type
  return mkBVToIEEEFP(rem, LHS->Sort);
}

SMTExprRef MathSATSolver::mkFPAddImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS,
                                      const SMTExprRef &R) {
  return newExprRef(
      MathSATExpr(Context, LHS->Sort,
                  msat_make_fp_plus(*Context, toMathSATTerm(R),
                                    toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkFPSubImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS,
                                      const SMTExprRef &R) {
  return newExprRef(
      MathSATExpr(Context, LHS->Sort,
                  msat_make_fp_minus(*Context, toMathSATTerm(R),
                                     toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkFPSqrtImpl(const SMTExprRef &Exp,
                                       const SMTExprRef &R) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_fp_sqrt(*Context, toMathSATTerm(R), toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                      const SMTExprRef &Z,
                                      const SMTExprRef &R) {
  // MathSAT does not support FMA, so convert to BVFP and call the fp_api

  // Save camada flag
  bool oldUseCamadaFP = useCamadaFP;

  // To convert the rounding mode, we first need to generate the equalities in
  // floating-point mode
  const SMTExprRef &isNe = mkEqual(R, mkRM(RM::ROUND_TO_EVEN));
  const SMTExprRef &isPi = mkEqual(R, mkRM(RM::ROUND_TO_PLUS_INF));
  const SMTExprRef &isMi = mkEqual(R, mkRM(RM::ROUND_TO_MINUS_INF));

  // Enable fp conversion API
  useCamadaFP = true;

  // Now we want to generate the correct rounding mode encoded as a bitvector,
  // so use the equalities previously generated in an ite chain
  const SMTExprRef &roundingMode =
      mkIte(isNe, mkBVFromDec(0, mkRMSort()),
            mkIte(isPi, mkBVFromDec(2, mkRMSort()),
                  mkIte(isMi, mkBVFromDec(3, mkRMSort()),
                        mkBVFromDec(4, mkRMSort()))));

  // We can call the conversion API directly here because the arguments were
  // already checked
  const SMTExprRef &fma =
      SMTSolverImpl::mkFPFMAImpl(mkIEEEFPToBVImpl(X), mkIEEEFPToBVImpl(Y),
                                 mkIEEEFPToBVImpl(Z), roundingMode);

  // Restore camada flag
  useCamadaFP = oldUseCamadaFP;

  // And convert it back the right type
  return mkBVToIEEEFP(fma, X->Sort);
}

SMTExprRef MathSATSolver::mkFPLtImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_lt(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkFPLeImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_leq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkFPEqualImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, mkBoolSort(),
      msat_make_fp_equal(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS))));
}

SMTExprRef MathSATSolver::mkFPtoFPImpl(const SMTExprRef &From,
                                       const SMTSortRef &To,
                                       const SMTExprRef &R) {
  return newExprRef(
      MathSATExpr(Context, To,
                  msat_make_fp_cast(*Context, To->getFPExponentWidth(),
                                    To->getFPSignificandWidth(),
                                    toMathSATTerm(R), toMathSATTerm(From))));
}

SMTExprRef MathSATSolver::mkSBVtoFPImpl(const SMTExprRef &From,
                                        const SMTSortRef &To,
                                        const SMTExprRef &R) {
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_from_sbv(*Context, To->getFPExponentWidth(),
                            To->getFPSignificandWidth(), toMathSATTerm(R),
                            toMathSATTerm(From))));
}

SMTExprRef MathSATSolver::mkUBVtoFPImpl(const SMTExprRef &From,
                                        const SMTSortRef &To,
                                        const SMTExprRef &R) {
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_from_ubv(*Context, To->getFPExponentWidth(),
                            To->getFPSignificandWidth(), toMathSATTerm(R),
                            toMathSATTerm(From))));
}

SMTExprRef MathSATSolver::mkFPtoSBVImpl(const SMTExprRef &From,
                                        unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO);
  return newExprRef(MathSATExpr(Context, mkBVSort(ToWidth),
                                msat_make_fp_to_bv(*Context, ToWidth,
                                                   toMathSATTerm(roundingMode),
                                                   toMathSATTerm(From))));
}

SMTExprRef MathSATSolver::mkFPtoUBVImpl(const SMTExprRef &From,
                                        unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO);
  return newExprRef(MathSATExpr(Context, mkBVSort(ToWidth),
                                msat_make_fp_to_ubv(*Context, ToWidth,
                                                    toMathSATTerm(roundingMode),
                                                    toMathSATTerm(From))));
}

SMTExprRef MathSATSolver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                             const SMTExprRef &R) {
  return newExprRef(
      MathSATExpr(Context, From->Sort,
                  msat_make_fp_round_to_int(*Context, toMathSATTerm(R),
                                            toMathSATTerm(From))));
}

bool MathSATSolver::getBoolImpl(const SMTExprRef &Exp) {
  if (msat_term_is_true(*Context, toMathSATTerm(Exp)))
    return true;

  if (msat_term_is_false(*Context, toMathSATTerm(Exp)))
    return false;

  assert(0 && "Bool is neither true nor false");
  __builtin_unreachable();
}

static inline std::string getGMPVal(const MathSATSolver &S,
                                    const SMTExprRef &Exp) {
  const SMTExprRef &t = S.newExprRef(
      MathSATExpr(S.Context, Exp->Sort,
                  msat_get_model_value(*S.Context, toMathSATTerm(Exp))));

  // GMP rational value object.
  mpq_t val;
  mpq_init(val);
  msat_term_to_number(*toSolverExpr<MathSATExpr>(*t).Context, toMathSATTerm(t),
                      val);

  char *raw_bv = mpq_get_str(nullptr, 2, val);
  std::string bv = raw_bv;
  void (*gmp_free)(void *, std::size_t);
  mp_get_memory_functions(nullptr, nullptr, &gmp_free);
  gmp_free(raw_bv, bv.size() + 2);
  mpq_clear(val);
  return bv;
}

std::string MathSATSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  return getGMPVal(*this, Exp);
}

std::string MathSATSolver::getFPInBinImpl(const SMTExprRef &Exp) {
  return getGMPVal(*this, Exp);
}

SMTExprRef MathSATSolver::getArrayElementImpl(const SMTExprRef &Array,
                                              const SMTExprRef &Index) {
  const SMTExprRef &sel = mkArraySelect(Array, Index);
  return newExprRef(MathSATExpr(
      Context, sel->Sort, msat_get_model_value(*Context, toMathSATTerm(sel))));
}

SMTExprRef MathSATSolver::mkBoolImpl(const bool Bool) {
  return newExprRef(
      MathSATExpr(Context, mkBoolSort(),
                  Bool ? msat_make_true(*Context) : msat_make_false(*Context)));
}

SMTExprRef MathSATSolver::mkIntImpl(int64_t v) {
  return newExprRef(MathSATExpr(
      Context, mkIntSort(),
      msat_make_number(*Context, std::to_string(v).c_str())));
}

SMTExprRef MathSATSolver::mkRealImpl(const std::string &v) {
  std::string repr = v;
  if (repr.find('/') == std::string::npos && repr.find('.') == std::string::npos)
    repr.append("/1");
  return newExprRef(MathSATExpr(
      Context, mkRealSort(), msat_make_number(*Context, repr.c_str())));
}

SMTExprRef MathSATSolver::mkRealImpl(int64_t v) {
  return mkRealImpl(std::to_string(v));
}

SMTExprRef MathSATSolver::mkRealImpl(int64_t num, int64_t den) {
  return mkRealImpl(std::to_string(num) + "/" + std::to_string(den));
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
                                       const SMTSortRef &Sort) {
  msat_decl d = msat_declare_function(*Context, Name.c_str(),
                                      toSolverSort<MathSATSort>(*Sort).Sort);
  assert(!MSAT_ERROR_DECL(d) && "Invalid function symbol declaration sort");
  if (Sort->isFunctionSort())
    return newExprRef(MathSATExpr(Context, Sort, d));
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
    std::cerr << "MathSAT Error unsupported floating-point rounding mode.\n";
    std::abort();
  case RM::ROUND_TO_EVEN:
    e = msat_make_fp_roundingmode_nearest_even(*Context);
    break;
  case RM::ROUND_TO_AWAY:
    std::cerr << "MathSAT Error ROUND_TO_AWAY is not supported.\n";
    std::abort();
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
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1);
  const SMTExprRef &theNaN = newExprRef(MathSATExpr(
      Context, sort, msat_make_fp_nan(*Context, ExpWidth, SigWidth - 1)));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef MathSATSolver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1);
  return newExprRef(MathSATExpr(
      Context, sort,
      Sgn ? msat_make_fp_minus_inf(*Context, ExpWidth, SigWidth - 1)
          : msat_make_fp_plus_inf(*Context, ExpWidth, SigWidth - 1)));
}

SMTExprRef MathSATSolver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                           const SMTSortRef &To) {
  return newExprRef(
      MathSATExpr(Context, To,
                  msat_make_fp_from_ieeebv(*Context, To->getFPExponentWidth(),
                                           To->getFPSignificandWidth(),
                                           toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  const SMTSortRef &to = mkBVFPSort(Exp->Sort->getFPExponentWidth(),
                                    Exp->Sort->getFPSignificandWidth());
  return newExprRef(MathSATExpr(
      Context, to, msat_make_fp_as_ieeebv(*Context, toMathSATTerm(Exp))));
}

SMTExprRef MathSATSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                           const SMTExprRef &InitValue) {
  const SMTSortRef &sort = mkArraySort(IndexSort, InitValue->Sort);
  msat_term backend_init = toMathSATTerm(InitValue);
  if (InitValue->isBoolSort()) {
    const SMTExprRef &zero = mkBVFromDec(0, mkBVSort(1));
    const SMTExprRef &one = mkBVFromDec(1, mkBVSort(1));
    backend_init = msat_make_term_ite(*Context, toMathSATTerm(InitValue),
                                      toMathSATTerm(one), toMathSATTerm(zero));
  }
  return newExprRef(MathSATExpr(
      Context, sort,
      msat_make_array_const(*Context, toSolverSort<MathSATSort>(*sort).Sort,
                            backend_init)));
}

SMTExprRef MathSATSolver::mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                       const SMTExprRef &Body) {
  std::vector<msat_term> old_terms;
  std::vector<msat_term> bound_vars;
  old_terms.reserve(Vars.size());
  bound_vars.reserve(Vars.size());

  for (std::size_t i = 0; i < Vars.size(); ++i) {
    const SMTExprRef &Var = Vars[i];
    old_terms.push_back(toMathSATTerm(Var));
    bound_vars.push_back(msat_make_variable(
        *Context, ("__CAMADA_qvar" + std::to_string(i)).c_str(),
        toSolverSort<MathSATSort>(*Var->Sort).Sort));
  }

  msat_term quantified_body =
      msat_apply_substitution(*Context, toMathSATTerm(Body), old_terms.size(),
                              old_terms.data(), bound_vars.data());
  assert(!MSAT_ERROR_TERM(quantified_body) &&
         "Failed to substitute MathSAT quantified body");

  for (auto it = bound_vars.rbegin(); it != bound_vars.rend(); ++it) {
    quantified_body = msat_make_forall(*Context, *it, quantified_body);
    assert(!MSAT_ERROR_TERM(quantified_body) &&
           "Failed to build MathSAT forall term");
  }

  return newExprRef(MathSATExpr(Context, mkBoolSort(), quantified_body));
}

SMTExprRef MathSATSolver::mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                       const SMTExprRef &Body) {
  std::vector<msat_term> old_terms;
  std::vector<msat_term> bound_vars;
  old_terms.reserve(Vars.size());
  bound_vars.reserve(Vars.size());

  for (std::size_t i = 0; i < Vars.size(); ++i) {
    const SMTExprRef &Var = Vars[i];
    old_terms.push_back(toMathSATTerm(Var));
    bound_vars.push_back(msat_make_variable(
        *Context, ("__CAMADA_qvar" + std::to_string(i)).c_str(),
        toSolverSort<MathSATSort>(*Var->Sort).Sort));
  }

  msat_term quantified_body =
      msat_apply_substitution(*Context, toMathSATTerm(Body), old_terms.size(),
                              old_terms.data(), bound_vars.data());
  assert(!MSAT_ERROR_TERM(quantified_body) &&
         "Failed to substitute MathSAT quantified body");

  for (auto it = bound_vars.rbegin(); it != bound_vars.rend(); ++it) {
    quantified_body = msat_make_exists(*Context, *it, quantified_body);
    assert(!MSAT_ERROR_TERM(quantified_body) &&
           "Failed to build MathSAT exists term");
  }

  return newExprRef(MathSATExpr(Context, mkBoolSort(), quantified_body));
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

void MathSATSolver::pushImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i)
    msat_push_backtrack_point(*Context);
}

void MathSATSolver::popImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i)
    msat_pop_backtrack_point(*Context);
}

std::string MathSATSolver::getSolverNameAndVersion() const {
  char *tmp = msat_get_version();
  std::string ver = tmp;
  msat_free(tmp);
  return std::string("MathSAT v").append(ver);
}

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
