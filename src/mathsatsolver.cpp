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
#include <cstdio>
#include <cstdlib>
#include <gmp.h>

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

  if (msat_is_integer_type(*Context, Sort) ||
      msat_is_rational_type(*Context, Sort))
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
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void MathSATSort::dump(std::string &Out) const {
  char *s = msat_type_repr(Sort);
  Out = s;
  Out += "\n";
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
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void MathSATExpr::dump(std::string &Out) const {
  if (IsDecl) {
    char *name = msat_decl_get_name(Decl);
    Out = "(declare-fun ";
    Out += name;
    Out += " ...)\n";
    msat_free(name);
    return;
  }
  char *ast = msat_to_smtlib2(*Context, Expr);
  Out = ast;
  Out += "\n";
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
    std::fprintf(stderr, "MathSAT Error %s\n",
                 msat_last_error_message(*exp.Context));
    return true;
  }
  return false;
}

static inline bool checkExprError(MathSATContextRef Context, msat_decl Decl) {
  if (MSAT_ERROR_DECL(Decl)) {
    std::fprintf(stderr, "MathSAT Error %s\n",
                 msat_last_error_message(*Context));
    return true;
  }
  return false;
}

SMTExprRef MathSATSolver::newExprRefImpl(const SMTExpr &Exp) const {
  assert(!checkExprError(Exp) && "Error when creating MathSAT expr.");
  return storeExprRef(toSolverExpr<MathSATExpr>(Exp));
}

SMTExprRef MathSATSolver::rewrapExprImpl(const SMTExpr &Exp,
                                         const SMTSortRef &Sort,
                                         SMTExprKind Kind) const {
  assert(!checkExprError(Exp) && "Error when creating MathSAT expr.");
  const auto &Wrapped = toSolverExpr<MathSATExpr>(Exp);
  if (Wrapped.IsDecl)
    return storeExprRef(MathSATExpr(Kind, Wrapped.Context, Sort, Wrapped.Decl));
  return storeExprRef(MathSATExpr(Kind, Wrapped.Context, Sort, Wrapped.Expr));
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
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVNeg, Context, Exp->Sort,
      msat_make_bv_neg(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVNot, Context, Exp->Sort,
      msat_make_bv_not(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(SMTExprKind::Not, Context, Exp->Sort,
                                  msat_make_not(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVAdd, Context, LHS->Sort,
      msat_make_bv_plus(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVSub, Context, LHS->Sort,
      msat_make_bv_minus(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVMul, Context, LHS->Sort,
      msat_make_bv_times(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVSRem, Context, LHS->Sort,
      msat_make_bv_srem(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVURem, Context, LHS->Sort,
      msat_make_bv_urem(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVSDiv, Context, LHS->Sort,
      msat_make_bv_sdiv(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVUDiv, Context, LHS->Sort,
      msat_make_bv_udiv(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVShl, Context, LHS->Sort,
      msat_make_bv_lshl(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVAshr, Context, LHS->Sort,
      msat_make_bv_ashr(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVLshr, Context, LHS->Sort,
      msat_make_bv_lshr(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVXor, Context, LHS->Sort,
      msat_make_bv_xor(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVOrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVOr, Context, LHS->Sort,
      msat_make_bv_or(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVAnd, Context, LHS->Sort,
      msat_make_bv_and(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVUlt, Context, mkBoolSort(),
      msat_make_bv_ult(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVSlt, Context, mkBoolSort(),
      msat_make_bv_slt(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVUle, Context, mkBoolSort(),
      msat_make_bv_uleq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVSle, Context, mkBoolSort(),
      msat_make_bv_sleq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkAndImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::And, Context, mkBoolSort(),
      msat_make_and(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkOrImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::Or, Context, mkBoolSort(),
      msat_make_or(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkArithNegImpl(const SMTExprRef &Exp) {
  const SMTExprRef &minus_one = Exp->isIntSort() ? mkInt(-1) : mkReal(-1);
  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArithNeg, Context, Exp->Sort,
      msat_make_times(*Context, toMathSATTerm(minus_one), toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkArithAddImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArithAdd, Context, LHS->Sort,
      msat_make_plus(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkArithSubImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return mkArithAdd(LHS, mkArithNeg(RHS));
}

SMTExprRef MathSATSolver::mkArithMulImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArithMul, Context, LHS->Sort,
      msat_make_times(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkArithDivImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArithDiv, Context, LHS->Sort,
      msat_make_divide(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkArithModImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  const SMTExprRef &lhs_real = mkInt2Real(LHS);
  const SMTExprRef &rhs_real = mkInt2Real(RHS);
  const SMTExprRef &q = mkReal2Int(mkArithDiv(lhs_real, rhs_real));
  SMTExprRef theExp = mkArithSub(LHS, mkArithMul(RHS, q));
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::ArithMod);
}

SMTExprRef MathSATSolver::mkArithShlImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArithShl, Context, mkIntSort(),
      msat_make_times(*Context, toMathSATTerm(LHS),
                      msat_make_pow(*Context, toMathSATTerm(mkInt("2")),
                                    toMathSATTerm(RHS))));
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
  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArithLe, Context, mkBoolSort(),
      msat_make_leq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkArithGeImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArithGe, Context, mkBoolSort(),
      msat_make_leq(*Context, toMathSATTerm(RHS), toMathSATTerm(LHS)));
}

SMTExprRef MathSATSolver::mkInt2RealImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::Int2Real, Context, mkRealSort(),
      msat_make_times(*Context, toMathSATTerm(Exp), toMathSATTerm(mkReal(1))));
}

SMTExprRef MathSATSolver::mkReal2IntImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::Real2Int, Context, mkIntSort(),
      msat_make_floor(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkIsIntImpl(const SMTExprRef &Exp) {
  if (Exp->isIntSort())
    return mkBool(true);

  SMTExprRef theExp = mkEqual(mkInt2Real(mkReal2Int(Exp)), Exp);
  return rewrapExprImpl(*theExp, theExp->Sort, SMTExprKind::IsInt);
}

SMTExprRef MathSATSolver::mkEqualImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::Equal, Context, mkBoolSort(),
      msat_make_eq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                    const SMTExprRef &F) {
  if (T->isBoolSort())
    return mkOr(mkAnd(Cond, T), mkAnd(mkNot(Cond), F));

  return makeExprRef<MathSATExpr>(
      SMTExprKind::Ite, Context, T->Sort,
      msat_make_term_ite(*Context, toMathSATTerm(Cond), toMathSATTerm(T),
                         toMathSATTerm(F)));
}

SMTExprRef MathSATSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVSignExt, Context, mkBVSort(i + Exp->getWidth()),
      msat_make_bv_sext(*Context, i, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVZeroExt, Context, mkBVSort(i + Exp->getWidth()),
      msat_make_bv_zext(*Context, i, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                          const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVExtract, Context, mkBVSort(High - Low + 1),
      msat_make_bv_extract(*Context, High, Low, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVConcat, Context,
      mkBVSort(LHS->getWidth() + RHS->getWidth()),
      msat_make_bv_concat(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                            const SMTExprRef &Index) {
  msat_term read = msat_make_array_read(*Context, toMathSATTerm(Array),
                                        toMathSATTerm(Index));
  if (Array->Sort->getElementSort()->isBoolSort()) {
    const SMTExprRef &one = mkBVFromDec(1, mkBVSort(1));
    return makeExprRef<MathSATExpr>(
        SMTExprKind::ArraySelect, Context, mkBoolSort(),
        msat_make_eq(*Context, read, toMathSATTerm(one)));
  }

  return makeExprRef<MathSATExpr>(SMTExprKind::ArraySelect, Context,
                                  Array->Sort->getElementSort(), read);
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

  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArrayStore, Context, Array->Sort,
      msat_make_array_write(*Context, toMathSATTerm(Array),
                            toMathSATTerm(Index), backend_element));
}

SMTExprRef MathSATSolver::mkApplyImpl(const SMTExprRef &Function,
                                      const std::vector<SMTExprRef> &Args) {
  std::vector<msat_term> ApplyArgs;
  ApplyArgs.reserve(Args.size());
  for (const auto &Arg : Args)
    ApplyArgs.push_back(toMathSATTerm(Arg));
  return makeExprRef<MathSATExpr>(
      SMTExprKind::Apply, Context, Function->Sort->getCodomainSort(),
      msat_make_term(*Context, toMathSATDecl(Function), ApplyArgs.data()));
}

SMTExprRef MathSATSolver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPAbs, Context, Exp->Sort,
      msat_make_fp_abs(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkFPNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPNeg, Context, Exp->Sort,
      msat_make_fp_neg(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPIsInfinite, Context, mkBoolSort(),
      msat_make_fp_isinf(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPIsNaN, Context, mkBoolSort(),
      msat_make_fp_isnan(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPIsDenormal, Context, mkBoolSort(),
      msat_make_fp_issubnormal(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPIsNormal, Context, mkBoolSort(),
      msat_make_fp_isnormal(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPIsZero, Context, mkBoolSort(),
      msat_make_fp_iszero(*Context, toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkFPMulImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS,
                                      const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(SMTExprKind::FPMul, Context, LHS->Sort,
                                  msat_make_fp_times(*Context, toMathSATTerm(R),
                                                     toMathSATTerm(LHS),
                                                     toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkFPDivImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS,
                                      const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(SMTExprKind::FPDiv, Context, LHS->Sort,
                                  msat_make_fp_div(*Context, toMathSATTerm(R),
                                                   toMathSATTerm(LHS),
                                                   toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkFPRemImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  // MathSAT does not support rem, so convert to BVFP and call the fp_api

  // We can call the conversion API directly here because the arguments were
  // already checked
  const SMTExprRef &rem =
      SMTSolverImpl::mkFPRemImpl(mkIEEEFPToBVImpl(LHS), mkIEEEFPToBVImpl(RHS));

  // And convert it back the right type
  return mkBVToIEEEFP(rem, LHS->Sort);
}

SMTExprRef MathSATSolver::mkFPAddImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS,
                                      const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(SMTExprKind::FPAdd, Context, LHS->Sort,
                                  msat_make_fp_plus(*Context, toMathSATTerm(R),
                                                    toMathSATTerm(LHS),
                                                    toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkFPSubImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS,
                                      const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(SMTExprKind::FPSub, Context, LHS->Sort,
                                  msat_make_fp_minus(*Context, toMathSATTerm(R),
                                                     toMathSATTerm(LHS),
                                                     toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkFPSqrtImpl(const SMTExprRef &Exp,
                                       const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPSqrt, Context, Exp->Sort,
      msat_make_fp_sqrt(*Context, toMathSATTerm(R), toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                      const SMTExprRef &Z,
                                      const SMTExprRef &R) {
  // MathSAT does not support FMA, so convert to BVFP and call the fp_api

  // To convert the rounding mode, we first need to generate the equalities in
  // floating-point mode
  const SMTExprRef &isNe =
      mkEqual(R, mkRM(RM::ROUND_TO_EVEN, FPEncoding::Native));
  const SMTExprRef &isPi =
      mkEqual(R, mkRM(RM::ROUND_TO_PLUS_INF, FPEncoding::Native));
  const SMTExprRef &isMi =
      mkEqual(R, mkRM(RM::ROUND_TO_MINUS_INF, FPEncoding::Native));

  // Now we want to generate the correct rounding mode encoded as a bitvector,
  // so use the equalities previously generated in an ite chain
  const SMTExprRef &roundingMode =
      mkIte(isNe, mkBVFromDec(0, mkRMSort(FPEncoding::BV)),
            mkIte(isPi, mkBVFromDec(2, mkRMSort(FPEncoding::BV)),
                  mkIte(isMi, mkBVFromDec(3, mkRMSort(FPEncoding::BV)),
                        mkBVFromDec(4, mkRMSort(FPEncoding::BV)))));

  // We can call the conversion API directly here because the arguments were
  // already checked
  const SMTExprRef &fma =
      SMTSolverImpl::mkFPFMAImpl(mkIEEEFPToBVImpl(X), mkIEEEFPToBVImpl(Y),
                                 mkIEEEFPToBVImpl(Z), roundingMode);

  // And convert it back the right type
  return mkBVToIEEEFP(fma, X->Sort);
}

SMTExprRef MathSATSolver::mkFPLtImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPLt, Context, mkBoolSort(),
      msat_make_fp_lt(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkFPLeImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPLe, Context, mkBoolSort(),
      msat_make_fp_leq(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkFPEqualImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPEqual, Context, mkBoolSort(),
      msat_make_fp_equal(*Context, toMathSATTerm(LHS), toMathSATTerm(RHS)));
}

SMTExprRef MathSATSolver::mkFPtoFPImpl(const SMTExprRef &From,
                                       const SMTSortRef &To,
                                       const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPtoFP, Context, To,
      msat_make_fp_cast(*Context, To->getFPExponentWidth(),
                        To->getFPSignificandWidth(), toMathSATTerm(R),
                        toMathSATTerm(From)));
}

SMTExprRef MathSATSolver::mkSBVtoFPImpl(const SMTExprRef &From,
                                        const SMTSortRef &To,
                                        const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::SBVtoFP, Context, To,
      msat_make_fp_from_sbv(*Context, To->getFPExponentWidth(),
                            To->getFPSignificandWidth(), toMathSATTerm(R),
                            toMathSATTerm(From)));
}

SMTExprRef MathSATSolver::mkUBVtoFPImpl(const SMTExprRef &From,
                                        const SMTSortRef &To,
                                        const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::UBVtoFP, Context, To,
      msat_make_fp_from_ubv(*Context, To->getFPExponentWidth(),
                            To->getFPSignificandWidth(), toMathSATTerm(R),
                            toMathSATTerm(From)));
}

SMTExprRef MathSATSolver::mkFPtoSBVImpl(const SMTExprRef &From,
                                        unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPtoSBV, Context, mkBVSort(ToWidth),
      msat_make_fp_to_bv(*Context, ToWidth, toMathSATTerm(roundingMode),
                         toMathSATTerm(From)));
}

SMTExprRef MathSATSolver::mkFPtoUBVImpl(const SMTExprRef &From,
                                        unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPtoUBV, Context, mkBVSort(ToWidth),
      msat_make_fp_to_ubv(*Context, ToWidth, toMathSATTerm(roundingMode),
                          toMathSATTerm(From)));
}

SMTExprRef MathSATSolver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                             const SMTExprRef &R) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPtoIntegral, Context, From->Sort,
      msat_make_fp_round_to_int(*Context, toMathSATTerm(R),
                                toMathSATTerm(From)));
}

bool MathSATSolver::getBoolImpl(const SMTExprRef &Exp) {
  if (msat_term_is_true(*Context, toMathSATTerm(Exp)))
    return true;

  if (msat_term_is_false(*Context, toMathSATTerm(Exp)))
    return false;

  fatalError("Bool is neither true nor false");
}

static inline std::string getGMPVal(const SMTExprRef &t) {
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

static inline void getMathSATModelRational(const SMTExprRef &t, mpq_t val) {
  msat_term_to_number(*toSolverExpr<MathSATExpr>(*t).Context, toMathSATTerm(t),
                      val);
}

std::string MathSATSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  const SMTExprRef &t = makeExprRef<MathSATExpr>(
      Exp->getKind(), Context, Exp->Sort,
      msat_get_model_value(*Context, toMathSATTerm(Exp)));
  return getGMPVal(t);
}

std::string MathSATSolver::getIntImpl(const SMTExprRef &Exp) {
  if (Exp->isRealSort()) {
    std::string Num, Den;
    getRationalImpl(Exp, Num, Den);
    assert(Den == "1" && "Real value is not integral");
    return Num;
  }

  mpq_t val;
  mpq_init(val);
  const SMTExprRef &t = makeExprRef<MathSATExpr>(
      Exp->getKind(), Context, Exp->Sort,
      msat_get_model_value(*Context, toMathSATTerm(Exp)));
  getMathSATModelRational(t, val);
  assert(mpz_cmp_ui(mpq_denref(val), 1) == 0 && "Expected integer value");
  char *raw_num = mpz_get_str(nullptr, 10, mpq_numref(val));
  std::string num = raw_num;
  void (*gmp_free)(void *, std::size_t);
  mp_get_memory_functions(nullptr, nullptr, &gmp_free);
  gmp_free(raw_num, num.size() + 1);
  mpq_clear(val);
  return num;
}

void MathSATSolver::getRationalImpl(const SMTExprRef &Exp, std::string &Num,
                                    std::string &Den) {
  mpq_t val;
  mpq_init(val);
  const SMTExprRef &t = makeExprRef<MathSATExpr>(
      Exp->getKind(), Context, Exp->Sort,
      msat_get_model_value(*Context, toMathSATTerm(Exp)));
  getMathSATModelRational(t, val);
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

std::string MathSATSolver::getFPInBinImpl(const SMTExprRef &Exp) {
  const SMTExprRef &t = makeExprRef<MathSATExpr>(
      Exp->getKind(), Context, Exp->Sort,
      msat_get_model_value(*Context, toMathSATTerm(Exp)));
  return getGMPVal(t);
}

SMTExprRef MathSATSolver::getArrayElementImpl(const SMTExprRef &Array,
                                              const SMTExprRef &Index) {
  const SMTExprRef &sel = mkArraySelect(Array, Index);
  return makeExprRef<MathSATExpr>(
      sel->getKind(), Context, sel->Sort,
      msat_get_model_value(*Context, toMathSATTerm(sel)));
}

SMTExprRef MathSATSolver::mkBoolImpl(const bool Bool) {
  return makeExprRef<MathSATExpr>(SMTExprKind::BoolConst, Context, mkBoolSort(),
                                  Bool ? msat_make_true(*Context)
                                       : msat_make_false(*Context));
}

SMTExprRef MathSATSolver::mkIntImpl(int64_t v) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::IntConst, Context, mkIntSort(),
      msat_make_number(*Context, std::to_string(v).c_str()));
}

SMTExprRef MathSATSolver::mkIntImpl(const std::string &v) {
  return makeExprRef<MathSATExpr>(SMTExprKind::IntConst, Context, mkIntSort(),
                                  msat_make_number(*Context, v.c_str()));
}

SMTExprRef MathSATSolver::mkRealImpl(const std::string &v) {
  std::string repr = v;
  if (repr.find('/') == std::string::npos &&
      repr.find('.') == std::string::npos)
    repr.append("/1");
  return makeExprRef<MathSATExpr>(SMTExprKind::RealConst, Context, mkRealSort(),
                                  msat_make_number(*Context, repr.c_str()));
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

  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVConst, Context, Sort,
      msat_make_bv_number(*Context, std::to_string(newInt).c_str(),
                          Sort->getWidth(), 10));
}

SMTExprRef MathSATSolver::mkBVFromBinImpl(const std::string &Int,
                                          const SMTSortRef &Sort) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVConst, Context, Sort,
      msat_make_bv_number(*Context, Int.c_str(), Sort->getWidth(), 2));
}

SMTExprRef MathSATSolver::mkSymbolImpl(const std::string &Name,
                                       const SMTSortRef &Sort) {
  msat_decl d = msat_declare_function(*Context, Name.c_str(),
                                      toSolverSort<MathSATSort>(*Sort).Sort);
  assert(!checkExprError(Context, d) &&
         "Invalid function symbol declaration sort");
  if (Sort->isFunctionSort())
    return makeExprRef<MathSATExpr>(SMTExprKind::Symbol, Context, Sort, d);
  return makeExprRef<MathSATExpr>(SMTExprKind::Symbol, Context, Sort,
                                  msat_make_constant(*Context, d));
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

  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPConst, Context,
      mkFPSort(EWidth, FP.length() - EWidth - 1, FPEncoding::Native),
      msat_from_string(*Context, fpSMTStr.c_str()));
}

SMTExprRef MathSATSolver::mkRMImpl(const RM &R) {
  msat_term e;
  switch (R) {
  case RM::ROUND_TO_EVEN:
    e = msat_make_fp_roundingmode_nearest_even(*Context);
    break;
  case RM::ROUND_TO_AWAY:
    std::fprintf(stderr, "MathSAT Error ROUND_TO_AWAY is not supported.\n");
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
  return makeExprRef<MathSATExpr>(SMTExprKind::RMConst, Context,
                                  mkRMSort(FPEncoding::Native), e);
}

SMTExprRef MathSATSolver::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  const SMTExprRef &theNaN = makeExprRef<MathSATExpr>(
      SMTExprKind::FPConst, Context, sort,
      msat_make_fp_nan(*Context, ExpWidth, SigWidth - 1));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef MathSATSolver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  return makeExprRef<MathSATExpr>(
      SMTExprKind::FPConst, Context, sort,
      Sgn ? msat_make_fp_minus_inf(*Context, ExpWidth, SigWidth - 1)
          : msat_make_fp_plus_inf(*Context, ExpWidth, SigWidth - 1));
}

SMTExprRef MathSATSolver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                           const SMTSortRef &To) {
  return makeExprRef<MathSATExpr>(
      SMTExprKind::BVToIEEEFP, Context, To,
      msat_make_fp_from_ieeebv(*Context, To->getFPExponentWidth(),
                               To->getFPSignificandWidth(),
                               toMathSATTerm(Exp)));
}

SMTExprRef MathSATSolver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  const SMTSortRef &to =
      mkFPSort(Exp->Sort->getFPExponentWidth(),
               Exp->Sort->getFPSignificandWidth(), FPEncoding::BV);
  return makeExprRef<MathSATExpr>(
      SMTExprKind::IEEEFPToBV, Context, to,
      msat_make_fp_as_ieeebv(*Context, toMathSATTerm(Exp)));
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
  return makeExprRef<MathSATExpr>(
      SMTExprKind::ArrayConst, Context, sort,
      msat_make_array_const(*Context, toSolverSort<MathSATSort>(*sort).Sort,
                            backend_init));
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

  return makeExprRef<MathSATExpr>(SMTExprKind::Forall, Context, mkBoolSort(),
                                  quantified_body);
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

  return makeExprRef<MathSATExpr>(SMTExprKind::Exists, Context, mkBoolSort(),
                                  quantified_body);
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
  std::string Out;
  dumpImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void MathSATSolver::dumpImpl(std::string &Out) {
  Out.clear();
  size_t num_of_asserted;
  msat_term *asserted_formulas =
      msat_get_asserted_formulas(*Context, &num_of_asserted);

  for (unsigned i = 0; i < num_of_asserted; i++)
    Out += std::string(msat_to_smtlib2(*Context, asserted_formulas[i])) + "\n";
  msat_free(asserted_formulas);
}

void MathSATSolver::dumpModelImpl() {
  std::string Out;
  dumpModelImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void MathSATSolver::dumpModelImpl(std::string &Out) {
  Out.clear();
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
    Out += s;
    Out += " = ";
    msat_free(s);
    s = msat_term_repr(v);
    assert(s && "Error when getting variable value from model");
    Out += s;
    Out += "\n";
    msat_free(s);
  }
  msat_destroy_model_iterator(iter);
}

} // namespace camada

#endif
