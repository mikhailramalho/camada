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

#if SOLVER_BITWUZLA_ENABLED

#include "bitwuzlasolver.h"
#include "camadautil.h"

#include <cassert>
#include <cstdio>
#include <cstring>

namespace camada {

namespace {

void bitwuzlaErrorHandler(const char *msg) { fatalError(msg); }

static inline void bitwuzlaCheck(bool Ok, const char *Message) {
  if (Ok)
    return;
  fatalError(Message);
}

BitwuzlaTerm mkTerm1(BitwuzlaTermManager *tm, BitwuzlaKind kind,
                     const SMTExprRef &Exp) {
  return bitwuzla_mk_term1(tm, kind, toSolverExpr<BitwExpr>(*Exp).Expr);
}

BitwuzlaTerm mkTerm2(BitwuzlaTermManager *tm, BitwuzlaKind kind,
                     const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return bitwuzla_mk_term2(tm, kind, toSolverExpr<BitwExpr>(*LHS).Expr,
                           toSolverExpr<BitwExpr>(*RHS).Expr);
}

BitwuzlaTerm mkTerm3(BitwuzlaTermManager *tm, BitwuzlaKind kind,
                     const SMTExprRef &A, const SMTExprRef &B,
                     const SMTExprRef &C) {
  return bitwuzla_mk_term3(tm, kind, toSolverExpr<BitwExpr>(*A).Expr,
                           toSolverExpr<BitwExpr>(*B).Expr,
                           toSolverExpr<BitwExpr>(*C).Expr);
}

BitwuzlaTerm mkTerm4(BitwuzlaTermManager *tm, BitwuzlaKind kind,
                     const SMTExprRef &A, const SMTExprRef &B,
                     const SMTExprRef &C, const SMTExprRef &D) {
  BitwuzlaTerm args[] = {
      toSolverExpr<BitwExpr>(*A).Expr, toSolverExpr<BitwExpr>(*B).Expr,
      toSolverExpr<BitwExpr>(*C).Expr, toSolverExpr<BitwExpr>(*D).Expr};
  return bitwuzla_mk_term(tm, kind, 4, args);
}

} // namespace

unsigned BitwSort::getWidthFromSolver() const { return getWidth(); }

void BitwSort::dump(std::string &Out) const {
  Out = bitwuzla_sort_to_string(Sort);
  Out += "\n";
}

bool BitwExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return Expr == static_cast<const BitwExpr &>(Other).Expr;
}

void BitwExpr::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void BitwExpr::dump(std::string &Out) const {
  Out = bitwuzla_term_to_string(Expr);
}

BitwuzlaSolver::BitwuzlaSolver() : SMTSolverImpl() {
  initializeContext();
  initializeCommonSingletons();
}

BitwuzlaSolver::~BitwuzlaSolver() {
  invalidateGeneratedObjects();
  destroyContext();
}

void BitwuzlaSolver::initializeContext() {
  TermManager = bitwuzla_term_manager_new();
  Options = bitwuzla_options_new();
  bitwuzla_set_option(Options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  bitwuzla_set_abort_callback(bitwuzlaErrorHandler);
  Context = bitwuzla_new(TermManager, Options);
}

void BitwuzlaSolver::destroyContext() {
  if (Context)
    bitwuzla_delete(Context);
  Context = nullptr;
  if (Options) {
    bitwuzla_options_delete(Options);
    Options = nullptr;
  }
  if (TermManager) {
    bitwuzla_term_manager_delete(TermManager);
    TermManager = nullptr;
  }
}

void BitwuzlaSolver::addConstraintImpl(const SMTExprRef &Exp) {
  bitwuzla_assert(Context, toSolverExpr<BitwExpr>(*Exp).Expr);
}

SMTExprRef BitwuzlaSolver::newExprRefImpl(const SMTExpr &Exp) const {
  return storeExprRef(toSolverExpr<BitwExpr>(Exp));
}

SMTExprRef BitwuzlaSolver::rewrapExprImpl(const SMTExpr &Exp,
                                          const SMTSortRef &Sort,
                                          SMTExprKind Kind) const {
  const auto &Wrapped = toSolverExpr<BitwExpr>(Exp);
  return storeExprRef(BitwExpr(Kind, Wrapped.Context, Sort, Wrapped.Expr));
}

SMTSortRef BitwuzlaSolver::mkBoolSortImpl() {
  return newSortRef<BitwSort>(BitwSort(SMTSortKind::Bool, Context,
                                       bitwuzla_mk_bool_sort(TermManager),
                                       SMTSort::ScalarSortData{1}));
}

SMTSortRef BitwuzlaSolver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<BitwSort>(BitwSort(
      SMTSortKind::BV, Context, bitwuzla_mk_bv_sort(TermManager, BitWidth),
      SMTSort::ScalarSortData{BitWidth}));
}

SMTSortRef BitwuzlaSolver::mkRMSortImpl() {
  return newSortRef<BitwSort>(BitwSort(SMTSortKind::RM, Context,
                                       bitwuzla_mk_rm_sort(TermManager),
                                       SMTSort::ScalarSortData{3}));
}

SMTSortRef BitwuzlaSolver::mkFPSortImpl(const unsigned ExpWidth,
                                        const unsigned SigWidth) {
  return newSortRef<BitwSort>(BitwSort(
      SMTSortKind::FP, Context,
      bitwuzla_mk_fp_sort(TermManager, ExpWidth, SigWidth + 1),
      SMTSort::FPSortData{ExpWidth + SigWidth + 1, ExpWidth, SigWidth}));
}

SMTSortRef BitwuzlaSolver::mkBVFPSortImpl(const unsigned ExpWidth,
                                          const unsigned SigWidth) {
  return newSortRef<BitwSort>(BitwSort(
      SMTSortKind::BVFP, Context,
      bitwuzla_mk_bv_sort(TermManager, ExpWidth + SigWidth + 1),
      SMTSort::FPSortData{ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1}));
}

SMTSortRef BitwuzlaSolver::mkBVRMSortImpl() {
  return newSortRef<BitwSort>(BitwSort(SMTSortKind::BVRM, Context,
                                       bitwuzla_mk_bv_sort(TermManager, 3),
                                       SMTSort::ScalarSortData{3}));
}

SMTSortRef BitwuzlaSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                           const SMTSortRef &ElemSort) {
  return newSortRef<BitwSort>(
      BitwSort(SMTSortKind::Array, Context,
               bitwuzla_mk_array_sort(TermManager,
                                      toSolverSort<BitwSort>(*IndexSort).Sort,
                                      toSolverSort<BitwSort>(*ElemSort).Sort),
               SMTSort::ArraySortData{IndexSort, ElemSort}));
}

SMTSortRef
BitwuzlaSolver::mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                                   const SMTSortRef &CodomainSort) {
  std::vector<BitwuzlaSort> Domain;
  Domain.reserve(DomainSorts.size());
  for (const auto &Sort : DomainSorts)
    Domain.push_back(toSolverSort<BitwSort>(*Sort).Sort);
  return newSortRef<BitwSort>(
      BitwSort(SMTSortKind::Function, Context,
               bitwuzla_mk_fun_sort(TermManager, Domain.size(), Domain.data(),
                                    toSolverSort<BitwSort>(*CodomainSort).Sort),
               SMTSort::FunctionSortData{DomainSorts, CodomainSort}));
}

SMTExprRef BitwuzlaSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(SMTExprKind::BVNeg, Context, Exp->Sort,
                               mkTerm1(TermManager, BITWUZLA_KIND_BV_NEG, Exp));
}

SMTExprRef BitwuzlaSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(SMTExprKind::BVNot, Context, Exp->Sort,
                               mkTerm1(TermManager, BITWUZLA_KIND_BV_NOT, Exp));
}

SMTExprRef BitwuzlaSolver::mkNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(SMTExprKind::Not, Context, Exp->Sort,
                               mkTerm1(TermManager, BITWUZLA_KIND_NOT, Exp));
}

SMTExprRef BitwuzlaSolver::mkBVRedOrImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVRedOr, Context, mkBVSort(1),
      mkTerm1(TermManager, BITWUZLA_KIND_BV_REDOR, Exp));
}

SMTExprRef BitwuzlaSolver::mkBVRedAndImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVRedAnd, Context, mkBVSort(1),
      mkTerm1(TermManager, BITWUZLA_KIND_BV_REDAND, Exp));
}

SMTExprRef BitwuzlaSolver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(SMTExprKind::FPAbs, Context, Exp->Sort,
                               mkTerm1(TermManager, BITWUZLA_KIND_FP_ABS, Exp));
}

SMTExprRef BitwuzlaSolver::mkFPNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(SMTExprKind::FPNeg, Context, Exp->Sort,
                               mkTerm1(TermManager, BITWUZLA_KIND_FP_NEG, Exp));
}

SMTExprRef BitwuzlaSolver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPIsInfinite, Context, mkBoolSort(),
      mkTerm1(TermManager, BITWUZLA_KIND_FP_IS_INF, Exp));
}

SMTExprRef BitwuzlaSolver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPIsNaN, Context, mkBoolSort(),
      mkTerm1(TermManager, BITWUZLA_KIND_FP_IS_NAN, Exp));
}

SMTExprRef BitwuzlaSolver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPIsDenormal, Context, mkBoolSort(),
      mkTerm1(TermManager, BITWUZLA_KIND_FP_IS_SUBNORMAL, Exp));
}

SMTExprRef BitwuzlaSolver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPIsNormal, Context, mkBoolSort(),
      mkTerm1(TermManager, BITWUZLA_KIND_FP_IS_NORMAL, Exp));
}

SMTExprRef BitwuzlaSolver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPIsZero, Context, mkBoolSort(),
      mkTerm1(TermManager, BITWUZLA_KIND_FP_IS_ZERO, Exp));
}

SMTExprRef BitwuzlaSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVAdd, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_ADD, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVSub, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SUB, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVMul, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_MUL, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVSRem, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SREM, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVURem, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_UREM, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVSDiv, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SDIV, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVUDiv, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_UDIV, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVShl, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SHL, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVAshr, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_ASHR, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVLshr, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SHR, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVXor, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_XOR, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVOrImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVOr, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_OR, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVAnd, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_AND, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVXnorImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVXnor, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_XNOR, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVNorImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVNor, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_NOR, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVNandImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVNand, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_BV_NAND, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVUlt, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_ULT, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVSlt, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SLT, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVUgtImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVUgt, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_UGT, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVSgtImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVSgt, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SGT, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVUle, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_ULE, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVSle, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SLE, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVUgeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVUge, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_UGE, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVSgeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVSge, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_SGE, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkImpliesImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::Implies, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_IMPLIES, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkAndImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::And, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_AND, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkOrImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::Or, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_OR, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkXorImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::Xor, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_XOR, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkEqualImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::Equal, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_EQUAL, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                          const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVConcat, Context,
      mkBVSort(LHS->getWidth() + RHS->getWidth()),
      mkTerm2(TermManager, BITWUZLA_KIND_BV_CONCAT, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPRemImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPRem, Context, LHS->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_FP_REM, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPLtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPLt, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_FP_LT, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPGtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPGt, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_FP_GT, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPLeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPLe, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_FP_LEQ, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPGeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPGe, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_FP_GEQ, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPEqualImpl(const SMTExprRef &LHS,
                                         const SMTExprRef &RHS) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPEqual, Context, mkBoolSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_FP_EQUAL, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkIteImpl(const SMTExprRef &Cond,
                                     const SMTExprRef &T, const SMTExprRef &F) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::Ite, Context, T->Sort,
      mkTerm3(TermManager, BITWUZLA_KIND_ITE, Cond, T, F));
}

SMTExprRef BitwuzlaSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVSignExt, Context, mkBVSort(i + Exp->getWidth()),
      bitwuzla_mk_term1_indexed1(TermManager, BITWUZLA_KIND_BV_SIGN_EXTEND,
                                 toSolverExpr<BitwExpr>(*Exp).Expr, i));
}

SMTExprRef BitwuzlaSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVZeroExt, Context, mkBVSort(i + Exp->getWidth()),
      bitwuzla_mk_term1_indexed1(TermManager, BITWUZLA_KIND_BV_ZERO_EXTEND,
                                 toSolverExpr<BitwExpr>(*Exp).Expr, i));
}

SMTExprRef BitwuzlaSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                           const SMTExprRef &Exp) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVExtract, Context, mkBVSort(High - Low + 1),
      bitwuzla_mk_term1_indexed2(TermManager, BITWUZLA_KIND_BV_EXTRACT,
                                 toSolverExpr<BitwExpr>(*Exp).Expr, High, Low));
}

SMTExprRef BitwuzlaSolver::mkFPMulImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS,
                                       const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPMul, Context, LHS->Sort,
      mkTerm3(TermManager, BITWUZLA_KIND_FP_MUL, R, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS,
                                       const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPDiv, Context, LHS->Sort,
      mkTerm3(TermManager, BITWUZLA_KIND_FP_DIV, R, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPAddImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS,
                                       const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPAdd, Context, LHS->Sort,
      mkTerm3(TermManager, BITWUZLA_KIND_FP_ADD, R, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPSubImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS,
                                       const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPSub, Context, LHS->Sort,
      mkTerm3(TermManager, BITWUZLA_KIND_FP_SUB, R, LHS, RHS));
}

SMTExprRef BitwuzlaSolver::mkFPSqrtImpl(const SMTExprRef &Exp,
                                        const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPSqrt, Context, Exp->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_FP_SQRT, R, Exp));
}

SMTExprRef BitwuzlaSolver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                       const SMTExprRef &Z,
                                       const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPFMA, Context, X->Sort,
      mkTerm4(TermManager, BITWUZLA_KIND_FP_FMA, R, X, Y, Z));
}

SMTExprRef BitwuzlaSolver::mkFPtoFPImpl(const SMTExprRef &From,
                                        const SMTSortRef &To,
                                        const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPtoFP, Context, To,
      bitwuzla_mk_term2_indexed2(
          TermManager, BITWUZLA_KIND_FP_TO_FP_FROM_FP,
          toSolverExpr<BitwExpr>(*R).Expr, toSolverExpr<BitwExpr>(*From).Expr,
          To->getFPExponentWidth(), To->getFPSignificandWidth() + 1));
}

SMTExprRef BitwuzlaSolver::mkSBVtoFPImpl(const SMTExprRef &From,
                                         const SMTSortRef &To,
                                         const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::SBVtoFP, Context, To,
      bitwuzla_mk_term2_indexed2(
          TermManager, BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
          toSolverExpr<BitwExpr>(*R).Expr, toSolverExpr<BitwExpr>(*From).Expr,
          To->getFPExponentWidth(), To->getFPSignificandWidth() + 1));
}

SMTExprRef BitwuzlaSolver::mkUBVtoFPImpl(const SMTExprRef &From,
                                         const SMTSortRef &To,
                                         const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::UBVtoFP, Context, To,
      bitwuzla_mk_term2_indexed2(
          TermManager, BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
          toSolverExpr<BitwExpr>(*R).Expr, toSolverExpr<BitwExpr>(*From).Expr,
          To->getFPExponentWidth(), To->getFPSignificandWidth() + 1));
}

SMTExprRef BitwuzlaSolver::mkFPtoSBVImpl(const SMTExprRef &From,
                                         unsigned ToWidth) {
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPtoSBV, Context, mkBVSort(ToWidth),
      bitwuzla_mk_term2_indexed1(TermManager, BITWUZLA_KIND_FP_TO_SBV,
                                 toSolverExpr<BitwExpr>(*roundingMode).Expr,
                                 toSolverExpr<BitwExpr>(*From).Expr, ToWidth));
}

SMTExprRef BitwuzlaSolver::mkFPtoUBVImpl(const SMTExprRef &From,
                                         unsigned ToWidth) {
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPtoUBV, Context, mkBVSort(ToWidth),
      bitwuzla_mk_term2_indexed1(TermManager, BITWUZLA_KIND_FP_TO_UBV,
                                 toSolverExpr<BitwExpr>(*roundingMode).Expr,
                                 toSolverExpr<BitwExpr>(*From).Expr, ToWidth));
}

SMTExprRef BitwuzlaSolver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                              const SMTExprRef &R) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPtoIntegral, Context, From->Sort,
      mkTerm2(TermManager, BITWUZLA_KIND_FP_RTI, R, From));
}

SMTExprRef BitwuzlaSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                             const SMTExprRef &Index) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::ArraySelect, Context, Array->Sort->getElementSort(),
      mkTerm2(TermManager, BITWUZLA_KIND_ARRAY_SELECT, Array, Index));
}

SMTExprRef BitwuzlaSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                            const SMTExprRef &Index,
                                            const SMTExprRef &Element) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::ArrayStore, Context, Array->Sort,
      mkTerm3(TermManager, BITWUZLA_KIND_ARRAY_STORE, Array, Index, Element));
}

SMTExprRef BitwuzlaSolver::mkApplyImpl(const SMTExprRef &Function,
                                       const std::vector<SMTExprRef> &Args) {
  std::vector<BitwuzlaTerm> ApplyArgs;
  ApplyArgs.reserve(Args.size() + 1);
  ApplyArgs.push_back(toSolverExpr<BitwExpr>(*Function).Expr);
  for (const auto &Arg : Args)
    ApplyArgs.push_back(toSolverExpr<BitwExpr>(*Arg).Expr);
  return makeExprRef<BitwExpr>(
      SMTExprKind::Apply, Context, Function->Sort->getCodomainSort(),
      bitwuzla_mk_term(TermManager, BITWUZLA_KIND_APPLY, ApplyArgs.size(),
                       ApplyArgs.data()));
}

bool BitwuzlaSolver::getBoolImpl(const SMTExprRef &Exp) {
  const char *result = bitwuzla_term_to_string(
      bitwuzla_get_value(Context, toSolverExpr<BitwExpr>(*Exp).Expr));

  bitwuzlaCheck(result != nullptr,
                "Bitwuzla returned null boolean value string");
  if (!strcmp(result, "true"))
    return true;
  if (!strcmp(result, "false"))
    return false;

  fatalError("Bool is neither true nor false");
}

std::string BitwuzlaSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  const char *result = bitwuzla_term_value_get_str(
      bitwuzla_get_value(Context, toSolverExpr<BitwExpr>(*Exp).Expr));
  return result ? std::string(result) : std::string();
}

std::string BitwuzlaSolver::getFPInBinImpl(const SMTExprRef &Exp) {
  const char *result = bitwuzla_term_value_get_str_fmt(
      bitwuzla_get_value(Context, toSolverExpr<BitwExpr>(*Exp).Expr), 2);
  return result ? std::string(result) : std::string();
}

SMTExprRef BitwuzlaSolver::getArrayElementImpl(const SMTExprRef &Array,
                                               const SMTExprRef &Index) {
  const SMTExprRef &select = mkArraySelect(Array, Index);
  return makeExprRef<BitwExpr>(
      select->getKind(), Context, select->Sort,
      bitwuzla_get_value(Context, toSolverExpr<BitwExpr>(*select).Expr));
}

SMTExprRef BitwuzlaSolver::mkBoolImpl(const bool b) {
  return makeExprRef<BitwExpr>(SMTExprKind::BoolConst, Context, mkBoolSort(),
                               b ? bitwuzla_mk_true(TermManager)
                                 : bitwuzla_mk_false(TermManager));
}

SMTExprRef BitwuzlaSolver::mkBVFromDecImpl(const int64_t Int,
                                           const SMTSortRef &Sort) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVConst, Context, Sort,
      bitwuzla_mk_bv_value(TermManager, toSolverSort<BitwSort>(*Sort).Sort,
                           toTwosComplementBin(Int, Sort->getWidth()).c_str(),
                           2));
}

SMTExprRef BitwuzlaSolver::mkBVFromBinImpl(const std::string &Int,
                                           const SMTSortRef &Sort) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVConst, Context, Sort,
      bitwuzla_mk_bv_value(TermManager, toSolverSort<BitwSort>(*Sort).Sort,
                           Int.c_str(), 2));
}

SMTExprRef BitwuzlaSolver::mkFPFromBinImpl(const std::string &FP,
                                           unsigned EWidth) {
  const SMTExprRef &sgn = SMTSolverImpl::mkBVFromBin({FP[0]});
  const SMTExprRef &exp = SMTSolverImpl::mkBVFromBin(FP.substr(1, EWidth));
  const SMTExprRef &sig = SMTSolverImpl::mkBVFromBin(FP.substr(1 + EWidth));
  const unsigned SWidth = FP.length() - EWidth - 1;
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPConst, Context,
      mkFPSort(EWidth, SWidth, FPEncoding::Native),
      mkTerm3(TermManager, BITWUZLA_KIND_FP_FP, sgn, exp, sig));
}

SMTExprRef BitwuzlaSolver::mkRMImpl(const RM &R) {
  BitwuzlaRoundingMode mode;
  switch (R) {
  default:
    fatalError("Unsupported floating-point semantics.");
  case RM::ROUND_TO_EVEN:
    mode = BITWUZLA_RM_RNE;
    break;
  case RM::ROUND_TO_AWAY:
    mode = BITWUZLA_RM_RNA;
    break;
  case RM::ROUND_TO_PLUS_INF:
    mode = BITWUZLA_RM_RTP;
    break;
  case RM::ROUND_TO_MINUS_INF:
    mode = BITWUZLA_RM_RTN;
    break;
  case RM::ROUND_TO_ZERO:
    mode = BITWUZLA_RM_RTZ;
    break;
  }
  return makeExprRef<BitwExpr>(SMTExprKind::RMConst, Context,
                               mkRMSort(FPEncoding::Native),
                               bitwuzla_mk_rm_value(TermManager, mode));
}

SMTExprRef BitwuzlaSolver::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                     const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  const SMTExprRef &theNaN = makeExprRef<BitwExpr>(
      SMTExprKind::FPConst, Context, sort,
      bitwuzla_mk_fp_nan(TermManager, toSolverSort<BitwSort>(*sort).Sort));
  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef BitwuzlaSolver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                     const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  return makeExprRef<BitwExpr>(
      SMTExprKind::FPConst, Context, sort,
      Sgn ? bitwuzla_mk_fp_neg_inf(TermManager,
                                   toSolverSort<BitwSort>(*sort).Sort)
          : bitwuzla_mk_fp_pos_inf(TermManager,
                                   toSolverSort<BitwSort>(*sort).Sort));
}

SMTExprRef BitwuzlaSolver::mkSymbolImpl(const std::string &Name,
                                        const SMTSortRef &Sort) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::Symbol, Context, Sort,
      bitwuzla_mk_const(TermManager, toSolverSort<BitwSort>(*Sort).Sort,
                        Name.c_str()));
}

SMTExprRef BitwuzlaSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                            const SMTExprRef &InitValue) {
  const SMTSortRef &sort = mkArraySort(IndexSort, InitValue->Sort);
  return makeExprRef<BitwExpr>(
      SMTExprKind::ArrayConst, Context, sort,
      bitwuzla_mk_const_array(TermManager, toSolverSort<BitwSort>(*sort).Sort,
                              toSolverExpr<BitwExpr>(*InitValue).Expr));
}

SMTExprRef BitwuzlaSolver::mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                        const SMTExprRef &Body) {
  std::vector<BitwuzlaTerm> old_terms;
  std::vector<BitwuzlaTerm> bound_vars;
  old_terms.reserve(Vars.size());
  bound_vars.reserve(Vars.size());

  for (std::size_t i = 0; i < Vars.size(); ++i) {
    const SMTExprRef &Var = Vars[i];
    old_terms.push_back(toSolverExpr<BitwExpr>(*Var).Expr);
    bound_vars.push_back(
        bitwuzla_mk_var(TermManager, toSolverSort<BitwSort>(*Var->Sort).Sort,
                        ("__CAMADA_qvar" + std::to_string(i)).c_str()));
  }

  BitwuzlaTerm substituted_body = bitwuzla_substitute_term(
      toSolverExpr<BitwExpr>(*Body).Expr, old_terms.size(), old_terms.data(),
      bound_vars.data());
  std::vector<BitwuzlaTerm> args = bound_vars;
  args.push_back(substituted_body);
  return makeExprRef<BitwExpr>(SMTExprKind::Forall, Context, mkBoolSort(),
                               bitwuzla_mk_term(TermManager,
                                                BITWUZLA_KIND_FORALL,
                                                args.size(), args.data()));
}

SMTExprRef BitwuzlaSolver::mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                        const SMTExprRef &Body) {
  std::vector<BitwuzlaTerm> old_terms;
  std::vector<BitwuzlaTerm> bound_vars;
  old_terms.reserve(Vars.size());
  bound_vars.reserve(Vars.size());

  for (std::size_t i = 0; i < Vars.size(); ++i) {
    const SMTExprRef &Var = Vars[i];
    old_terms.push_back(toSolverExpr<BitwExpr>(*Var).Expr);
    bound_vars.push_back(
        bitwuzla_mk_var(TermManager, toSolverSort<BitwSort>(*Var->Sort).Sort,
                        ("__CAMADA_qvar" + std::to_string(i)).c_str()));
  }

  BitwuzlaTerm substituted_body = bitwuzla_substitute_term(
      toSolverExpr<BitwExpr>(*Body).Expr, old_terms.size(), old_terms.data(),
      bound_vars.data());
  std::vector<BitwuzlaTerm> args = bound_vars;
  args.push_back(substituted_body);
  return makeExprRef<BitwExpr>(SMTExprKind::Exists, Context, mkBoolSort(),
                               bitwuzla_mk_term(TermManager,
                                                BITWUZLA_KIND_EXISTS,
                                                args.size(), args.data()));
}

SMTExprRef BitwuzlaSolver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                            const SMTSortRef &To) {
  return makeExprRef<BitwExpr>(
      SMTExprKind::BVToIEEEFP, Context, To,
      bitwuzla_mk_term1_indexed2(TermManager, BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                 toSolverExpr<BitwExpr>(*Exp).Expr,
                                 To->getFPExponentWidth(),
                                 To->getFPSignificandWidth() + 1));
}

SMTExprRef BitwuzlaSolver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  const std::string name = "__CAMADA_ieeebv" + std::to_string(ToBVCounter++);
  const SMTSortRef &to =
      mkFPSort(Exp->Sort->getFPExponentWidth(),
               Exp->Sort->getFPSignificandWidth(), FPEncoding::BV);
  const SMTExprRef &newSymbol = mkSymbol(name, to);
  addConstraint(mkEqual(Exp, mkBVToIEEEFP(newSymbol, Exp->Sort)));
  return newSymbol;
}

checkResult BitwuzlaSolver::checkImpl() {
  BitwuzlaResult res = bitwuzla_check_sat(Context);
  if (res == BITWUZLA_SAT)
    return checkResult::SAT;
  if (res == BITWUZLA_UNSAT)
    return checkResult::UNSAT;
  return checkResult::UNKNOWN;
}

void BitwuzlaSolver::resetImpl() {
  destroyContext();
  initializeContext();
}

void BitwuzlaSolver::pushImpl(unsigned nscopes) {
  bitwuzla_push(Context, nscopes);
}

void BitwuzlaSolver::popImpl(unsigned nscopes) {
  bitwuzla_pop(Context, nscopes);
}

std::string BitwuzlaSolver::getSolverNameAndVersion() const {
  return std::string("Bitwuzla v").append(bitwuzla_version());
}

void BitwuzlaSolver::dumpImpl() {
  std::string Out;
  dumpImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void BitwuzlaSolver::dumpImpl(std::string &Out) {
  char *Buffer = nullptr;
  size_t Size = 0;
  FILE *Stream = open_memstream(&Buffer, &Size);
  bitwuzlaCheck(Stream != nullptr,
                "Failed to open memory stream for Bitwuzla dump");
  bitwuzla_print_formula(Context, "smt2", Stream, 2);
  fclose(Stream);
  Out.assign(Buffer, Size);
  free(Buffer);
}

void BitwuzlaSolver::dumpModelImpl() {
  std::string Out;
  dumpModelImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void BitwuzlaSolver::dumpModelImpl(std::string &Out) {
  Out.clear();
  for (const auto &entry : SymbolExprCache) {
    const BitwuzlaTerm term = toSolverExpr<BitwExpr>(*entry.second).Expr;
    Out += "(define-fun ";
    Out += bitwuzla_term_get_symbol(term);
    Out += " () ";
    Out += bitwuzla_sort_to_string(bitwuzla_term_get_sort(term));
    Out += " ";
    Out += bitwuzla_term_to_string(bitwuzla_get_value(Context, term));
    Out += ")\n";
  }
}

} // namespace camada

#endif
