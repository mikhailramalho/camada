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
#if SOLVER_STP_ENABLED

#include "camadautil.h"
#include "stpsolver.h"

#include <algorithm>
#include <cassert>
#include <cstdio>

namespace camada {

namespace {

// Function used to report errors
void STPErrorHandler(const char *msg) { fatalError(msg); }

} // namespace

STPExpr::~STPExpr() {
  if (OwnsExpr && Expr != nullptr)
    STP::vc_DeleteExpr(Expr);
}

unsigned STPSort::getWidthFromSolver() const {
  if (isBoolSort())
    return 1;
  return STP::vc_getValueSize(Context, Sort);
}

void STPSort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void STPSort::dump(std::string &Out) const {
  char *s = STP::typeString(Sort);
  Out = s;
  Out += "\n";
  free(s);
}

bool STPExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return (STP::getExprID(Expr) ==
          STP::getExprID(static_cast<const STPExpr &>(Other).Expr));
}

void STPExpr::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void STPExpr::dump(std::string &Out) const {
  char *s = STP::exprString(Expr);
  Out = s;
  Out += "\n";
  free(s);
}

STPSolver::STPSolver() : Context(STP::vc_createValidityChecker()) {
  STP::vc_registerErrorHandler(STPErrorHandler);
  initializeCommonSingletons();
}

STPSolver::STPSolver(STPContextRef C) : Context(*C) {
  initializeCommonSingletons();
}

STPSolver::~STPSolver() {
  invalidateGeneratedObjects();
  if (Context)
    STP::vc_Destroy(Context);
  Context = nullptr;
}

void STPSolver::addConstraintImpl(const SMTExprRef &Exp) {
  STP::vc_assertFormula(Context, toSolverExpr<STPExpr>(*Exp).Expr);
}

SMTExprRef STPSolver::newExprRefImpl(const SMTExpr &Exp) const {
  // Store a fresh wrapper that owns the underlying STP term. STP leaks
  // ordinary constructed terms unless the final arena-held wrapper deletes
  // them via `vc_DeleteExpr`.
  const auto &Wrapped = toSolverExpr<STPExpr>(Exp);
  return makeExprRef<STPExpr>(Exp.getKind(), Wrapped.Context, Exp.Sort,
                              Wrapped.Expr, true);
}

SMTExprRef STPSolver::rewrapExprImpl(const SMTExpr &Exp, const SMTSortRef &Sort,
                                     SMTExprKind Kind) const {
  const auto &Wrapped = toSolverExpr<STPExpr>(Exp);
  return makeExprRef<STPExpr>(Kind, Wrapped.Context, Sort, Wrapped.Expr, false);
}

SMTSortRef STPSolver::mkBoolSortImpl() {
  return makeSortRef<STPSort>(STPSort(SMTSortKind::Bool, &Context,
                                     STP::vc_boolType(Context),
                                     SMTSort::ScalarSortData{1}));
}

SMTSortRef STPSolver::mkBVSortImpl(unsigned BitWidth) {
  return makeSortRef<STPSort>(STPSort(SMTSortKind::BV, &Context,
                                     STP::vc_bvType(Context, BitWidth),
                                     SMTSort::ScalarSortData{BitWidth}));
}

SMTSortRef STPSolver::mkBVFPSortImpl(const unsigned ExpWidth,
                                     const unsigned SigWidth) {
  return makeSortRef<STPSort>(STPSort(
      SMTSortKind::BVFP, &Context,
      STP::vc_bvType(Context, ExpWidth + SigWidth + 1),
      SMTSort::FPSortData{ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1}));
}

SMTSortRef STPSolver::mkBVRMSortImpl() {
  return makeSortRef<STPSort>(STPSort(SMTSortKind::BVRM, &Context,
                                     STP::vc_bvType(Context, 3),
                                     SMTSort::ScalarSortData{3}));
}

SMTSortRef STPSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                      const SMTSortRef &ElemSort) {
  const SMTSortRef &backend_elem_sort =
      ElemSort->isBoolSort() ? mkBVSort(1) : ElemSort;
  return makeSortRef<STPSort>(
      STPSort(SMTSortKind::Array, &Context,
              STP::vc_arrayType(Context, toSolverSort<STPSort>(*IndexSort).Sort,
                                toSolverSort<STPSort>(*backend_elem_sort).Sort),
              SMTSort::ArraySortData{IndexSort, ElemSort}));
}

SMTExprRef STPSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVNeg, &Context, Exp->Sort,
      STP::vc_bvUMinusExpr(Context, toSolverExpr<STPExpr>(*Exp).Expr));
}

SMTExprRef STPSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVNot, &Context, Exp->Sort,
      STP::vc_bvNotExpr(Context, toSolverExpr<STPExpr>(*Exp).Expr));
}

SMTExprRef STPSolver::mkNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<STPExpr>(
      SMTExprKind::Not, &Context, Exp->Sort,
      STP::vc_notExpr(Context, toSolverExpr<STPExpr>(*Exp).Expr));
}

SMTExprRef STPSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVAdd, &Context, LHS->Sort,
      STP::vc_bvPlusExpr(Context, LHS->getWidth(),
                         toSolverExpr<STPExpr>(*LHS).Expr,
                         toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVSub, &Context, LHS->Sort,
      STP::vc_bvMinusExpr(Context, LHS->getWidth(),
                          toSolverExpr<STPExpr>(*LHS).Expr,
                          toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVMul, &Context, LHS->Sort,
      STP::vc_bvMultExpr(Context, LHS->getWidth(),
                         toSolverExpr<STPExpr>(*LHS).Expr,
                         toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVSRem, &Context, LHS->Sort,
      STP::vc_sbvModExpr(Context, LHS->getWidth(),
                         toSolverExpr<STPExpr>(*LHS).Expr,
                         toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVURem, &Context, LHS->Sort,
      STP::vc_bvModExpr(Context, LHS->getWidth(),
                        toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVSDiv, &Context, LHS->Sort,
      STP::vc_sbvDivExpr(Context, LHS->getWidth(),
                         toSolverExpr<STPExpr>(*LHS).Expr,
                         toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVUDiv, &Context, LHS->Sort,
      STP::vc_bvDivExpr(Context, LHS->getWidth(),
                        toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVShl, &Context, LHS->Sort,
      STP::vc_bvLeftShiftExprExpr(Context, LHS->getWidth(),
                                  toSolverExpr<STPExpr>(*LHS).Expr,
                                  toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVAshr, &Context, LHS->Sort,
      STP::vc_bvSignedRightShiftExprExpr(Context, LHS->getWidth(),
                                         toSolverExpr<STPExpr>(*LHS).Expr,
                                         toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVLshr, &Context, LHS->Sort,
      STP::vc_bvRightShiftExprExpr(Context, LHS->getWidth(),
                                   toSolverExpr<STPExpr>(*LHS).Expr,
                                   toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVXor, &Context, LHS->Sort,
      STP::vc_bvXorExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVOr, &Context, LHS->Sort,
      STP::vc_bvOrExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                       toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVAnd, &Context, LHS->Sort,
      STP::vc_bvAndExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVUlt, &Context, mkBoolSort(),
      STP::vc_bvLtExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                       toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVSlt, &Context, mkBoolSort(),
      STP::vc_sbvLtExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVUgtImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVUgt, &Context, mkBoolSort(),
      STP::vc_bvGtExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                       toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVSgtImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVSgt, &Context, mkBoolSort(),
      STP::vc_sbvGtExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVUle, &Context, mkBoolSort(),
      STP::vc_bvLeExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                       toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVSle, &Context, mkBoolSort(),
      STP::vc_sbvLeExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVUgeImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVUge, &Context, mkBoolSort(),
      STP::vc_bvGeExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                       toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkBVSgeImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVSge, &Context, mkBoolSort(),
      STP::vc_sbvGeExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkImpliesImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::Implies, &Context, mkBoolSort(),
      STP::vc_impliesExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                          toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::And, &Context, mkBoolSort(),
      STP::vc_andExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                      toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(SMTExprKind::Or, &Context, mkBoolSort(),
                              STP::vc_orExpr(Context,
                                             toSolverExpr<STPExpr>(*LHS).Expr,
                                             toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::Xor, &Context, mkBoolSort(),
      STP::vc_xorExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                      toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkEqualImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  if (LHS->isArraySort()) {
    // STP does not support array extensionality, so let's create a free
    // variable
    const std::string name =
        "__CAMADA_index" + std::to_string(ConstArrayCounter++);
    const SMTExprRef &index = mkSymbol(name, LHS->Sort->getIndexSort());

    // and do select(A,i) == select(B,i)
    return mkEqual(mkArraySelect(LHS, index), mkArraySelect(RHS, index));
  }

  if (LHS->isBoolSort())
    return makeExprRef<STPExpr>(
        SMTExprKind::Equal, &Context, mkBoolSort(),
        STP::vc_iffExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                        toSolverExpr<STPExpr>(*RHS).Expr));

  return makeExprRef<STPExpr>(SMTExprKind::Equal, &Context, mkBoolSort(),
                              STP::vc_eqExpr(Context,
                                             toSolverExpr<STPExpr>(*LHS).Expr,
                                             toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                const SMTExprRef &F) {
  return makeExprRef<STPExpr>(SMTExprKind::Ite, &Context, T->Sort,
                              STP::vc_iteExpr(Context,
                                              toSolverExpr<STPExpr>(*Cond).Expr,
                                              toSolverExpr<STPExpr>(*T).Expr,
                                              toSolverExpr<STPExpr>(*F).Expr));
}

SMTExprRef STPSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVSignExt, &Context, mkBVSort(i + Exp->getWidth()),
      STP::vc_bvSignExtend(Context, toSolverExpr<STPExpr>(*Exp).Expr,
                           i + Exp->getWidth()));
}

SMTExprRef STPSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  const SMTExprRef &z = SMTSolverImpl::mkBVFromDec(0, i);
  return mkBVConcat(z, Exp);
}

SMTExprRef STPSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                      const SMTExprRef &Exp) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVExtract, &Context, mkBVSort(High - Low + 1),
      STP::vc_bvExtract(Context, toSolverExpr<STPExpr>(*Exp).Expr, High, Low));
}

SMTExprRef STPSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVConcat, &Context,
      mkBVSort(LHS->getWidth() + RHS->getWidth()),
      STP::vc_bvConcatExpr(Context, toSolverExpr<STPExpr>(*LHS).Expr,
                           toSolverExpr<STPExpr>(*RHS).Expr));
}

SMTExprRef STPSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                        const SMTExprRef &Index) {
  const SMTSortRef &elementSort = Array->Sort->getElementSort();
  const SMTExprRef &read = makeExprRef<STPExpr>(
      SMTExprKind::ArraySelect, &Context,
      elementSort->isBoolSort() ? mkBVSort(1) : elementSort,
      STP::vc_readExpr(Context, toSolverExpr<STPExpr>(*Array).Expr,
                       toSolverExpr<STPExpr>(*Index).Expr));
  if (elementSort->isBoolSort()) {
    const SMTExprRef &one = mkBVFromDec(1, 1);
    return makeExprRef<STPExpr>(
        SMTExprKind::ArraySelect, &Context, mkBoolSort(),
        STP::vc_eqExpr(Context, toSolverExpr<STPExpr>(*read).Expr,
                       toSolverExpr<STPExpr>(*one).Expr));
  }

  return read;
}

SMTExprRef STPSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                       const SMTExprRef &Index,
                                       const SMTExprRef &Element) {
  STP::Expr backend_element = toSolverExpr<STPExpr>(*Element).Expr;
  if (Array->Sort->getElementSort()->isBoolSort()) {
    const SMTExprRef &one = mkBVFromDec(1, 1);
    const SMTExprRef &zero = mkBVFromDec(0, 1);
    const SMTExprRef &ite = makeExprRef<STPExpr>(
        SMTExprKind::Ite, &Context, mkBVSort(1),
        STP::vc_iteExpr(Context, toSolverExpr<STPExpr>(*Element).Expr,
                        toSolverExpr<STPExpr>(*one).Expr,
                        toSolverExpr<STPExpr>(*zero).Expr));
    backend_element = toSolverExpr<STPExpr>(*ite).Expr;
  }

  STP::Expr written =
      STP::vc_writeExpr(Context, toSolverExpr<STPExpr>(*Array).Expr,
                        toSolverExpr<STPExpr>(*Index).Expr, backend_element);

  return makeExprRef<STPExpr>(SMTExprKind::ArrayStore, &Context, Array->Sort,
                              written);
}

bool STPSolver::getBoolImpl(const SMTExprRef &Exp) {
  STP::Expr value =
      STP::vc_getCounterExample(Context, toSolverExpr<STPExpr>(*Exp).Expr);
  STP::Expr bv_value = STP::vc_boolToBVExpr(Context, value);
  const bool result = STP::getBVUnsigned(bv_value) != 0;
  STP::vc_DeleteExpr(bv_value);
  STP::vc_DeleteExpr(value);
  return result;
}

std::string STPSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  STP::Expr value =
      STP::vc_getCounterExample(Context, toSolverExpr<STPExpr>(*Exp).Expr);
  char *buf;
  unsigned long len;
  STP::vc_printBVBitStringToBuffer(value, &buf, &len);
  std::string bv(buf);
  free(buf);
  STP::vc_DeleteExpr(value);
  return bv;
}

SMTExprRef STPSolver::getArrayElementImpl(const SMTExprRef &Array,
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

SMTExprRef STPSolver::mkBoolImpl(const bool b) {
  return makeExprRef<STPExpr>(SMTExprKind::BoolConst, &Context, mkBoolSort(),
                              b ? STP::vc_trueExpr(Context)
                                : STP::vc_falseExpr(Context));
}

SMTExprRef STPSolver::mkBVFromDecImpl(const int64_t Int,
                                      const SMTSortRef &Sort) {
  return makeExprRef<STPExpr>(
      SMTExprKind::BVConst, &Context, Sort,
      STP::vc_bvConstExprFromStr(
          Context, toTwosComplementBin(Int, Sort->getWidth()).c_str()));
}

SMTExprRef STPSolver::mkBVFromBinImpl(const std::string &Int,
                                      const SMTSortRef &Sort) {
  return makeExprRef<STPExpr>(SMTExprKind::BVConst, &Context, Sort,
                              STP::vc_bvConstExprFromStr(Context, Int.c_str()));
}

SMTExprRef STPSolver::mkSymbolImpl(const std::string &Name,
                                   const SMTSortRef &Sort) {

  std::string new_name = Name;
  std::replace(new_name.begin(), new_name.end(), '@', '_');
  std::replace(new_name.begin(), new_name.end(), '!', '_');
  std::replace(new_name.begin(), new_name.end(), '&', '_');
  std::replace(new_name.begin(), new_name.end(), '#', '_');
  std::replace(new_name.begin(), new_name.end(), '$', '_');
  std::replace(new_name.begin(), new_name.end(), ':', '_');

  return makeExprRef<STPExpr>(
      SMTExprKind::Symbol, &Context, Sort,
      STP::vc_varExpr(Context, new_name.c_str(),
                      toSolverSort<STPSort>(*Sort).Sort));
}

SMTExprRef STPSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                       const SMTExprRef &InitValue) {
  const std::string name = "__CAMADA_arr" + std::to_string(ConstArrayCounter++);
  SMTExprRef arr = mkSymbol(name, mkArraySort(IndexSort, InitValue->Sort));

  uint64_t size = 1ULL << IndexSort->getWidth();
  for (uint64_t i = 0; i < size; i++)
    arr = mkArrayStore(arr, mkBVFromDec(i, IndexSort), InitValue);

  return makeExprRef<STPExpr>(SMTExprKind::ArrayConst, &Context, arr->Sort,
                              toSolverExpr<STPExpr>(*arr).Expr, false);
}

checkResult STPSolver::checkImpl() {
  STP::Expr query = STP::vc_falseExpr(Context);
  int res = STP::vc_query(Context, query);
  STP::vc_DeleteExpr(query);
  if (!res)
    return checkResult::SAT;

  if (res == 1)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void STPSolver::resetImpl() {
  if (Context)
    STP::vc_Destroy(Context);
  Context = STP::vc_createValidityChecker();
  STP::vc_registerErrorHandler(STPErrorHandler);
}

void STPSolver::pushImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i)
    STP::vc_push(Context);
}

void STPSolver::popImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i)
    STP::vc_pop(Context);
}

std::string STPSolver::getSolverNameAndVersion() const {
  return std::string("STP v").append(STP::get_git_version_tag());
}

void STPSolver::dumpImpl() {
  std::string Out;
  dumpImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void STPSolver::dumpImpl(std::string &Out) {
  char *buf = nullptr;
  unsigned long len = 0;
  STP::Expr query = STP::vc_trueExpr(Context);
  STP::vc_printQueryStateToBuffer(Context, query, &buf, &len, 0);
  STP::vc_DeleteExpr(query);
  Out.assign(buf, len);
  free(buf);
}

void STPSolver::dumpModelImpl() {
  std::string Out;
  dumpModelImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void STPSolver::dumpModelImpl(std::string &Out) {
  char *buf;
  unsigned long len;
  STP::vc_printCounterExampleToBuffer(Context, &buf, &len);
  Out = buf;
  Out += "\n";
  free(buf);
}

} // namespace camada

#endif
