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

#include "stpsolver.h"
#include "ac_config.h"

#include <algorithm>
#include <cassert>
#include <iostream>

using namespace camada;

#ifdef SOLVER_STP_ENABLED

void STPSort::dump() const {
  char *s = STP::typeString(Sort);
  std::cerr << s << '\n';
  free(s);
}

bool STPExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
  return (STP::getExprID(Expr) ==
          STP::getExprID(dynamic_cast<const STPExpr &>(Other).Expr));
}

void STPExpr::dump() const {
  char *s = STP::exprString(Expr);
  std::cerr << s << '\n';
  free(s);
}

// Function used to report errors
void STPErrorHandler(const char *msg) { assert(0 && msg); }

STPSolver::STPSolver()
    : Context(std::make_shared<STP::VC>(STP::vc_createValidityChecker())) {
  STP::vc_registerErrorHandler(STPErrorHandler);
}

STPSolver::STPSolver(STPContextRef C) : Context(std::move(C)) {}

STPSolver::~STPSolver() { STP::vc_Destroy(*Context); }

void STPSolver::addConstraint(const SMTExprRef &Exp) {
  STP::vc_assertFormula(*Context, toSolverExpr<STPExpr>(*Exp).Expr);
}

SMTExprRef STPSolver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<STPExpr>(toSolverExpr<STPExpr>(Exp));
}

SMTSortRef STPSolver::mkBoolSort() {
  return newSortRef<SolverBoolSort<STPSort>>(
      {Context, STP::vc_boolType(*Context)});
}

SMTSortRef STPSolver::mkBVSort(unsigned BitWidth) {
  return newSortRef<SolverBVSort<STPSort>>(
      {BitWidth, Context, STP::vc_bvType(*Context, BitWidth)});
}

SMTSortRef STPSolver::getBVFPSort(const unsigned ExpWidth,
                                  const unsigned SigWidth) {
  return newSortRef<SolverFPSort<STPSort>>(
      {ExpWidth, SigWidth + 1, Context,
       STP::vc_bvType(*Context, ExpWidth + SigWidth + 1)});
}

SMTSortRef STPSolver::getBVRMSort() {
  return newSortRef<SolverRMSort<STPSort>>(
      {Context, STP::vc_bvType(*Context, 3)});
}

SMTSortRef STPSolver::mkArraySort(const SMTSortRef &IndexSort,
                                  const SMTSortRef &ElemSort) {
  return newSortRef<SolverArraySort<STPSort>>(
      {IndexSort, ElemSort, Context,
       STP::vc_arrayType(*Context, toSolverSort<STPSort>(*IndexSort).Sort,
                         toSolverSort<STPSort>(*ElemSort).Sort)});
}

SMTExprRef STPSolver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(STPExpr(
      Context, Exp->Sort,
      STP::vc_bvUMinusExpr(*Context, toSolverExpr<STPExpr>(*Exp).Expr)));
}

SMTExprRef STPSolver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(
      STPExpr(Context, Exp->Sort,
              STP::vc_bvNotExpr(*Context, toSolverExpr<STPExpr>(*Exp).Expr)));
}

SMTExprRef STPSolver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(
      STPExpr(Context, Exp->Sort,
              STP::vc_notExpr(*Context, toSolverExpr<STPExpr>(*Exp).Expr)));
}

SMTExprRef STPSolver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvPlusExpr(*Context, LHS->getWidth(),
                                 toSolverExpr<STPExpr>(*LHS).Expr,
                                 toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvMinusExpr(*Context, LHS->getWidth(),
                                  toSolverExpr<STPExpr>(*LHS).Expr,
                                  toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvMultExpr(*Context, LHS->getWidth(),
                                 toSolverExpr<STPExpr>(*LHS).Expr,
                                 toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_sbvModExpr(*Context, LHS->getWidth(),
                                 toSolverExpr<STPExpr>(*LHS).Expr,
                                 toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvModExpr(*Context, LHS->getWidth(),
                                toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_sbvDivExpr(*Context, LHS->getWidth(),
                                 toSolverExpr<STPExpr>(*LHS).Expr,
                                 toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvDivExpr(*Context, LHS->getWidth(),
                                toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvLeftShiftExprExpr(*Context, LHS->getWidth(),
                                          toSolverExpr<STPExpr>(*LHS).Expr,
                                          toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(STPExpr(
      Context, LHS->Sort,
      STP::vc_bvSignedRightShiftExprExpr(*Context, LHS->getWidth(),
                                         toSolverExpr<STPExpr>(*LHS).Expr,
                                         toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvLeftShiftExprExpr(*Context, LHS->getWidth(),
                                          toSolverExpr<STPExpr>(*LHS).Expr,
                                          toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvXorExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvOrExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                               toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvAndExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvLtExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                               toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_sbvLtExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvGtExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                               toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_sbvGtExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvLeExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                               toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_sbvLeExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_bvGeExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                               toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, LHS->Sort,
              STP::vc_sbvGeExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, mkBoolSort(),
              STP::vc_andExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                              toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, mkBoolSort(),
              STP::vc_orExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                             toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, mkBoolSort(),
              STP::vc_xorExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                              toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  if (LHS->isArraySort()) {
    // STP does not support array extensionality, so let's create a free
    // variable
    const std::string name =
        "__CAMADA_index" + std::to_string(ConstArrayCounter++);
    SMTExprRef index = mkSymbol(name, LHS->Sort->getIndexSort());

    // and do select(A,i) == select(B,i)
    return mkEqual(mkArraySelect(LHS, index), mkArraySelect(RHS, index));
  }

  if (LHS->isBoolSort())
    return newExprRef(
        STPExpr(Context, mkBoolSort(),
                STP::vc_iffExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                                toSolverExpr<STPExpr>(*RHS).Expr)));

  return newExprRef(
      STPExpr(Context, mkBoolSort(),
              STP::vc_eqExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                             toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                            const SMTExprRef &F) {
  return newExprRef(
      STPExpr(Context, T->Sort,
              STP::vc_iteExpr(*Context, toSolverExpr<STPExpr>(*Cond).Expr,
                              toSolverExpr<STPExpr>(*T).Expr,
                              toSolverExpr<STPExpr>(*F).Expr)));
}

SMTExprRef STPSolver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(STPExpr(
      Context, mkBVSort(i + Exp->getWidth()),
      STP::vc_bvSignExtend(*Context, toSolverExpr<STPExpr>(*Exp).Expr, i)));
}

SMTExprRef STPSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  SMTExprRef z = SMTFPSolver::mkBVFromDec(0, i);
  return mkBVConcat(z, Exp);
}

SMTExprRef STPSolver::mkBVExtract(unsigned High, unsigned Low,
                                  const SMTExprRef &Exp) {
  return newExprRef(
      STPExpr(Context, mkBVSort(High - Low + 1),
              STP::vc_bvExtract(*Context, toSolverExpr<STPExpr>(*Exp).Expr,
                                High, Low)));
}

SMTExprRef STPSolver::mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      STPExpr(Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
              STP::vc_bvConcatExpr(*Context, toSolverExpr<STPExpr>(*LHS).Expr,
                                   toSolverExpr<STPExpr>(*RHS).Expr)));
}

SMTExprRef STPSolver::mkArraySelect(const SMTExprRef &Array,
                                    const SMTExprRef &Index) {
  return newExprRef(
      STPExpr(Context, Array->Sort->getElementSort(),
              STP::vc_readExpr(*Context, toSolverExpr<STPExpr>(*Array).Expr,
                               toSolverExpr<STPExpr>(*Index).Expr)));
}

SMTExprRef STPSolver::mkArrayStore(const SMTExprRef &Array,
                                   const SMTExprRef &Index,
                                   const SMTExprRef &Element) {
  return newExprRef(
      STPExpr(Context, Array->Sort,
              STP::vc_writeExpr(*Context, toSolverExpr<STPExpr>(*Array).Expr,
                                toSolverExpr<STPExpr>(*Index).Expr,
                                toSolverExpr<STPExpr>(*Element).Expr)));
}

bool STPSolver::getBool(const SMTExprRef &Exp) {
  STP::Expr value =
      STP::vc_getCounterExample(*Context, toSolverExpr<STPExpr>(*Exp).Expr);
  return STP::getBVUnsigned(STP::vc_boolToBVExpr(*Context, value)) != 0;
}

std::string STPSolver::getBVInBin(const SMTExprRef &Exp) {
  STP::Expr value =
      STP::vc_getCounterExample(*Context, toSolverExpr<STPExpr>(*Exp).Expr);
  char *buf;
  unsigned long len;
  STP::vc_printBVBitStringToBuffer(value, &buf, &len);
  std::string bv(buf);
  free(buf);
  return bv;
}

SMTExprRef STPSolver::getArrayElement(const SMTExprRef &Array,
                                      const SMTExprRef &Index) {
  SMTExprRef sel = mkArraySelect(Array, Index);

  SMTSortRef elementSort = Array->Sort->getElementSort();
  if (elementSort->isBoolSort())
    return mkBool(getBool(sel));

  if (elementSort->isBVSort())
    return SMTFPSolver::mkBVFromBin(getBVInBin(sel));

  assert(elementSort->isFPSort() && "Unknown array element type");
  return SMTFPSolver::mkFPFromBin(getFPInBin(sel),
                                  elementSort->getFPExponentWidth());
}

SMTExprRef STPSolver::mkBool(const bool b) {
  return newExprRef(
      STPExpr(Context, mkBoolSort(),
              b ? STP::vc_trueExpr(*Context) : STP::vc_falseExpr(*Context)));
}

SMTExprRef STPSolver::mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) {
  // Prevent creating a bitvector with size greater than the bitwidth
  int64_t newInt = Int & ((1 << Sort->getWidth()) - 1);

  return newExprRef(
      STPExpr(Context, Sort,
              STP::vc_bvConstExprFromDecStr(*Context, Sort->getWidth(),
                                            std::to_string(newInt).c_str())));
}

SMTExprRef STPSolver::mkBVFromBin(const std::string &Int,
                                  const SMTSortRef &Sort) {
  return newExprRef(STPExpr(Context, Sort,
                            STP::vc_bvConstExprFromStr(*Context, Int.c_str())));
}

SMTExprRef STPSolver::mkSymbol(const std::string &Name, SMTSortRef Sort) {

  std::string new_name = Name;
  std::replace(new_name.begin(), new_name.end(), '@', '_');
  std::replace(new_name.begin(), new_name.end(), '!', '_');
  std::replace(new_name.begin(), new_name.end(), '&', '_');
  std::replace(new_name.begin(), new_name.end(), '#', '_');
  std::replace(new_name.begin(), new_name.end(), '$', '_');
  std::replace(new_name.begin(), new_name.end(), ':', '_');

  return newExprRef(
      STPExpr(Context, Sort,
              STP::vc_varExpr(*Context, new_name.c_str(),
                              toSolverSort<STPSort>(*Sort).Sort)));
}

SMTExprRef STPSolver::mkArrayConst(const SMTSortRef &IndexSort,
                                   const SMTExprRef &InitValue) {
  const std::string name = "__CAMADA_arr" + std::to_string(ConstArrayCounter++);
  SMTExprRef arr = mkSymbol(name, mkArraySort(IndexSort, InitValue->Sort));

  uint64_t size = 1ULL << IndexSort->getWidth();
  for (uint64_t i = 0; i < size; i++)
    arr = mkArrayStore(arr, mkBVFromDec(i, IndexSort), InitValue);

  return arr;
}

checkResult STPSolver::check() {
  int res = STP::vc_query(*Context, STP::vc_falseExpr(*Context));
  if (!res)
    return checkResult::SAT;

  if (res == 1)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void STPSolver::reset() {
  STP::vc_Destroy(*Context);
  Context = std::make_shared<STP::VC>(STP::vc_createValidityChecker());
  STP::vc_registerErrorHandler(STPErrorHandler);
}

void STPSolver::dump() { STP::vc_printQuery(*Context); }

void STPSolver::dumpModel() {
  char *buf;
  unsigned long len;
  STP::vc_printCounterExampleToBuffer(*Context, &buf, &len);
  std::cerr << buf << '\n';
  free(buf);
}

#endif
