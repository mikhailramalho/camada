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

#include "cvc4solver.h"
#include "ac_config.h"
#include "camadautils.h"

#include <cmath>

using namespace camada;

#ifdef SOLVER_CVC4_ENABLED

void CVC4Sort::dump() const { std::cerr << Sort.toString() << '\n'; }

bool CVC4Expr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
  return (Expr == dynamic_cast<const CVC4Expr &>(Other).Expr);
}

void CVC4Expr::dump() const { std::cerr << Expr.toString() << '\n'; }

CVC4Solver::CVC4Solver()
    : Context(std::make_shared<CVC4::ExprManager>()), Solver(Context.get()) {
  Solver.setOption("produce-models", true);
  Solver.setOption("produce-assertions", true);
}

void CVC4Solver::addConstraint(const SMTExprRef &Exp) {
  Solver.assertFormula(toSolverExpr<CVC4Expr>(*Exp).Expr);
}

SMTExprRef CVC4Solver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<CVC4Expr>(toSolverExpr<CVC4Expr>(Exp));
}

SMTSortRef CVC4Solver::getBoolSort() {
  return newSortRef<camada::SolverBoolSort<CVC4Sort>>(
      camada::SolverBoolSort<CVC4Sort>(Context, Context->booleanType()));
}

SMTSortRef CVC4Solver::getBVSort(unsigned BitWidth) {
  return newSortRef<camada::SolverBVSort<CVC4Sort>>(
      camada::SolverBVSort<CVC4Sort>(BitWidth, Context,
                                     Context->mkBitVectorType(BitWidth)));
}

SMTSortRef CVC4Solver::getRMSortImpl() {
  return newSortRef<camada::SolverRMSort<CVC4Sort>>(
      camada::SolverRMSort<CVC4Sort>(Context, Context->roundingModeType()));
}

SMTSortRef CVC4Solver::getFPSortImpl(const unsigned ExpWidth,
                                     const unsigned SigWidth) {
  return newSortRef<camada::SolverFPSort<CVC4Sort>>(
      camada::SolverFPSort<CVC4Sort>(
          ExpWidth, SigWidth + 1, Context,
          Context->mkFloatingPointType(ExpWidth, SigWidth)));
}

SMTSortRef CVC4Solver::getBVRMSort() {
  return newSortRef<camada::SolverRMSort<CVC4Sort>>(
      camada::SolverRMSort<CVC4Sort>(Context, Context->mkBitVectorType(3)));
}

SMTSortRef CVC4Solver::getBVFPSort(const unsigned ExpWidth,
                                   const unsigned SigWidth) {
  return newSortRef<camada::SolverFPSort<CVC4Sort>>(
      camada::SolverFPSort<CVC4Sort>(
          ExpWidth, SigWidth + 1, Context,
          Context->mkBitVectorType(ExpWidth + SigWidth + 1)));
}

SMTExprRef CVC4Solver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Exp->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_NEG,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Exp->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_NOT,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(CVC4Expr(
      Context, Exp->Sort,
      Context->mkExpr(CVC4::kind::NOT, toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_PLUS,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_SUB,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_MULT,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_SREM,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_UREM,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_SDIV,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_UDIV,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_SHL,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_ASHR,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_LSHR,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_XOR,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_OR,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_AND,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_ULT,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_SLT,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_UGT,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_SGT,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_ULE,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_SLE,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_UGE,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::BITVECTOR_SGE,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, getBoolSort(),
      Context->mkExpr(CVC4::kind::AND, toSolverExpr<CVC4Expr>(*LHS).Expr,
                      toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, getBoolSort(),
      Context->mkExpr(CVC4::kind::OR, toSolverExpr<CVC4Expr>(*LHS).Expr,
                      toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, getBoolSort(),
      Context->mkExpr(CVC4::kind::XOR, toSolverExpr<CVC4Expr>(*LHS).Expr,
                      toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, getBoolSort(),
      Context->mkExpr(CVC4::kind::EQUAL, toSolverExpr<CVC4Expr>(*LHS).Expr,
                      toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                             const SMTExprRef &F) {
  return newExprRef(CVC4Expr(Context, T->Sort,
                             Context->mkExpr(CVC4::kind::ITE,
                                             toSolverExpr<CVC4Expr>(*Cond).Expr,
                                             toSolverExpr<CVC4Expr>(*T).Expr,
                                             toSolverExpr<CVC4Expr>(*F).Expr)));
}

SMTExprRef CVC4Solver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, getBVSort(i + Exp->getWidth()),
               Context->mkExpr(CVC4::kind::BITVECTOR_SIGN_EXTEND,
                               Context->mkConst(CVC4::BitVectorSignExtend(i)),
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, getBVSort(i + Exp->getWidth()),
               Context->mkExpr(CVC4::kind::BITVECTOR_ZERO_EXTEND,
                               Context->mkConst(CVC4::BitVectorZeroExtend(i)),
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkBVExtract(unsigned High, unsigned Low,
                                   const SMTExprRef &Exp) {
  return newExprRef(CVC4Expr(
      Context, getBVSort(Exp->getWidth()),
      Context->mkExpr(CVC4::Kind::BITVECTOR_EXTRACT,
                      Context->mkConst(CVC4::BitVectorExtract(High, Low)),
                      toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkBVConcat(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, getBVSort(LHS->getWidth() + RHS->getWidth()),
               Context->mkExpr(CVC4::kind::BITVECTOR_CONCAT,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Exp->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_ABS,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkFPNegImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Exp->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_NEG,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISINF,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISNAN,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISSN,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISN,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISZ,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_MULT,
                               toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_DIV,
                               toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPRemImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_REM,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_PLUS,
                               toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, LHS->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_SUB,
                               toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPSqrtImpl(const SMTExprRef &Exp, const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, Exp->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_SQRT,
                               toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                               toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                   const SMTExprRef &Z, const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, X->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_FMA,
                               toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                               toSolverExpr<CVC4Expr>(*X).Expr,
                               toSolverExpr<CVC4Expr>(*Y).Expr,
                               toSolverExpr<CVC4Expr>(*Z).Expr)));
}

SMTExprRef CVC4Solver::mkFPLtImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_LT,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_GT,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPLeImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_LEQ,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_GEQ,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPEqualImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, getBoolSort(),
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_EQ,
                               toSolverExpr<CVC4Expr>(*LHS).Expr,
                               toSolverExpr<CVC4Expr>(*RHS).Expr)));
}

SMTExprRef CVC4Solver::mkFPtoFPImpl(const SMTExprRef &From,
                                    const SMTSortRef &To, const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, To,
               Context->mkExpr(
                   CVC4::kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT,
                   Context->mkConst(CVC4::FloatingPointToFPFloatingPoint(
                       To->getFPExponentWidth(), To->getFPSignificandWidth())),
                   toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                   toSolverExpr<CVC4Expr>(*From).Expr)));
}

SMTExprRef CVC4Solver::mkSBVtoFPImpl(const SMTExprRef &From,
                                     const SMTSortRef &To, const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, To,
               Context->mkExpr(
                   CVC4::kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
                   Context->mkConst(CVC4::FloatingPointToFPSignedBitVector(
                       To->getFPExponentWidth(), To->getFPSignificandWidth())),
                   toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                   toSolverExpr<CVC4Expr>(*From).Expr)));
}

SMTExprRef CVC4Solver::mkUBVtoFPImpl(const SMTExprRef &From,
                                     const SMTSortRef &To, const RM &R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, To,
               Context->mkExpr(
                   CVC4::kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
                   Context->mkConst(CVC4::FloatingPointToFPUnsignedBitVector(
                       To->getFPExponentWidth(), To->getFPSignificandWidth())),
                   toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                   toSolverExpr<CVC4Expr>(*From).Expr)));
}

SMTExprRef CVC4Solver::mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRMImpl(RM::ROUND_TO_ZERO);
  return newExprRef(CVC4Expr(
      Context, getBVSort(ToWidth),
      Context->mkExpr(CVC4::kind::FLOATINGPOINT_TO_SBV,
                      Context->mkConst(CVC4::FloatingPointToSBV(ToWidth)),
                      toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                      toSolverExpr<CVC4Expr>(*From).Expr)));
}

SMTExprRef CVC4Solver::mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRMImpl(RM::ROUND_TO_ZERO);
  return newExprRef(CVC4Expr(
      Context, getBVSort(ToWidth),
      Context->mkExpr(CVC4::kind::FLOATINGPOINT_TO_UBV,
                      Context->mkConst(CVC4::FloatingPointToUBV(ToWidth)),
                      toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                      toSolverExpr<CVC4Expr>(*From).Expr)));
}

SMTExprRef CVC4Solver::mkFPtoIntegralImpl(const SMTExprRef &From, RM R) {
  SMTExprRef roundingMode = mkRMImpl(R);
  return newExprRef(
      CVC4Expr(Context, From->Sort,
               Context->mkExpr(CVC4::kind::FLOATINGPOINT_RTI,
                               toSolverExpr<CVC4Expr>(*roundingMode).Expr,
                               toSolverExpr<CVC4Expr>(*From).Expr)));
}

bool CVC4Solver::getBool(const SMTExprRef &Exp) {
  return Solver.getValue(toSolverExpr<CVC4Expr>(*Exp).Expr).getConst<bool>();
}

uint64_t CVC4Solver::getBV(const SMTExprRef &Exp) {
  return Solver.getValue(toSolverExpr<CVC4Expr>(*Exp).Expr)
      .getConst<CVC4::BitVector>()
      .toInteger()
      .getUnsignedLong();
}

template <class FPType>
static inline bool isNaNOrInf(const CVC4::FloatingPoint &FP, FPType &Res) {
  // TODO: what about negative NaN?
  if (FP.isNaN()) {
    Res = NAN;
    return true;
  }

  // Convert the float to bv
  if (FP.isInfinite()) {
    Res = FP.isPositive() ? INFINITY : -INFINITY;
    return true;
  }

  return false;
}

float CVC4Solver::getFP32Impl(const SMTExprRef &Exp) {
  CVC4::FloatingPoint fp = Solver.getValue(toSolverExpr<CVC4Expr>(*Exp).Expr)
                               .getConst<CVC4::FloatingPoint>();

  float result;
  if (isNaNOrInf(fp, result))
    return result;

  // Convert the integer to float. We assume that floats are 32 bits long
  auto FP_as_int = fp.pack().toInteger().getSignedInt();
  camada::abortCondWithMessage(sizeof(float) == sizeof(FP_as_int),
                               "Cannot convert int to floating-point");

  memcpy(&result, &FP_as_int, sizeof(float));
  return result;
}

double CVC4Solver::getFP64Impl(const SMTExprRef &Exp) {
  CVC4::FloatingPoint fp = Solver.getValue(toSolverExpr<CVC4Expr>(*Exp).Expr)
                               .getConst<CVC4::FloatingPoint>();

  double result;
  if (isNaNOrInf(fp, result))
    return result;

  // Convert the integer to float. We assume that floats are 32 bits long
  auto FP_as_int = fp.pack().toInteger().getLong();
  camada::abortCondWithMessage(sizeof(double) == sizeof(FP_as_int),
                               "Cannot convert int to floating-point");

  memcpy(&result, &FP_as_int, sizeof(double));
  return result;
}

SMTExprRef CVC4Solver::mkBool(const bool b) {
  return newExprRef(CVC4Expr(Context, getBoolSort(), Context->mkConst(b)));
}

SMTExprRef CVC4Solver::mkBVFromDec(const uint64_t Int, const SMTSortRef &Sort) {
  return newExprRef(
      CVC4Expr(Context, Sort,
               Context->mkConst(CVC4::BitVector(Sort->getWidth(),
                                                static_cast<uint64_t>(Int)))));
}

SMTExprRef CVC4Solver::mkSymbol(const std::string &Name, SMTSortRef Sort) {

  // Standard arrangement: if we already have the name, return the expression
  // from the symbol table. If not, time for a new name.
  if (SymbolTable.isBound(Name))
    return newExprRef(CVC4Expr(Context, Sort, SymbolTable.lookup(Name)));

  // Time for a new one.
  SMTExprRef sym = newExprRef(CVC4Expr(
      Context, Sort, Context->mkVar(Name, toSolverSort<CVC4Sort>(*Sort).Sort)));
  SymbolTable.bind(Name, toSolverExpr<CVC4Expr>(*sym).Expr, true);
  return sym;
}

template <typename FPType, typename IntType>
static inline IntType FPasInt(const FPType FP) {
  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  camada::abortCondWithMessage(sizeof(FPType) == sizeof(IntType),
                               "Cannot convert int to floating-point");

  IntType FPAsInt;
  memcpy(&FPAsInt, &FP, sizeof(FPType));
  return FPAsInt;
}

SMTExprRef CVC4Solver::mkFP32Impl(const float Float) {
  return newExprRef(CVC4Expr(
      Context, getFP32Sort(),
      Context->mkConst(CVC4::FloatingPoint(
          8, 24, CVC4::BitVector(63, FPasInt<float, uint32_t>(Float))))));
}

SMTExprRef CVC4Solver::mkFP64Impl(const double Double) {
  return newExprRef(CVC4Expr(
      Context, getFP64Sort(),
      Context->mkConst(CVC4::FloatingPoint(
          11, 53, CVC4::BitVector(65, FPasInt<double, uint64_t>(Double))))));
}

SMTExprRef CVC4Solver::mkRMImpl(const RM &R) {
  CVC4::Expr e;
  switch (R) {
  default:
    camada::abortWithMessage("Unsupported floating-point semantics.");
  case RM::ROUND_TO_EVEN:
    e = Context->mkConst(CVC4::RoundingMode::roundNearestTiesToEven);
    break;
  case RM::ROUND_TO_AWAY:
    e = Context->mkConst(CVC4::RoundingMode::roundNearestTiesToAway);
    break;
  case RM::ROUND_TO_PLUS_INF:
    e = Context->mkConst(CVC4::RoundingMode::roundTowardPositive);
    break;
  case RM::ROUND_TO_MINUS_INF:
    e = Context->mkConst(CVC4::RoundingMode::roundTowardNegative);
    break;
  case RM::ROUND_TO_ZERO:
    e = Context->mkConst(CVC4::RoundingMode::roundTowardZero);
    break;
  }
  return newExprRef(CVC4Expr(Context, getRMSortImpl(), e));
}

SMTExprRef CVC4Solver::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                 const unsigned SigWidth) {
  SMTSortRef sort = getFPSortImpl(ExpWidth, SigWidth);
  SMTExprRef theNaN =
      newExprRef(CVC4Expr(Context, sort,
                          Context->mkConst(CVC4::FloatingPoint::makeNaN(
                              CVC4::FloatingPointSize(ExpWidth, SigWidth)))));

  return Sgn ? mkFPNegImpl(theNaN) : theNaN;
}

SMTExprRef CVC4Solver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                 const unsigned SigWidth) {
  SMTSortRef sort = getFPSortImpl(ExpWidth, SigWidth);
  return newExprRef(
      CVC4Expr(Context, sort,
               Context->mkConst(CVC4::FloatingPoint::makeInf(
                   CVC4::FloatingPointSize(ExpWidth, SigWidth), Sgn))));
}

SMTExprRef CVC4Solver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                        const SMTSortRef &To) {
  return newExprRef(
      CVC4Expr(Context, To,
               Context->mkExpr(
                   CVC4::kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
                   Context->mkConst(CVC4::FloatingPointToFPIEEEBitVector(
                       To->getFPExponentWidth(), To->getFPSignificandWidth())),
                   toSolverExpr<CVC4Expr>(*Exp).Expr)));
}

SMTExprRef CVC4Solver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {

  // CVC4 does not provide a direct way to convert from fp
  // to bv, so we create a new symbol
  const std::string name = "__CAMADA_ieeebv" + std::to_string(ToBVCounter++);

  SMTExprRef newSymbol = mkSymbol(name.c_str(), getBVSort(Exp->getWidth()));

  // and constraint it to be the conversion of the fp, since
  // (fp_matches_bv f bv) <-> (= f ((_ to_fp E S) bv))
  addConstraint(mkEqual(Exp, mkBVToIEEEFPImpl(newSymbol, Exp->Sort)));

  // NewSymbol is the resulting bitvector
  return newSymbol;
}

checkResult CVC4Solver::check() {
  CVC4::Result res = Solver.checkSat();
  if (res.isSat())
    return checkResult::SAT;

  if (res.isUnknown())
    return checkResult::UNKNOWN;

  return checkResult::UNSAT;
}

void CVC4Solver::reset() { Solver.reset(); }

void CVC4Solver::dump() {
  auto const &assertions = Solver.getAssertions();
  for (auto const &a : assertions)
    a.printAst(std::cerr, 0);
}

void CVC4Solver::dumpModel() { Solver.printSynthSolution(std::cerr); }

#endif
