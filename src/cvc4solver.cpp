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

#include <fmt/printf.h>

using namespace camada;

#ifdef SOLVER_CVC4_ENABLED

CVC4Sort::CVC4Sort(CVC4ContextRef C, const CVC4::Type &CS)
    : Context(std::move(C)), Sort(CS) {}

bool CVC4Sort::isBitvectorSortImpl() const { return Sort.isBitVector(); }

bool CVC4Sort::isBooleanSortImpl() const { return Sort.isBoolean(); }

bool CVC4Sort::isFloatSortImpl() const { return Sort.isFloatingPoint(); }

bool CVC4Sort::isRoundingModeSortImpl() const { return Sort.isRoundingMode(); }

unsigned CVC4Sort::getBitvectorSortSizeImpl() const {
  CVC4::BitVectorType bvType = static_cast<CVC4::BitVectorType>(Sort);
  return bvType.getSize();
}

unsigned CVC4Sort::getFloatSortSizeImpl() const {
  CVC4::FloatingPointType fpType = static_cast<CVC4::FloatingPointType>(Sort);
  return fpType.getExponentSize() + fpType.getSignificandSize();
}

bool CVC4Sort::equal_to(SMTSort const &Other) const {
  return Sort == dynamic_cast<const CVC4Sort &>(Other).Sort;
}

void CVC4Sort::dump() const { fmt::print(stderr, "{}\n", Sort.toString()); }

CVC4Expr::CVC4Expr(CVC4ContextRef C, const CVC4::Expr &CA)
    : Context(std::move(C)), AST(CA) {}

bool CVC4Expr::equal_to(SMTExpr const &Other) const {
  camada::abortCondWithMessage(
      Context->getType(AST) ==
          Context->getType(dynamic_cast<const CVC4Expr &>(Other).AST),
      "AST's must have the same sort");
  return (AST == dynamic_cast<const CVC4Expr &>(Other).AST);
}

void CVC4Expr::dump() const { fmt::print(stderr, "{}\n", AST.toString()); }

CVC4Solver::CVC4Solver()
    : Context(std::make_shared<CVC4::ExprManager>()), Solver(Context.get()) {
  Solver.setOption("produce-models", true);
  Solver.setOption("produce-assertions", true);
}

void CVC4Solver::addConstraint(const SMTExprRef &Exp) {
  Solver.assertFormula(toCVC4Expr(*Exp).AST);
}

SMTSortRef CVC4Solver::newSortRef(const SMTSort &Sort) const {
  return std::make_shared<CVC4Sort>(toCVC4Sort(Sort));
}

SMTExprRef CVC4Solver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<CVC4Expr>(toCVC4Expr(Exp));
}

SMTSortRef CVC4Solver::getBoolSort() {
  return newSortRef(CVC4Sort(Context, Context->booleanType()));
}

SMTSortRef CVC4Solver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef(CVC4Sort(Context, Context->mkBitVectorType(BitWidth)));
}

SMTSortRef CVC4Solver::getRoundingModeSort() {
  return newSortRef(CVC4Sort(Context, Context->roundingModeType()));
}

SMTSortRef CVC4Solver::getFloatSort(const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  return newSortRef(
      CVC4Sort(Context, Context->mkFloatingPointType(ExpWidth, SigWidth)));
}

SMTSortRef CVC4Solver::getSort(const SMTExprRef &Exp) {
  return newSortRef(CVC4Sort(Context, Context->getType(toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_NEG,
                                                      toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_NOT,
                                                      toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::NOT, toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_PLUS, toCVC4Expr(*LHS).AST,
                               toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_SUB,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_MULT, toCVC4Expr(*LHS).AST,
                               toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_SREM, toCVC4Expr(*LHS).AST,
                               toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_UREM, toCVC4Expr(*LHS).AST,
                               toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_SDIV, toCVC4Expr(*LHS).AST,
                               toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_UDIV, toCVC4Expr(*LHS).AST,
                               toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_SHL,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_ASHR, toCVC4Expr(*LHS).AST,
                               toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_LSHR, toCVC4Expr(*LHS).AST,
                               toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_XOR,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_OR,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_AND,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_ULT,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_SLT,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_UGT,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_SGT,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_ULE,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_SLE,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_UGE,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(Context, Context->mkExpr(CVC4::kind::BITVECTOR_SGE,
                                                      toCVC4Expr(*LHS).AST,
                                                      toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::AND, toCVC4Expr(*LHS).AST,
                                        toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::OR, toCVC4Expr(*LHS).AST,
                                        toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::EQUAL, toCVC4Expr(*LHS).AST,
                                        toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                             const SMTExprRef &F) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::ITE, toCVC4Expr(*Cond).AST,
                               toCVC4Expr(*T).AST, toCVC4Expr(*F).AST)));
}

SMTExprRef CVC4Solver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  CVC4::BitVectorSignExtend ext(i);
  SMTExprRef ext2r = newExprRef(CVC4Expr(Context, Context->mkConst(ext)));
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_SIGN_EXTEND,
                               toCVC4Expr(*ext2r).AST, toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  CVC4::BitVectorZeroExtend ext(i);
  SMTExprRef ext2r = newExprRef(CVC4Expr(Context, Context->mkConst(ext)));
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_ZERO_EXTEND,
                               toCVC4Expr(*ext2r).AST, toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkBVExtract(unsigned High, unsigned Low,
                                   const SMTExprRef &Exp) {
  CVC4::BitVectorExtract ext(High, Low);
  SMTExprRef ext2r = newExprRef(CVC4Expr(Context, Context->mkConst(ext)));
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::Kind::BITVECTOR_EXTRACT,
                               toCVC4Expr(*ext2r).AST, toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkBVConcat(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::BITVECTOR_CONCAT,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPNeg(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_NEG,
                                        toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkFPIsInfinite(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISINF,
                                        toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkFPIsNaN(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISNAN,
                                        toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkFPIsNormal(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISN,
                                        toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkFPIsZero(const SMTExprRef &Exp) {
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_ISZ,
                                        toCVC4Expr(*Exp).AST)));
}

SMTExprRef CVC4Solver::mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_MULT,
                               toCVC4Expr(*roundingMode).AST,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_DIV,
                               toCVC4Expr(*roundingMode).AST,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_REM,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_PLUS,
                               toCVC4Expr(*roundingMode).AST,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_SUB,
                               toCVC4Expr(*roundingMode).AST,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPSqrt(const SMTExprRef &Exp, const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_SQRT,
                                        toCVC4Expr(*roundingMode).AST,
                                        toCVC4Expr(*Exp).AST)));
};

SMTExprRef CVC4Solver::mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                               const SMTExprRef &Z, const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_FMA,
                                        toCVC4Expr(*roundingMode).AST,
                                        toCVC4Expr(*X).AST, toCVC4Expr(*Y).AST,
                                        toCVC4Expr(*Z).AST)));
};

SMTExprRef CVC4Solver::mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_LT,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_GT,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_LEQ,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_GEQ,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC4Expr(
      Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_EQ,
                               toCVC4Expr(*LHS).AST, toCVC4Expr(*RHS).AST)));
}

SMTExprRef CVC4Solver::mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                                const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);

  CVC4::FloatingPointType fto =
      static_cast<CVC4::FloatingPointType>(toCVC4Sort(*To).Sort);
  unsigned expWidth = fto.getExponentSize();
  unsigned mantWidth = fto.getSignificandSize();

  return newExprRef(CVC4Expr(
      Context,
      Context->mkExpr(CVC4::kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT,
                      Context->mkConst(CVC4::FloatingPointToFPFloatingPoint(
                          expWidth, mantWidth)),
                      toCVC4Expr(*roundingMode).AST, toCVC4Expr(*From).AST)));
}

SMTExprRef CVC4Solver::mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                                 const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);

  CVC4::FloatingPointType fto =
      static_cast<CVC4::FloatingPointType>(toCVC4Sort(*To).Sort);
  unsigned expWidth = fto.getExponentSize();
  unsigned mantWidth = fto.getSignificandSize();

  return newExprRef(CVC4Expr(
      Context,
      Context->mkExpr(CVC4::kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
                      Context->mkConst(CVC4::FloatingPointToFPSignedBitVector(
                          expWidth, mantWidth)),
                      toCVC4Expr(*roundingMode).AST, toCVC4Expr(*From).AST)));
}

SMTExprRef CVC4Solver::mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                                 const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);

  CVC4::FloatingPointType fto =
      static_cast<CVC4::FloatingPointType>(toCVC4Sort(*To).Sort);
  unsigned expWidth = fto.getExponentSize();
  unsigned mantWidth = fto.getSignificandSize();

  return newExprRef(CVC4Expr(
      Context,
      Context->mkExpr(CVC4::kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
                      Context->mkConst(CVC4::FloatingPointToFPUnsignedBitVector(
                          expWidth, mantWidth)),
                      toCVC4Expr(*roundingMode).AST, toCVC4Expr(*From).AST)));
}

SMTExprRef CVC4Solver::mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(CVC4Expr(
      Context,
      Context->mkExpr(CVC4::kind::FLOATINGPOINT_TO_SBV,
                      Context->mkConst(CVC4::FloatingPointToSBV(ToWidth)),
                      toCVC4Expr(*roundingMode).AST, toCVC4Expr(*From).AST)));
}

SMTExprRef CVC4Solver::mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(CVC4Expr(
      Context,
      Context->mkExpr(CVC4::kind::FLOATINGPOINT_TO_UBV,
                      Context->mkConst(CVC4::FloatingPointToUBV(ToWidth)),
                      toCVC4Expr(*roundingMode).AST, toCVC4Expr(*From).AST)));
}

SMTExprRef CVC4Solver::mkFPtoIntegral(const SMTExprRef &From, RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(
      CVC4Expr(Context, Context->mkExpr(CVC4::kind::FLOATINGPOINT_RTI,
                                        toCVC4Expr(*roundingMode).AST,
                                        toCVC4Expr(*From).AST)));
};

bool CVC4Solver::getBoolean(const SMTExprRef &Exp) {
  return Solver.getValue(toCVC4Expr(*Exp).AST).getConst<bool>();
}

int64_t CVC4Solver::getBitvector(const SMTExprRef &Exp) {
  return Solver.getValue(toCVC4Expr(*Exp).AST)
      .getConst<CVC4::BitVector>()
      .toInteger()
      .getUnsignedLong();
}

float CVC4Solver::getFloat(const SMTExprRef &Exp) {
  CVC4::FloatingPoint fp =
      Solver.getValue(toCVC4Expr(*Exp).AST).getConst<CVC4::FloatingPoint>();

  // TODO: what about negative NaN?
  if (fp.isNaN())
    return NAN;

  // Convert the float to bv
  if (fp.isInfinite())
    return fp.isPositive() ? INFINITY : -INFINITY;

  auto FP_as_int = fp.pack().toInteger().getSignedInt();

  // Convert the integer to float. We assume that floats are 32 bits long
  camada::abortCondWithMessage(sizeof(float) == sizeof(FP_as_int),
                               "Cannot convert int to floating-point");

  float result;
  memcpy(&result, &FP_as_int, sizeof(float));
  return result;
}

double CVC4Solver::getDouble(const SMTExprRef &Exp) {
  CVC4::FloatingPoint fp =
      Solver.getValue(toCVC4Expr(*Exp).AST).getConst<CVC4::FloatingPoint>();

  // TODO: what about negative NaN?
  if (fp.isNaN())
    return NAN;

  // Convert the float to bv
  if (fp.isInfinite())
    return fp.isPositive() ? INFINITY : -INFINITY;

  auto FP_as_int = fp.pack().toInteger().getLong();

  // Convert the integer to float. We assume that floats are 32 bits long
  camada::abortCondWithMessage(sizeof(double) == sizeof(FP_as_int),
                               "Cannot convert int to floating-point");

  double result;
  memcpy(&result, &FP_as_int, sizeof(double));
  return result;
}

bool CVC4Solver::getInterpretation(const SMTExprRef &Exp, int64_t &Inter) {
  // TODO: CVC4 never fails?
  Inter = getBitvector(Exp);
  return true;
}

bool CVC4Solver::getInterpretation(const SMTExprRef &Exp, float &Float) {
  // TODO: CVC4 never fails?
  Float = getFloat(Exp);
  return true;
}

bool CVC4Solver::getInterpretation(const SMTExprRef &Exp, double &Double) {
  // TODO: CVC4 never fails?
  Double = getDouble(Exp);
  return true;
}

SMTExprRef CVC4Solver::mkBoolean(const bool b) {
  return newExprRef(CVC4Expr(Context, Context->mkConst(b)));
}

SMTExprRef CVC4Solver::mkBitvector(const int64_t Int, unsigned BitWidth) {
  return newExprRef(CVC4Expr(
      Context,
      Context->mkConst(CVC4::BitVector(BitWidth, static_cast<uint64_t>(Int)))));
}

SMTExprRef CVC4Solver::mkSymbol(const char *Name, SMTSortRef Sort) {

  // Standard arrangement: if we already have the name, return the expression
  // from the symbol table. If not, time for a new name.
  if (SymbolTable.isBound(Name))
    return newExprRef(CVC4Expr(Context, SymbolTable.lookup(Name)));

  // Time for a new one.
  SMTExprRef sym = newExprRef(
      CVC4Expr(Context, Context->mkVar(Name, toCVC4Sort(*Sort).Sort)));
  SymbolTable.bind(Name, toCVC4Expr(*sym).AST, true);
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

SMTExprRef CVC4Solver::mkFloat(const float Float) {
  return newExprRef(CVC4Expr(
      Context,
      Context->mkConst(CVC4::FloatingPoint(
          8, 24, CVC4::BitVector(63, FPasInt<float, uint32_t>(Float))))));
}

SMTExprRef CVC4Solver::mkDouble(const double Double) {
  return newExprRef(CVC4Expr(
      Context,
      Context->mkConst(CVC4::FloatingPoint(
          11, 53, CVC4::BitVector(65, FPasInt<double, uint64_t>(Double))))));
}

SMTExprRef CVC4Solver::mkRoundingMode(const RoundingMode R) {
  switch (R) {
  case RoundingMode::ROUND_TO_EVEN:
    return newExprRef(CVC4Expr(
        Context, Context->mkConst(CVC4::RoundingMode::roundNearestTiesToEven)));
  case RoundingMode::ROUND_TO_AWAY:
    return newExprRef(CVC4Expr(
        Context, Context->mkConst(CVC4::RoundingMode::roundNearestTiesToAway)));
  case RoundingMode::ROUND_TO_PLUS_INF:
    return newExprRef(CVC4Expr(
        Context, Context->mkConst(CVC4::RoundingMode::roundTowardPositive)));
  case RoundingMode::ROUND_TO_MINUS_INF:
    return newExprRef(CVC4Expr(
        Context, Context->mkConst(CVC4::RoundingMode::roundTowardNegative)));
  case RoundingMode::ROUND_TO_ZERO:
    return newExprRef(CVC4Expr(
        Context, Context->mkConst(CVC4::RoundingMode::roundTowardZero)));
  default:;
  }
  camada::abortWithMessage("Unsupported floating-point semantics.");
}

SMTExprRef CVC4Solver::mkNaN(const bool Sgn, const unsigned ExpWidth,
                             const unsigned SigWidth) {
  SMTExprRef theNaN = newExprRef(
      CVC4Expr(Context, Context->mkConst(CVC4::FloatingPoint::makeNaN(
                            CVC4::FloatingPointSize(ExpWidth, SigWidth)))));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef CVC4Solver::mkInf(const bool Sgn, const unsigned ExpWidth,
                             const unsigned SigWidth) {
  return newExprRef(CVC4Expr(
      Context, Context->mkConst(CVC4::FloatingPoint::makeInf(
                   CVC4::FloatingPointSize(ExpWidth, SigWidth), Sgn))));
}

checkResult CVC4Solver::check() {
  CVC4::Result res = Solver.checkSat();
  if (res.isSat())
    return checkResult::SAT;

  if (res.isUnknown())
    return checkResult::UNKNOWN;

  return checkResult::UNSAT;
}

void CVC4Solver::push() { Solver.push(); }

void CVC4Solver::pop(unsigned NumStates) {
  while (NumStates--)
    Solver.pop();
}

void CVC4Solver::reset() { Solver.reset(); }

void CVC4Solver::dump() {
  auto const &assertions = Solver.getAssertions();
  for (auto const &a : assertions)
    a.printAst(std::cerr, 0);
}

void CVC4Solver::dumpModel() { Solver.printSynthSolution(std::cerr); }

#endif
