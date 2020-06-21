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

#include "mathsatsolver.h"
#include "ac_config.h"

#include <fmt/printf.h>
#include <gmp.h>

using namespace camada;

#ifdef SOLVER_MATHSAT_ENABLED

void MathSATSort::dump() const {
  char *s = msat_type_repr(Sort);
  fmt::print(stderr, "{}\n", s);
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
  fmt::print(stderr, "{}\n", ast);
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

void MathSATSolver::addConstraint(const SMTExprRef &Exp) {
  msat_assert_formula(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr);
}

SMTExprRef MathSATSolver::newExprRef(const SMTExpr &Exp) const {
  abortCondWithMessage(!MSAT_ERROR_TERM(toSolverExpr<MathSATExpr>(Exp).Expr),
                       "Error when creating MathSAT expr.");
  return std::make_shared<MathSATExpr>(toSolverExpr<MathSATExpr>(Exp));
}

SMTSortRef MathSATSolver::getBoolSort() {
  return newSortRef<camada::SolverBoolSort<MathSATSort>>(
      camada::SolverBoolSort<MathSATSort>(Context,
                                          msat_get_bool_type(*Context)));
}

SMTSortRef MathSATSolver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef<camada::SolverBVSort<MathSATSort>>(
      camada::SolverBVSort<MathSATSort>(BitWidth, Context,
                                        msat_get_bv_type(*Context, BitWidth)));
}

SMTSortRef MathSATSolver::getRoundingModeSort() {
  return newSortRef<camada::SolverRMSort<MathSATSort>>(
      camada::SolverRMSort<MathSATSort>(
          Context, msat_get_fp_roundingmode_type(*Context)));
}

SMTSortRef MathSATSolver::getFloatSort(const unsigned ExpWidth,
                                       const unsigned SigWidth) {
  return newSortRef<camada::SolverFPSort<MathSATSort>>(
      camada::SolverFPSort<MathSATSort>(
          ExpWidth, SigWidth, Context,
          msat_get_fp_type(*Context, ExpWidth, SigWidth)));
}

SMTExprRef MathSATSolver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_bv_neg(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_bv_not(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_not(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVAdd(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_plus(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSub(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_minus(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                         toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVMul(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_times(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                      toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSRem(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_srem(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVURem(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_urem(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSDiv(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_sdiv(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVUDiv(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_udiv(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVShl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_lshl(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVAshr(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_ashr(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVLshr(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_lshr(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVXor(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_xor(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_or(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                      toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVAnd(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_and(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVUlt(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_ult(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSlt(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_slt(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVUle(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_uleq(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkBVSle(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_bv_sleq(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, getBoolSort(),
                  msat_make_and(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                                toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, getBoolSort(),
                  msat_make_or(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                               toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  // Do this as and(or(a,b),not(and(a,b)))
  return mkAnd(mkOr(LHS, RHS), mkNot(mkAnd(LHS, RHS)));
}

SMTExprRef MathSATSolver::mkEqual(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, getBoolSort(),
                  msat_make_eq(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                               toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                                const SMTExprRef &F) {
  if (T->isBooleanSort())
    return mkOr(mkAnd(Cond, T), mkAnd(mkNot(Cond), F));

  return newExprRef(MathSATExpr(
      Context, T->Sort,
      msat_make_term_ite(*Context, toSolverExpr<MathSATExpr>(*Cond).Expr,
                         toSolverExpr<MathSATExpr>(*T).Expr,
                         toSolverExpr<MathSATExpr>(*F).Expr)));
}

SMTExprRef MathSATSolver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, getBitvectorSort(i + Exp->getWidth()),
      msat_make_bv_sext(*Context, i, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, getBitvectorSort(i + Exp->getWidth()),
      msat_make_bv_zext(*Context, i, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVExtract(unsigned High, unsigned Low,
                                      const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, getBitvectorSort(High - Low + 1),
                  msat_make_bv_extract(*Context, High, Low,
                                       toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkBVConcat(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, getBitvectorSort(LHS->getWidth() + RHS->getWidth()),
      msat_make_bv_concat(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                          toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPAbs(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_fp_abs(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPNeg(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_fp_neg(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsInfinite(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, getBoolSort(),
      msat_make_fp_isinf(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsNaN(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, getBoolSort(),
      msat_make_fp_isnan(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsDenormal(const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, getBoolSort(),
                  msat_make_fp_issubnormal(
                      *Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsNormal(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, getBoolSort(),
      msat_make_fp_isnormal(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPIsZero(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, getBoolSort(),
      msat_make_fp_iszero(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_fp_times(*Context,
                         toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                         toSolverExpr<MathSATExpr>(*LHS).Expr,
                         toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_fp_div(*Context, toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                       toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPRem(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("MathSAT does not implement fp.rem");
}

SMTExprRef MathSATSolver::mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_fp_plus(*Context, toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                        toSolverExpr<MathSATExpr>(*LHS).Expr,
                        toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, LHS->Sort,
      msat_make_fp_minus(*Context,
                         toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                         toSolverExpr<MathSATExpr>(*LHS).Expr,
                         toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPSqrt(const SMTExprRef &Exp,
                                   const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, Exp->Sort,
      msat_make_fp_sqrt(*Context, toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                        toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkFPFMA(const SMTExprRef &, const SMTExprRef &,
                                  const SMTExprRef &, const RoundingMode) {
  abortWithMessage("MathSAT does not implement fp.fma");
}

SMTExprRef MathSATSolver::mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, getBoolSort(),
      msat_make_fp_lt(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                      toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, getBoolSort(),
      msat_make_fp_leq(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                       toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPEqual(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, getBoolSort(),
      msat_make_fp_equal(*Context, toSolverExpr<MathSATExpr>(*LHS).Expr,
                         toSolverExpr<MathSATExpr>(*RHS).Expr)));
}

SMTExprRef MathSATSolver::mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                                   const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_cast(*Context, To->getFloatExponentWidth(),
                        To->getFloatSignificandWidth(),
                        toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                        toSolverExpr<MathSATExpr>(*From).Expr)));
}

SMTExprRef MathSATSolver::mkSBVtoFP(const SMTExprRef &From,
                                    const SMTSortRef &To,
                                    const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_from_sbv(*Context, To->getFloatExponentWidth(),
                            To->getFloatSignificandWidth(),
                            toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                            toSolverExpr<MathSATExpr>(*From).Expr)));
}

SMTExprRef MathSATSolver::mkUBVtoFP(const SMTExprRef &From,
                                    const SMTSortRef &To,
                                    const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_from_ubv(*Context, To->getFloatExponentWidth(),
                            To->getFloatSignificandWidth(),
                            toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                            toSolverExpr<MathSATExpr>(*From).Expr)));
}

SMTExprRef MathSATSolver::mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(MathSATExpr(
      Context, getBitvectorSort(ToWidth),
      msat_make_fp_to_bv(*Context, ToWidth,
                         toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                         toSolverExpr<MathSATExpr>(*From).Expr)));
}

SMTExprRef MathSATSolver::mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) {
  // We just need to call mkFPtoSBV
  return mkFPtoSBV(From, ToWidth);
}

SMTExprRef MathSATSolver::mkFPtoIntegral(const SMTExprRef &From,
                                         RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, From->Sort,
      msat_make_fp_round_to_int(*Context,
                                toSolverExpr<MathSATExpr>(*roundingMode).Expr,
                                toSolverExpr<MathSATExpr>(*From).Expr)));
}

bool MathSATSolver::getBoolean(const SMTExprRef &Exp) {
  if (msat_term_is_true(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr))
    return true;

  if (msat_term_is_false(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr))
    return false;

  abortWithMessage("Boolean is neither true nor false");
}

template <typename ResType, typename StrToFuncType>
static inline ResType GMPtoType(MathSATSolver &S, const SMTExprRef &Exp,
                                StrToFuncType StrToFunc) {

  SMTExprRef t = S.newExprRef(MathSATExpr(
      S.Context, Exp->Sort,
      msat_get_model_value(*S.Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));

  // GMP rational value object.
  mpq_t val;
  mpq_init(val);
  msat_term_to_number(*toSolverExpr<MathSATExpr>(*t).Context,
                      toSolverExpr<MathSATExpr>(*t).Expr, val);

  mpz_t num;
  mpz_init(num);
  mpz_set(num, mpq_numref(val));
  mpq_clear(val);

  char *buffer = new char[mpz_sizeinbase(num, 10) + 2];
  mpz_get_str(buffer, 10, num);
  mpz_clear(num);

  return StrToFunc(buffer);
}

int64_t MathSATSolver::getBitvector(const SMTExprRef &Exp) {
  camada::abortCondWithMessage(sizeof(int64_t) == sizeof(long int),
                               "Cannot convert GMP value to int");

  return GMPtoType<int64_t>(*this, Exp, [](char *buffer) -> int64_t {
    char *buffer_end = nullptr;
    return std::strtol(buffer, &buffer_end, 10);
  });
}

float MathSATSolver::getFloat(const SMTExprRef &Exp) {
  return GMPtoType<float>(*this, Exp, [](char *buffer) -> float {
    char *buffer_end = nullptr;
    return std::strtof(buffer, &buffer_end);
  });
}

double MathSATSolver::getDouble(const SMTExprRef &Exp) {
  return GMPtoType<double>(*this, Exp, [](char *buffer) -> double {
    char *buffer_end = nullptr;
    return std::strtod(buffer, &buffer_end);
  });
}

bool MathSATSolver::getInterpretation(const SMTExprRef &Exp, int64_t &Inter) {
  // TODO: MathSAT never fails?
  Inter = getBitvector(Exp);
  return true;
}

bool MathSATSolver::getInterpretation(const SMTExprRef &Exp, float &Float) {
  // TODO: MathSAT never fails?
  Float = getFloat(Exp);
  return true;
}

bool MathSATSolver::getInterpretation(const SMTExprRef &Exp, double &Double) {
  // TODO: MathSAT never fails?
  Double = getDouble(Exp);
  return true;
}

SMTExprRef MathSATSolver::mkBoolean(const bool Bool) {
  return newExprRef(
      MathSATExpr(Context, getBoolSort(),
                  Bool ? msat_make_true(*Context) : msat_make_false(*Context)));
}

SMTExprRef MathSATSolver::mkBitvector(const int64_t Int, unsigned BitWidth) {
  const SMTSortRef Sort = getBitvectorSort(BitWidth);
  return newExprRef(
      MathSATExpr(Context, Sort,
                  msat_make_bv_number(*Context, std::to_string(Int).c_str(),
                                      BitWidth, 10)));
}

SMTExprRef MathSATSolver::mkSymbol(const char *Name, SMTSortRef Sort) {
  msat_decl d = msat_declare_function(*Context, Name,
                                      toSolverSort<MathSATSort>(*Sort).Sort);
  abortCondWithMessage(!MSAT_ERROR_DECL(d),
                       "Invalid function symbol declaration sort");
  return newExprRef(
      MathSATExpr(Context, Sort, msat_make_constant(*Context, d)));
}

template <typename FPType, typename IntType>
static inline std::string FPasInt(const FPType FP) {
  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  camada::abortCondWithMessage(sizeof(FPType) == sizeof(IntType),
                               "Cannot convert int to floating-point");

  IntType FPAsInt;
  memcpy(&FPAsInt, &FP, sizeof(FPType));
  return std::to_string(FPAsInt);
}

SMTExprRef MathSATSolver::mkFloat(const float Float) {
  return newExprRef(MathSATExpr(
      Context, getFloat32Sort(),
      msat_make_fp_bits_number(*Context, FPasInt<float, int32_t>(Float).c_str(),
                               8, 24)));
}

SMTExprRef MathSATSolver::mkDouble(const double Double) {
  return newExprRef(MathSATExpr(
      Context, getFloat64Sort(),
      msat_make_fp_bits_number(
          *Context, FPasInt<double, int64_t>(Double).c_str(), 11, 53)));
}

SMTExprRef MathSATSolver::mkRoundingMode(const RoundingMode R) {
  msat_term e;
  switch (R) {
  default:
    camada::abortWithMessage("Unsupported floating-point semantics.");
  case RoundingMode::ROUND_TO_EVEN:
    e = msat_make_fp_roundingmode_nearest_even(*Context);
    break;
  case RoundingMode::ROUND_TO_PLUS_INF:
    e = msat_make_fp_roundingmode_plus_inf(*Context);
    break;
  case RoundingMode::ROUND_TO_MINUS_INF:
    e = msat_make_fp_roundingmode_minus_inf(*Context);
    break;
  case RoundingMode::ROUND_TO_ZERO:
    e = msat_make_fp_roundingmode_zero(*Context);
    break;
  }
  return newExprRef(MathSATExpr(Context, getRoundingModeSort(), e));
}

SMTExprRef MathSATSolver::mkNaN(const bool Sgn, const unsigned ExpWidth,
                                const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  SMTExprRef theNaN = newExprRef(MathSATExpr(
      Context, sort, msat_make_fp_nan(*Context, ExpWidth, SigWidth - 1)));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef MathSATSolver::mkInf(const bool Sgn, const unsigned ExpWidth,
                                const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  return newExprRef(MathSATExpr(
      Context, sort,
      Sgn ? msat_make_fp_minus_inf(*Context, ExpWidth, SigWidth - 1)
          : msat_make_fp_plus_inf(*Context, ExpWidth, SigWidth - 1)));
}

SMTExprRef MathSATSolver::mkBVToIEEEFP(const SMTExprRef &Exp,
                                       const SMTSortRef &To) {
  return newExprRef(MathSATExpr(
      Context, To,
      msat_make_fp_from_ieeebv(*Context, To->getFloatExponentWidth(),
                               To->getFloatSignificandWidth() - 1,
                               toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

SMTExprRef MathSATSolver::mkIEEEFPToBV(const SMTExprRef &Exp) {
  SMTSortRef to = getBitvectorSort(Exp->getWidth());
  return newExprRef(MathSATExpr(
      Context, to,
      msat_make_fp_as_ieeebv(*Context, toSolverExpr<MathSATExpr>(*Exp).Expr)));
}

checkResult MathSATSolver::check() {
  msat_result res = msat_solve(*Context);
  if (res == MSAT_SAT)
    return checkResult::SAT;

  if (res == MSAT_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void MathSATSolver::reset() { msat_reset_env(*Context); }

void MathSATSolver::dump() {
  size_t num_of_asserted;
  msat_term *asserted_formulas =
      msat_get_asserted_formulas(*Context, &num_of_asserted);

  for (unsigned i = 0; i < num_of_asserted; i++)
    fmt::print(stderr, "{}\n", msat_to_smtlib2(*Context, asserted_formulas[i]));
  msat_free(asserted_formulas);
}

void MathSATSolver::dumpModel() {
  // we use a model iterator to retrieve the model values for all the
  // variables, and the necessary function instantiations
  msat_model_iterator iter = msat_create_model_iterator(*Context);
  abortCondWithMessage(!MSAT_ERROR_MODEL_ITERATOR(iter),
                       "Error when getting model iterator");

  fmt::print(stderr, "Model:\n");
  while (msat_model_iterator_has_next(iter)) {
    msat_term t, v;
    char *s;
    msat_model_iterator_next(iter, &t, &v);
    s = msat_term_repr(t);
    abortCondWithMessage(s, "Error when getting variable from model");
    fmt::print(stderr, "{} = ", s);
    msat_free(s);
    s = msat_term_repr(v);
    abortCondWithMessage(s, "Error when getting variable value from model");
    fmt::print(stderr, "{}\n", s);
    msat_free(s);
  }
  msat_destroy_model_iterator(iter);
}

#endif
