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

#include "boolectorsolver.h"
#include "ac_config.h"

#include <fmt/printf.h>

using namespace camada;

#ifdef SOLVER_BOOLECTOR_ENABLED

// Function used to report errors
void BtorErrorHandler(const char *msg) {
  fmt::print(stderr, "Btor error: {}\n", msg);
}

BtorContext::BtorContext() : Context(nullptr) {
  boolector_set_abort(BtorErrorHandler);
  createAndConfig();
}

void BtorContext::createAndConfig() {
  Context = boolector_new();
  boolector_set_opt(Context, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt(Context, BTOR_OPT_AUTO_CLEANUP, 1);
}

BtorContext::~BtorContext() {
  boolector_release_all(Context);
  boolector_delete(Context);
  Context = nullptr;
}

void BtorContext::reset() {
  boolector_release_all(Context);
  boolector_delete(Context);
  Context = nullptr;
  createAndConfig();
}

bool BtorExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort)
    return false;
  return (boolector_get_node_id(Context->Context, Expr) ==
          boolector_get_node_id(Context->Context,
                                dynamic_cast<const BtorExpr &>(Other).Expr));
}

void BtorExpr::dump() const {
  boolector_dump_smt2_node(Context->Context, stderr, Expr);
}

BtorSolver::BtorSolver() : Context(std::make_shared<BtorContext>()) {}

BtorSolver::BtorSolver(BtorContextRef C) : Context(std::move(C)) {}

void BtorSolver::addConstraint(const SMTExprRef &Exp) {
  boolector_assert(Context->Context, toSolverExpr<BtorExpr>(*Exp).Expr);
}

SMTExprRef BtorSolver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<BtorExpr>(toSolverExpr<BtorExpr>(Exp));
}

SMTSortRef BtorSolver::getBoolSort() {
  return newSortRef<camada::SolverBoolSort<BtorSort>>(
      camada::SolverBoolSort<BtorSort>(Context,
                                       boolector_bool_sort(Context->Context)));
}

SMTSortRef BtorSolver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef<camada::SolverBVSort<BtorSort>>(
      camada::SolverBVSort<BtorSort>(
          BitWidth, Context,
          boolector_bitvec_sort(Context->Context, BitWidth)));
}

SMTSortRef BtorSolver::getRoundingModeSort() {
  abortWithMessage("Boolector does not support fp");
}

SMTSortRef BtorSolver::getFloatSort(const unsigned, const unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, Exp->Sort,
      boolector_neg(Context->Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, Exp->Sort,
      boolector_not(Context->Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, Exp->Sort,
      boolector_not(Context->Context, toSolverExpr<BtorExpr>(*Exp).Expr)));
}

SMTExprRef BtorSolver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_add(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_sub(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_mul(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, LHS->Sort,
      boolector_srem(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                     toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, LHS->Sort,
      boolector_urem(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                     toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, LHS->Sort,
      boolector_sdiv(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                     toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, LHS->Sort,
      boolector_udiv(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                     toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_sll(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_sra(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_srl(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_xor(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, LHS->Sort,
               boolector_or(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_and(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_ult(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_slt(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_ugt(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, LHS->Sort,
                             boolector_sgt(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, LHS->Sort,
      boolector_ulte(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                     toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, LHS->Sort,
      boolector_slte(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                     toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, LHS->Sort,
      boolector_ugte(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                     toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, LHS->Sort,
      boolector_sgte(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                     toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, getBoolSort(),
                             boolector_and(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, getBoolSort(),
               boolector_or(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(Context, getBoolSort(),
                             boolector_xor(Context->Context,
                                           toSolverExpr<BtorExpr>(*LHS).Expr,
                                           toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, getBoolSort(),
               boolector_eq(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                            toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                             const SMTExprRef &F) {
  return newExprRef(BtorExpr(Context, T->Sort,
                             boolector_cond(Context->Context,
                                            toSolverExpr<BtorExpr>(*Cond).Expr,
                                            toSolverExpr<BtorExpr>(*T).Expr,
                                            toSolverExpr<BtorExpr>(*F).Expr)));
}

SMTExprRef BtorSolver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, getBitvectorSort(i + Exp->getWidth()),
      boolector_sext(Context->Context, toSolverExpr<BtorExpr>(*Exp).Expr, i)));
}

SMTExprRef BtorSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, getBitvectorSort(i + Exp->getWidth()),
      boolector_uext(Context->Context, toSolverExpr<BtorExpr>(*Exp).Expr, i)));
}

SMTExprRef BtorSolver::mkBVExtract(unsigned High, unsigned Low,
                                   const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, getBitvectorSort(High - Low + 1),
               boolector_slice(Context->Context,
                               toSolverExpr<BtorExpr>(*Exp).Expr, High, Low)));
}

SMTExprRef BtorSolver::mkBVConcat(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(BtorExpr(
      Context, getBitvectorSort(LHS->getWidth() + RHS->getWidth()),
      boolector_concat(Context->Context, toSolverExpr<BtorExpr>(*LHS).Expr,
                       toSolverExpr<BtorExpr>(*RHS).Expr)));
}

SMTExprRef BtorSolver::mkFPAbs(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPNeg(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsInfinite(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsNaN(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsNormal(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsDenormal(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsZero(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPMul(const SMTExprRef &, const SMTExprRef &,
                               const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPDiv(const SMTExprRef &, const SMTExprRef &,
                               const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPRem(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPAdd(const SMTExprRef &, const SMTExprRef &,
                               const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPSub(const SMTExprRef &, const SMTExprRef &,
                               const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPSqrt(const SMTExprRef &, const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPFMA(const SMTExprRef &, const SMTExprRef &,
                               const SMTExprRef &, const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPLt(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPGt(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPLe(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPGe(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPEqual(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPtoFP(const SMTExprRef &, const SMTSortRef &,
                                const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkSBVtoFP(const SMTExprRef &, const SMTSortRef &,
                                 const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkUBVtoFP(const SMTExprRef &, const SMTSortRef &,
                                 const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPtoSBV(const SMTExprRef &, unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPtoUBV(const SMTExprRef &, unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPtoIntegral(const SMTExprRef &, RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

bool BtorSolver::getBoolean(const SMTExprRef &Exp) {
  const char *boolean = boolector_bv_assignment(
      Context->Context, toSolverExpr<BtorExpr>(*Exp).Expr);

  abortCondWithMessage(boolean != nullptr,
                       "Boolector returned null bv assignment string");
  bool res;
  switch (*boolean) {
  case '1':
    res = true;
    break;
  case '0':
    res = false;
    break;
  default:
    abortWithMessage(
        "Boolector returned digit other than 0 or 1 for a boolean");
  }

  boolector_free_bv_assignment(Context->Context, boolean);
  return res;
}

int64_t BtorSolver::getBitvector(const SMTExprRef &Exp) {
  const char *bv = boolector_bv_assignment(Context->Context,
                                           toSolverExpr<BtorExpr>(*Exp).Expr);
  char *foo;
  int64_t finval = strtol(bv, &foo, 2);

  if (bv[0] != '\0' && (foo == bv || *foo != '\0'))
    camada::abortWithMessage(
        "Couldn't parse string representation of Bitvector");

  return finval;
}

float BtorSolver::getFloat(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

double BtorSolver::getDouble(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

bool BtorSolver::getInterpretation(const SMTExprRef &Exp, int64_t &Inter) {
  // TODO: Boolector never fails?
  Inter = getBitvector(Exp);
  return true;
}

bool BtorSolver::getInterpretation(const SMTExprRef &, float &) {
  abortWithMessage("Boolector does not support fp");
}

bool BtorSolver::getInterpretation(const SMTExprRef &, double &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkBoolean(const bool b) {
  return newExprRef(BtorExpr(Context, getBoolSort(),
                             b ? boolector_true(Context->Context)
                               : boolector_false(Context->Context)));
}

SMTExprRef BtorSolver::mkBitvector(const int64_t Int, unsigned BitWidth) {
  const SMTSortRef Sort = getBitvectorSort(BitWidth);
  return newExprRef(BtorExpr(
      Context, Sort,
      boolector_constd(Context->Context, toSolverSort<BtorSort>(*Sort).Sort,
                       std::to_string(Int).c_str())));
}

SMTExprRef BtorSolver::mkSymbol(const char *Name, SMTSortRef Sort) {
  auto it = SymbolTable.find(Name);
  if (it != SymbolTable.end())
    return it->second;

  auto inserted = SymbolTable.insert(SymbolTablet::value_type(
      Name, newExprRef(BtorExpr(
                Context, Sort,
                boolector_var(Context->Context,
                              toSolverSort<BtorSort>(*Sort).Sort, Name)))));

  abortCondWithMessage(inserted.second,
                       "Could not cache new Boolector variable");

  return inserted.first->second;
}

SMTExprRef BtorSolver::mkFloat(const float) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkDouble(const double) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkRoundingMode(const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkNaN(const bool, const unsigned, const unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkInf(const bool, const unsigned, const unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkBVToIEEEFP(const SMTExprRef &, const SMTSortRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkIEEEFPToBV(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

checkResult BtorSolver::check() {
  int res = boolector_sat(Context->Context);
  if (res == BOOLECTOR_SAT)
    return checkResult::SAT;

  if (res == BOOLECTOR_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void BtorSolver::reset() { Context->reset(); }

void BtorSolver::dump() { boolector_dump_smt2(Context->Context, stderr); }

void BtorSolver::dumpModel() {
  boolector_print_model(Context->Context, const_cast<char *>("smt2"), stderr);
}

#endif
