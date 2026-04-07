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

#if SOLVER_CVC5_ENABLED

#include "cvc5solver.h"

#include <cstdio>

namespace camada {

static inline void parseCVC5RationalValue(const std::string &Value,
                                          std::string &Num, std::string &Den) {
  const auto slash = Value.find('/');
  if (slash == std::string::npos) {
    Num = Value;
    Den = "1";
    return;
  }
  Num = Value.substr(0, slash);
  Den = Value.substr(slash + 1);
}

unsigned CVC5Sort::getWidthFromSolver() const {
  if (Sort.isBitVector()) {
    cvc5::Sort bvType = static_cast<cvc5::Sort>(Sort);
    return bvType.getBitVectorSize();
  }

  if (Sort.isBoolean())
    return 1;

  if (Sort.isInteger() || Sort.isReal())
    return 0;

  if (Sort.isRoundingMode())
    return 3;

  assert(Sort.isFloatingPoint());
  cvc5::Sort fpType = static_cast<cvc5::Sort>(Sort);
  return fpType.getFloatingPointExponentSize() +
         fpType.getFloatingPointSignificandSize();
}

void CVC5Sort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void CVC5Sort::dump(std::string &Out) const {
  Out = Sort.toString();
  Out += "\n";
}

bool CVC5Expr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return (Expr == static_cast<const CVC5Expr &>(Other).Expr);
}

void CVC5Expr::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void CVC5Expr::dump(std::string &Out) const {
  Out = Expr.toString();
  Out += "\n";
}

CVC5Solver::CVC5Solver()
    : SMTSolverImpl(), OwnedTerms(std::make_unique<cvc5::TermManager>()),
      Terms(OwnedTerms.get()),
      OwnedContext(std::make_unique<cvc5::Solver>(*Terms)),
      Context(OwnedContext.get()) {
  Context->setOption("arrays-exp", "true");
  Context->setOption("produce-models", "true");
  Context->setOption("produce-assertions", "true");
  initializeCommonSingletons();
}

CVC5Solver::~CVC5Solver() { invalidateGeneratedObjects(); }

void CVC5Solver::addConstraintImpl(const SMTExprRef &Exp) {
  Context->assertFormula(toSolverExpr<CVC5Expr>(*Exp).Expr);
}

SMTExprRef CVC5Solver::newExprRefImpl(const SMTExpr &Exp) const {
  return storeExprRef(toSolverExpr<CVC5Expr>(Exp));
}

SMTExprRef CVC5Solver::cloneExprWithSortImpl(const SMTExpr &Exp,
                                             const SMTSortRef &Sort) const {
  CVC5Expr Retagged = toSolverExpr<CVC5Expr>(Exp);
  Retagged.Sort = Sort;
  return storeExprRef(Retagged);
}

SMTSortRef CVC5Solver::mkBoolSortImpl() {
  return newSortRef<CVC5Sort>(
      CVC5Sort(SMTSortKind::Bool, Context, Terms->getBooleanSort(), 1));
}

SMTSortRef CVC5Solver::mkIntSortImpl() {
  return newSortRef<CVC5Sort>(
      CVC5Sort(SMTSortKind::Int, Context, Terms->getIntegerSort()));
}

SMTSortRef CVC5Solver::mkRealSortImpl() {
  return newSortRef<CVC5Sort>(
      CVC5Sort(SMTSortKind::Real, Context, Terms->getRealSort()));
}

SMTSortRef CVC5Solver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<CVC5Sort>(CVC5Sort(
      SMTSortKind::BV, Context, Terms->mkBitVectorSort(BitWidth), BitWidth));
}

SMTSortRef CVC5Solver::mkRMSortImpl() {
  return newSortRef<CVC5Sort>(
      CVC5Sort(SMTSortKind::RM, Context, Terms->getRoundingModeSort(), 3));
}

SMTSortRef CVC5Solver::mkFPSortImpl(const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  return newSortRef<CVC5Sort>(
      CVC5Sort(SMTSortKind::FP, Context,
               Terms->mkFloatingPointSort(ExpWidth, SigWidth + 1),
               ExpWidth + SigWidth + 1, ExpWidth, SigWidth));
}

SMTSortRef CVC5Solver::mkBVFPSortImpl(const unsigned ExpWidth,
                                      const unsigned SigWidth) {
  return newSortRef<CVC5Sort>(
      CVC5Sort(SMTSortKind::BVFP, Context,
               Terms->mkBitVectorSort(ExpWidth + SigWidth + 1),
               ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1));
}

SMTSortRef CVC5Solver::mkBVRMSortImpl() {
  return newSortRef<CVC5Sort>(
      CVC5Sort(SMTSortKind::BVRM, Context, Terms->mkBitVectorSort(3), 3));
}

SMTSortRef CVC5Solver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                       const SMTSortRef &ElemSort) {
  return newSortRef<CVC5Sort>(
      CVC5Sort(SMTSortKind::Array, Context,
               Terms->mkArraySort(toSolverSort<CVC5Sort>(*IndexSort).Sort,
                                  toSolverSort<CVC5Sort>(*ElemSort).Sort),
               0, 0, 0, IndexSort, ElemSort));
}

SMTSortRef
CVC5Solver::mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                               const SMTSortRef &CodomainSort) {
  std::vector<cvc5::Sort> Domain;
  Domain.reserve(DomainSorts.size());
  for (const auto &Sort : DomainSorts)
    Domain.push_back(toSolverSort<CVC5Sort>(*Sort).Sort);
  return newSortRef<CVC5Sort>(CVC5Sort(
      SMTSortKind::Function, Context,
      Terms->mkFunctionSort(Domain, toSolverSort<CVC5Sort>(*CodomainSort).Sort),
      0, 0, 0, {}, {}, DomainSorts, CodomainSort));
}

SMTExprRef CVC5Solver::mkBVNegImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, Exp->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_NEG,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkBVNotImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, Exp->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_NOT,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkNotImpl(const SMTExprRef &Exp) {
  return newExprRef(CVC5Expr(
      Context, Exp->Sort,
      Terms->mkTerm(cvc5::Kind::NOT, {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkBVAddImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_ADD,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVSubImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_SUB,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVMulImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_MULT,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVSRemImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_SREM,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVURemImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_UREM,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVSDivImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_SDIV,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVUDivImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_UDIV,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVShlImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_SHL,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVAshrImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_ASHR,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVLshrImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_LSHR,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVXorImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_XOR,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVOrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_OR,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVAndImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_AND,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVXnorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_XNOR,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVNorImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_NOR,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVNandImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::BITVECTOR_NAND,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVUltImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_ULT,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVSltImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_SLT,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVUgtImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_UGT,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVSgtImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_SGT,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVUleImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_ULE,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVSleImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_SLE,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVUgeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_UGE,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkBVSgeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_SGE,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkImpliesImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::IMPLIES, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                          toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::AND, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                      toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::OR, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                     toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::XOR, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                      toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithNegImpl(const SMTExprRef &Exp) {
  return newExprRef(CVC5Expr(
      Context, Exp->Sort,
      Terms->mkTerm(cvc5::Kind::NEG, {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkArithAddImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, LHS->Sort,
      Terms->mkTerm(cvc5::Kind::ADD, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                      toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithSubImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, LHS->Sort,
      Terms->mkTerm(cvc5::Kind::SUB, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                      toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithMulImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, LHS->Sort,
      Terms->mkTerm(cvc5::Kind::MULT, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                       toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithDivImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::DIVISION,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithModImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkIntSort(),
               Terms->mkTerm(cvc5::Kind::INTS_MODULUS,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithShlImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkIntSort(),
      Terms->mkTerm(cvc5::Kind::MULT,
                    {toSolverExpr<CVC5Expr>(*LHS).Expr,
                     Terms->mkTerm(cvc5::Kind::POW,
                                   {Terms->mkInteger(2),
                                    toSolverExpr<CVC5Expr>(*RHS).Expr})})));
}

SMTExprRef CVC5Solver::mkArithLtImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::LT, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                     toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithGtImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::GT, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                     toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithLeImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::LEQ, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                      toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArithGeImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::GEQ, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                      toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkInt2RealImpl(const SMTExprRef &Exp) {
  return newExprRef(CVC5Expr(
      Context, mkRealSort(),
      Terms->mkTerm(cvc5::Kind::TO_REAL, {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkReal2IntImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, mkIntSort(),
               Terms->mkTerm(cvc5::Kind::TO_INTEGER,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkIsIntImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::IS_INTEGER,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkEqualImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::EQUAL, {toSolverExpr<CVC5Expr>(*LHS).Expr,
                                        toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                 const SMTExprRef &F) {
  return newExprRef(CVC5Expr(
      Context, T->Sort,
      Terms->mkTerm(cvc5::Kind::ITE, {toSolverExpr<CVC5Expr>(*Cond).Expr,
                                      toSolverExpr<CVC5Expr>(*T).Expr,
                                      toSolverExpr<CVC5Expr>(*F).Expr})));
}

SMTExprRef CVC5Solver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(CVC5Expr(
      Context, mkBVSort(i + Exp->getWidth()),
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::BITVECTOR_SIGN_EXTEND, {i}),
                    {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(CVC5Expr(
      Context, mkBVSort(i + Exp->getWidth()),
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::BITVECTOR_ZERO_EXTEND, {i}),
                    {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkBVExtractImpl(unsigned High, unsigned Low,
                                       const SMTExprRef &Exp) {
  return newExprRef(CVC5Expr(
      Context, mkBVSort(High - Low + 1),
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::BITVECTOR_EXTRACT, {High, Low}),
                    {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkBVConcatImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBVSort(LHS->getWidth() + RHS->getWidth()),
               Terms->mkTerm(cvc5::Kind::BITVECTOR_CONCAT,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkArraySelectImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index) {
  return newExprRef(
      CVC5Expr(Context, Array->Sort->getElementSort(),
               Terms->mkTerm(cvc5::Kind::SELECT,
                             {toSolverExpr<CVC5Expr>(*Array).Expr,
                              toSolverExpr<CVC5Expr>(*Index).Expr})));
}

SMTExprRef CVC5Solver::mkArrayStoreImpl(const SMTExprRef &Array,
                                        const SMTExprRef &Index,
                                        const SMTExprRef &Element) {
  return newExprRef(
      CVC5Expr(Context, Array->Sort,
               Terms->mkTerm(cvc5::Kind::STORE,
                             {toSolverExpr<CVC5Expr>(*Array).Expr,
                              toSolverExpr<CVC5Expr>(*Index).Expr,
                              toSolverExpr<CVC5Expr>(*Element).Expr})));
}

SMTExprRef CVC5Solver::mkApplyImpl(const SMTExprRef &Function,
                                   const std::vector<SMTExprRef> &Args) {
  std::vector<cvc5::Term> ApplyArgs;
  ApplyArgs.reserve(Args.size() + 1);
  ApplyArgs.push_back(toSolverExpr<CVC5Expr>(*Function).Expr);
  for (const auto &Arg : Args)
    ApplyArgs.push_back(toSolverExpr<CVC5Expr>(*Arg).Expr);
  return newExprRef(CVC5Expr(Context, Function->Sort->getCodomainSort(),
                             Terms->mkTerm(cvc5::Kind::APPLY_UF, ApplyArgs)));
}

SMTExprRef CVC5Solver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, Exp->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_ABS,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkFPNegImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, Exp->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_NEG,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_IS_INF,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_IS_NAN,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_IS_SUBNORMAL,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_IS_NORMAL,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_IS_ZERO,
                             {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const SMTExprRef &R) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_MULT,
                             {toSolverExpr<CVC5Expr>(*R).Expr,
                              toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const SMTExprRef &R) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_DIV,
                             {toSolverExpr<CVC5Expr>(*R).Expr,
                              toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPRemImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_REM,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const SMTExprRef &R) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_ADD,
                             {toSolverExpr<CVC5Expr>(*R).Expr,
                              toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                   const SMTExprRef &R) {
  return newExprRef(
      CVC5Expr(Context, LHS->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_SUB,
                             {toSolverExpr<CVC5Expr>(*R).Expr,
                              toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPSqrtImpl(const SMTExprRef &Exp,
                                    const SMTExprRef &R) {
  return newExprRef(
      CVC5Expr(Context, Exp->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_SQRT,
                             {toSolverExpr<CVC5Expr>(*R).Expr,
                              toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                   const SMTExprRef &Z, const SMTExprRef &R) {
  return newExprRef(CVC5Expr(Context, X->Sort,
                             Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_FMA,
                                           {toSolverExpr<CVC5Expr>(*R).Expr,
                                            toSolverExpr<CVC5Expr>(*X).Expr,
                                            toSolverExpr<CVC5Expr>(*Y).Expr,
                                            toSolverExpr<CVC5Expr>(*Z).Expr})));
}

SMTExprRef CVC5Solver::mkFPLtImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_LT,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPGtImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_GT,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPLeImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_LEQ,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPGeImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_GEQ,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPEqualImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(
      CVC5Expr(Context, mkBoolSort(),
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_EQ,
                             {toSolverExpr<CVC5Expr>(*LHS).Expr,
                              toSolverExpr<CVC5Expr>(*RHS).Expr})));
}

SMTExprRef CVC5Solver::mkFPtoFPImpl(const SMTExprRef &From,
                                    const SMTSortRef &To, const SMTExprRef &R) {
  return newExprRef(CVC5Expr(
      Context, To,
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_FP,
                                {To->getFPExponentWidth(),
                                 To->getFPSignificandWidth() + 1}),
                    {toSolverExpr<CVC5Expr>(*R).Expr,
                     toSolverExpr<CVC5Expr>(*From).Expr})));
}

SMTExprRef CVC5Solver::mkSBVtoFPImpl(const SMTExprRef &From,
                                     const SMTSortRef &To,
                                     const SMTExprRef &R) {
  return newExprRef(CVC5Expr(
      Context, To,
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_SBV,
                                {To->getFPExponentWidth(),
                                 To->getFPSignificandWidth() + 1}),
                    {toSolverExpr<CVC5Expr>(*R).Expr,
                     toSolverExpr<CVC5Expr>(*From).Expr})));
}

SMTExprRef CVC5Solver::mkUBVtoFPImpl(const SMTExprRef &From,
                                     const SMTSortRef &To,
                                     const SMTExprRef &R) {
  return newExprRef(CVC5Expr(
      Context, To,
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_UBV,
                                {To->getFPExponentWidth(),
                                 To->getFPSignificandWidth() + 1}),
                    {toSolverExpr<CVC5Expr>(*R).Expr,
                     toSolverExpr<CVC5Expr>(*From).Expr})));
}

SMTExprRef CVC5Solver::mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return newExprRef(CVC5Expr(
      Context, mkBVSort(ToWidth),
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::FLOATINGPOINT_TO_SBV, {ToWidth}),
                    {toSolverExpr<CVC5Expr>(*roundingMode).Expr,
                     toSolverExpr<CVC5Expr>(*From).Expr})));
}

SMTExprRef CVC5Solver::mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return newExprRef(CVC5Expr(
      Context, mkBVSort(ToWidth),
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::FLOATINGPOINT_TO_UBV, {ToWidth}),
                    {toSolverExpr<CVC5Expr>(*roundingMode).Expr,
                     toSolverExpr<CVC5Expr>(*From).Expr})));
}

SMTExprRef CVC5Solver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                          const SMTExprRef &R) {
  return newExprRef(
      CVC5Expr(Context, From->Sort,
               Terms->mkTerm(cvc5::Kind::FLOATINGPOINT_RTI,
                             {toSolverExpr<CVC5Expr>(*R).Expr,
                              toSolverExpr<CVC5Expr>(*From).Expr})));
}

bool CVC5Solver::getBoolImpl(const SMTExprRef &Exp) {
  return Context->getValue(toSolverExpr<CVC5Expr>(*Exp).Expr).getBooleanValue();
}

std::string CVC5Solver::getBVInBinImpl(const SMTExprRef &Exp) {
  return Context->getValue(toSolverExpr<CVC5Expr>(*Exp).Expr)
      .getBitVectorValue();
}

std::string CVC5Solver::getIntImpl(const SMTExprRef &Exp) {
  cvc5::Term value = Context->getValue(toSolverExpr<CVC5Expr>(*Exp).Expr);
  if (Exp->isRealSort()) {
    std::string num, den;
    getRationalImpl(Exp, num, den);
    assert(den == "1" && "Real value is not integral");
    return num;
  }
  assert(value.isIntegerValue() && "Expected integer model value");
  return value.getIntegerValue();
}

void CVC5Solver::getRationalImpl(const SMTExprRef &Exp, std::string &Num,
                                 std::string &Den) {
  cvc5::Term value = Context->getValue(toSolverExpr<CVC5Expr>(*Exp).Expr);
  assert(value.isRealValue() && "Expected rational model value");
  parseCVC5RationalValue(value.getRealValue(), Num, Den);
}

std::string CVC5Solver::getFPInBinImpl(const SMTExprRef &Exp) {
  std::tuple<uint32_t, uint32_t, cvc5::Term> fp =
      Context->getValue(toSolverExpr<CVC5Expr>(*Exp).Expr)
          .getFloatingPointValue();
  return std::get<2>(fp).getBitVectorValue();
}

SMTExprRef CVC5Solver::getArrayElementImpl(const SMTExprRef &Array,
                                           const SMTExprRef &Index) {
  const SMTExprRef &sel = mkArraySelect(Array, Index);
  return newExprRef(
      CVC5Expr(Context, sel->Sort,
               Context->getValue(toSolverExpr<CVC5Expr>(*sel).Expr)));
}

SMTExprRef CVC5Solver::mkBoolImpl(const bool b) {
  return newExprRef(CVC5Expr(Context, mkBoolSort(), Terms->mkBoolean(b)));
}

SMTExprRef CVC5Solver::mkIntImpl(int64_t v) {
  return newExprRef(CVC5Expr(Context, mkIntSort(), Terms->mkInteger(v)));
}

SMTExprRef CVC5Solver::mkIntImpl(const std::string &v) {
  return newExprRef(CVC5Expr(Context, mkIntSort(), Terms->mkInteger(v)));
}

SMTExprRef CVC5Solver::mkRealImpl(const std::string &v) {
  return newExprRef(CVC5Expr(Context, mkRealSort(), Terms->mkReal(v)));
}

SMTExprRef CVC5Solver::mkRealImpl(int64_t v) {
  return newExprRef(CVC5Expr(Context, mkRealSort(), Terms->mkReal(v)));
}

SMTExprRef CVC5Solver::mkRealImpl(int64_t num, int64_t den) {
  return newExprRef(CVC5Expr(Context, mkRealSort(), Terms->mkReal(num, den)));
}

SMTExprRef CVC5Solver::mkBVFromDecImpl(const int64_t Int,
                                       const SMTSortRef &Sort) {
  return newExprRef(
      CVC5Expr(Context, Sort, Terms->mkBitVector(Sort->getWidth(), Int)));
}

SMTExprRef CVC5Solver::mkBVFromBinImpl(const std::string &Int,
                                       const SMTSortRef &Sort) {
  return newExprRef(
      CVC5Expr(Context, Sort, Terms->mkBitVector(Sort->getWidth(), Int, 2)));
}

SMTExprRef CVC5Solver::mkSymbolImpl(const std::string &Name,
                                    const SMTSortRef &Sort) {

  // Standard arrangement: if we already have the name, return the expression
  // from the symbol table. If not, time for a new name.
  auto it = SymbolTable.find(Name);
  if (it != SymbolTable.end())
    return it->second;

  // Time for a new one.
  auto inserted = SymbolTable.insert(SymbolTablet::value_type(
      Name, newExprRef(CVC5Expr(
                Context, Sort,
                Terms->mkConst(toSolverSort<CVC5Sort>(*Sort).Sort, Name)))));

  assert(inserted.second && "Could not cache new CVC5 variable");
  return inserted.first->second;
}

SMTExprRef CVC5Solver::mkFPFromBinImpl(const std::string &FP, unsigned EWidth) {
  unsigned SWidth = FP.length() - EWidth - 1;
  const SMTSortRef &sort = mkFPSort(EWidth, SWidth, FPEncoding::Native);
  return newExprRef(CVC5Expr(
      Context, sort,
      Terms->mkFloatingPoint(EWidth, SWidth + 1,
                             Terms->mkBitVector(sort->getWidth(), FP, 2))));
}

SMTExprRef CVC5Solver::mkRMImpl(const RM &R) {
  cvc5::Term e;
  switch (R) {
  default:
    assert(0 && "Unsupported floating-point semantics.");
    __builtin_unreachable();
  case RM::ROUND_TO_EVEN:
    e = Terms->mkRoundingMode(cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
    break;
  case RM::ROUND_TO_AWAY:
    e = Terms->mkRoundingMode(cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
    break;
  case RM::ROUND_TO_PLUS_INF:
    e = Terms->mkRoundingMode(cvc5::RoundingMode::ROUND_TOWARD_POSITIVE);
    break;
  case RM::ROUND_TO_MINUS_INF:
    e = Terms->mkRoundingMode(cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE);
    break;
  case RM::ROUND_TO_ZERO:
    e = Terms->mkRoundingMode(cvc5::RoundingMode::ROUND_TOWARD_ZERO);
    break;
  }
  return newExprRef(CVC5Expr(Context, mkRMSortImpl(), e));
}

SMTExprRef CVC5Solver::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                 const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth, FPEncoding::Native);
  const SMTExprRef &theNaN = newExprRef(
      CVC5Expr(Context, sort, Terms->mkFloatingPointNaN(ExpWidth, SigWidth)));
  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef CVC5Solver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                 const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth, FPEncoding::Native);
  return newExprRef(
      CVC5Expr(Context, sort,
               Sgn ? Terms->mkFloatingPointNegInf(ExpWidth, SigWidth)
                   : Terms->mkFloatingPointPosInf(ExpWidth, SigWidth)));
}

SMTExprRef CVC5Solver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                        const SMTSortRef &To) {
  return newExprRef(CVC5Expr(
      Context, To,
      Terms->mkTerm(Terms->mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
                                {To->getFPExponentWidth(),
                                 To->getFPSignificandWidth() + 1}),
                    {toSolverExpr<CVC5Expr>(*Exp).Expr})));
}

SMTExprRef CVC5Solver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  // CVC5 does not provide a direct way to convert from fp
  // to bv, so we create a new symbol
  const std::string name = "__CAMADA_ieeebv" + std::to_string(ToBVCounter++);

  const SMTSortRef &to =
      mkFPSort(Exp->Sort->getFPExponentWidth(),
               Exp->Sort->getFPSignificandWidth(), FPEncoding::BV);
  const SMTExprRef &newSymbol = mkSymbol(name, to);

  // and constraint it to be the conversion of the fp, since
  // (fp_matches_bv f bv) <-> (= f ((_ to_fp E S) bv))
  addConstraint(mkEqual(Exp, mkBVToIEEEFP(newSymbol, Exp->Sort)));

  // NewSymbol is the resulting bitvector
  return newSymbol;
}

SMTExprRef CVC5Solver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                        const SMTExprRef &InitValue) {
  const SMTSortRef &sort = mkArraySort(IndexSort, InitValue->Sort);
  return newExprRef(
      CVC5Expr(Context, sort,
               Terms->mkConstArray(toSolverSort<CVC5Sort>(*sort).Sort,
                                   toSolverExpr<CVC5Expr>(*InitValue).Expr)));
}

SMTExprRef CVC5Solver::mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                    const SMTExprRef &Body) {
  std::vector<cvc5::Term> old_terms;
  std::vector<cvc5::Term> bound_vars;
  old_terms.reserve(Vars.size());
  bound_vars.reserve(Vars.size());
  for (std::size_t i = 0; i < Vars.size(); ++i) {
    const SMTExprRef &Var = Vars[i];
    old_terms.push_back(toSolverExpr<CVC5Expr>(*Var).Expr);
    bound_vars.push_back(Terms->mkVar(toSolverSort<CVC5Sort>(*Var->Sort).Sort,
                                      "__CAMADA_qvar" + std::to_string(i)));
  }
  cvc5::Term bound_list = Terms->mkTerm(cvc5::Kind::VARIABLE_LIST, bound_vars);
  cvc5::Term substituted_body =
      toSolverExpr<CVC5Expr>(*Body).Expr.substitute(old_terms, bound_vars);
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::FORALL, {bound_list, substituted_body})));
}

SMTExprRef CVC5Solver::mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                    const SMTExprRef &Body) {
  std::vector<cvc5::Term> old_terms;
  std::vector<cvc5::Term> bound_vars;
  old_terms.reserve(Vars.size());
  bound_vars.reserve(Vars.size());
  for (std::size_t i = 0; i < Vars.size(); ++i) {
    const SMTExprRef &Var = Vars[i];
    old_terms.push_back(toSolverExpr<CVC5Expr>(*Var).Expr);
    bound_vars.push_back(Terms->mkVar(toSolverSort<CVC5Sort>(*Var->Sort).Sort,
                                      "__CAMADA_qvar" + std::to_string(i)));
  }
  cvc5::Term bound_list = Terms->mkTerm(cvc5::Kind::VARIABLE_LIST, bound_vars);
  cvc5::Term substituted_body =
      toSolverExpr<CVC5Expr>(*Body).Expr.substitute(old_terms, bound_vars);
  return newExprRef(CVC5Expr(
      Context, mkBoolSort(),
      Terms->mkTerm(cvc5::Kind::EXISTS, {bound_list, substituted_body})));
}

checkResult CVC5Solver::checkImpl() {
  cvc5::Result res = Context->checkSat();
  if (res.isSat())
    return checkResult::SAT;

  if (res.isUnknown())
    return checkResult::UNKNOWN;

  return checkResult::UNSAT;
}

void CVC5Solver::resetImpl() {
  SymbolTable.clear();
  Context->resetAssertions();
}

void CVC5Solver::pushImpl(unsigned nscopes) { Context->push(nscopes); }

void CVC5Solver::popImpl(unsigned nscopes) { Context->pop(nscopes); }

std::string CVC5Solver::getSolverNameAndVersion() const {
  return std::string("CVC5 v").append(Context->getVersion());
}

void CVC5Solver::dumpImpl() {
  std::string Out;
  dumpImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void CVC5Solver::dumpImpl(std::string &Out) {
  Out.clear();
  auto const &assertions = Context->getAssertions();
  for (auto const &a : assertions) {
    Out += a.toString();
    Out += "\n";
  }
}

void CVC5Solver::dumpModelImpl() {
  std::string Out;
  dumpModelImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void CVC5Solver::dumpModelImpl(std::string &Out) {
  Out.clear();
  auto const &assertions = Context->getAssertions();
  for (auto const &a : assertions) {
    Out += Context->getValue(a).toString();
    Out += "\n";
  }
}

} // namespace camada

#endif
