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

#ifndef CVC4SOLVER_H_
#define CVC4SOLVER_H_

#include "camadafp.h"

#include <cvc4/cvc4.h>

namespace camada {

using CVC4ContextRef = std::shared_ptr<CVC4::ExprManager>;

/// Wrapper for CVC4 Sort
class CVC4Sort : public SolverSort<CVC4ContextRef, CVC4::Type> {
public:
  using SolverSort<CVC4ContextRef, CVC4::Type>::SolverSort;
  virtual ~CVC4Sort() = default;

  void dump() const override;
}; // end class CVC4Sort

class CVC4Expr : public SolverExpr<CVC4ContextRef, CVC4::Expr> {
public:
  using SolverExpr<CVC4ContextRef, CVC4::Expr>::SolverExpr;
  virtual ~CVC4Expr() = default;

  /// Comparison of Expr equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class CVC4Expr

class CVC4Solver : public SMTFPSolver {
public:
  CVC4ContextRef Context;

  CVC4::SmtEngine Solver;

  CVC4::SymbolTable SymbolTable;

  unsigned int ToBVCounter = 0;

  explicit CVC4Solver();
  virtual ~CVC4Solver() = default;

  virtual void setConfig();

  void addConstraint(const SMTExprRef &Exp) override;

  SMTExprRef newExprRef(const SMTExpr &Exp) const override;

  SMTSortRef mkBoolSort() override;

  SMTSortRef mkBVSort(unsigned BitWidth) override;

  SMTSortRef mkRMSortImpl() override;

  SMTSortRef mkFPSortImpl(const unsigned ExpWidth,
                          const unsigned SigWidth) override;

  SMTSortRef getBVFPSort(const unsigned ExpWidth,
                         const unsigned SigWidth) override;

  SMTSortRef getBVRMSort() override;

  SMTSortRef mkArraySort(const SMTSortRef &IndexType,
                         const SMTSortRef &ElemType) override;

  SMTExprRef mkBVNeg(const SMTExprRef &Exp) override;

  SMTExprRef mkBVNot(const SMTExprRef &Exp) override;

  SMTExprRef mkNot(const SMTExprRef &Exp) override;

  SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                   const SMTExprRef &F) override;

  SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) override;

  SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) override;

  SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                         const SMTExprRef &Exp) override;

  SMTExprRef mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkArraySelect(const SMTExprRef &Array,
                           const SMTExprRef &Index) override;

  SMTExprRef mkArrayStore(const SMTExprRef &Array, const SMTExprRef &Index,
                          const SMTExprRef &Element) override;

  SMTExprRef mkFPAbsImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPNegImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsInfiniteImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsNaNImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsDenormalImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsNormalImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsZeroImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const RM &R) override;

  SMTExprRef mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const RM &R) override;

  SMTExprRef mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const RM &R) override;

  SMTExprRef mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const RM &R) override;

  SMTExprRef mkFPSqrtImpl(const SMTExprRef &Exp, const RM &R) override;

  SMTExprRef mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                         const SMTExprRef &Z, const RM &R) override;

  SMTExprRef mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPEqualImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;

  SMTExprRef mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                          const RM &R) override;

  SMTExprRef mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                           const RM &R) override;

  SMTExprRef mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                           const RM &R) override;

  SMTExprRef mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth) override;

  SMTExprRef mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth) override;

  SMTExprRef mkFPtoIntegralImpl(const SMTExprRef &From, RM R) override;

  bool getBool(const SMTExprRef &Exp) override;

  std::string getBVInBin(const SMTExprRef &Exp) override;

  std::string getFPInBinImpl(const SMTExprRef &Exp) override;

  SMTExprRef getArrayElement(const SMTExprRef &Array,
                             const SMTExprRef &Index) override;

  SMTExprRef mkBool(const bool b) override;

  SMTExprRef mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) override;

  SMTExprRef mkBVFromBin(const std::string &Int,
                         const SMTSortRef &Sort) override;

  SMTExprRef mkSymbol(const std::string &Name, SMTSortRef Sort) override;

  SMTExprRef mkFPFromBinImpl(const std::string &FP, unsigned EWidth) override;

  SMTExprRef mkRMImpl(const RM &R) override;

  SMTExprRef mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                       const unsigned SigWidth) override;

  SMTExprRef mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                       const unsigned SigWidth) override;

  SMTExprRef mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                              const SMTSortRef &To) override;

  SMTExprRef mkIEEEFPToBVImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                          const SMTExprRef &InitValue) override;

  checkResult check() override;

  void reset() override;

  void dump() override;

  void dumpModel() override;
}; // end class CVC4Solver

} // namespace camada

#endif
