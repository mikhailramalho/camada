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

#ifndef CVC5SOLVER_H_
#define CVC5SOLVER_H_

#include "camadaimpl.h"

#include <cvc5/cvc5.h>

namespace camada {

using CVC5ContextRef = std::shared_ptr<cvc5::Solver>;

/// Wrapper for CVC5 Sort
class CVC5Sort : public SolverSort<CVC5ContextRef, cvc5::Sort> {
public:
  using SolverSort<CVC5ContextRef, cvc5::Sort>::SolverSort;
  ~CVC5Sort() override = default;

  unsigned getWidthFromSolver() const override;

  void dump() const override;
}; // end class CVC5Sort

class CVC5Expr : public SolverExpr<CVC5ContextRef, cvc5::Term> {
public:
  using SolverExpr<CVC5ContextRef, cvc5::Term>::SolverExpr;
  ~CVC5Expr() override = default;

  /// Comparison of Expr equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class CVC5Expr

class CVC5Solver : public SMTSolverImpl {
public:
  CVC5ContextRef Context;

  unsigned int ToBVCounter = 0;

  explicit CVC5Solver();
  ~CVC5Solver() override = default;

  void addConstraintImpl(const SMTExprRef &Exp) override;

  SMTExprRef newExprRefImpl(const SMTExpr &Exp) const override;

  SMTSortRef mkBoolSortImpl() override;

  SMTSortRef mkBVSortImpl(unsigned BitWidth) override;

  SMTSortRef mkRMSortImpl() override;

  SMTSortRef mkFPSortImpl(const unsigned ExpWidth,
                          const unsigned SigWidth) override;

  SMTSortRef mkBVFPSortImpl(const unsigned ExpWidth,
                            const unsigned SigWidth) override;

  SMTSortRef mkBVRMSortImpl() override;

  SMTSortRef mkArraySortImpl(const SMTSortRef &IndexSort,
                             const SMTSortRef &ElemSort) override;

  SMTExprRef mkBVNegImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkBVNotImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkNotImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkBVAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSRemImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;

  SMTExprRef mkBVURemImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;

  SMTExprRef mkBVSDivImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;

  SMTExprRef mkBVUDivImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;

  SMTExprRef mkBVShlImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVAshrImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;

  SMTExprRef mkBVLshrImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;

  SMTExprRef mkBVXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVXnorImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;

  SMTExprRef mkBVNorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVNandImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;

  SMTExprRef mkBVUltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkImpliesImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;

  SMTExprRef mkAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkEqualImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                       const SMTExprRef &F) override;

  SMTExprRef mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) override;

  SMTExprRef mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) override;

  SMTExprRef mkBVExtractImpl(unsigned High, unsigned Low,
                             const SMTExprRef &Exp) override;

  SMTExprRef mkBVConcatImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;

  SMTExprRef mkArraySelectImpl(const SMTExprRef &Array,
                               const SMTExprRef &Index) override;

  SMTExprRef mkArrayStoreImpl(const SMTExprRef &Array, const SMTExprRef &Index,
                              const SMTExprRef &Element) override;

  SMTExprRef mkFPAbsImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPNegImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsInfiniteImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsNaNImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsDenormalImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsNormalImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsZeroImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const SMTExprRef &R) override;

  SMTExprRef mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const SMTExprRef &R) override;

  SMTExprRef mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const SMTExprRef &R) override;

  SMTExprRef mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const SMTExprRef &R) override;

  SMTExprRef mkFPSqrtImpl(const SMTExprRef &Exp, const SMTExprRef &R) override;

  SMTExprRef mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                         const SMTExprRef &Z, const SMTExprRef &R) override;

  SMTExprRef mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPGtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPGeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPEqualImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;

  SMTExprRef mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                          const SMTExprRef &R) override;

  SMTExprRef mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                           const SMTExprRef &R) override;

  SMTExprRef mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                           const SMTExprRef &R) override;

  SMTExprRef mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth) override;

  SMTExprRef mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth) override;

  SMTExprRef mkFPtoIntegralImpl(const SMTExprRef &From,
                                const SMTExprRef &R) override;

  bool getBoolImpl(const SMTExprRef &Exp) override;

  std::string getBVInBinImpl(const SMTExprRef &Exp) override;

  std::string getFPInBinImpl(const SMTExprRef &Exp) override;

  SMTExprRef getArrayElementImpl(const SMTExprRef &Array,
                                 const SMTExprRef &Index) override;

  SMTExprRef mkBoolImpl(const bool b) override;

  SMTExprRef mkBVFromDecImpl(const int64_t Int,
                             const SMTSortRef &Sort) override;

  SMTExprRef mkBVFromBinImpl(const std::string &Int,
                             const SMTSortRef &Sort) override;

  SMTExprRef mkSymbolImpl(const std::string &Name,
                          const SMTSortRef &Sort) override;

  SMTExprRef mkFPFromBinImpl(const std::string &FP, unsigned EWidth) override;

  SMTExprRef mkRMImpl(const RM &R) override;

  SMTExprRef mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                       const unsigned SigWidth) override;

  SMTExprRef mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                       const unsigned SigWidth) override;

  SMTExprRef mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                              const SMTSortRef &To) override;

  SMTExprRef mkIEEEFPToBVImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkArrayConstImpl(const SMTSortRef &IndexSort,
                              const SMTExprRef &InitValue) override;

  checkResult checkImpl() override;

  void resetImpl() override;

  std::string getSolverNameAndVersion() const override;

  void dumpImpl() override;

  void dumpModelImpl() override;

protected:
  using SymbolTablet = std::unordered_map<std::string, SMTExprRef>;
  SymbolTablet SymbolTable;

}; // end class CVC5Solver

} // namespace camada

#endif
