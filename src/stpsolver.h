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

#ifndef STPSOLVER_H_
#define STPSOLVER_H_

#include "camadafp.h"

#include <unordered_map>

namespace STP {
#include <c_interface.h>
}

namespace camada {

using STPContextRef = std::shared_ptr<STP::VC>;

/// Wrapper for STP Sort
class STPSort : public SolverSort<STPContextRef, STP::Type> {
public:
  using SolverSort<STPContextRef, STP::Type>::SolverSort;
  ~STPSort() override = default;

  void dump() const override;
}; // end class STPSort

class STPExpr : public SolverExpr<STPContextRef, STP::Expr> {
public:
  using SolverExpr<STPContextRef, STP::Expr>::SolverExpr;
  virtual ~STPExpr() = default;

  /// Comparison of Expr equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class STPExpr

class STPSolver : public SMTFPSolver {
public:
  STPContextRef Context;

  unsigned int ConstArrayCounter = 0;

  using SymbolTablet = std::unordered_map<std::string, SMTExprRef>;
  SymbolTablet SymbolTable;

  explicit STPSolver();
  explicit STPSolver(STPContextRef C);
  virtual ~STPSolver();

  void addConstraint(const SMTExprRef &Exp) override;

  SMTExprRef newExprRef(const SMTExpr &Exp) const override;

  SMTSortRef mkBoolSort() override;

  SMTSortRef mkBVSort(unsigned BitWidth) override;

  SMTSortRef mkBVFPSort(const unsigned ExpWidth,
                         const unsigned SigWidth) override;

  SMTSortRef mkBVRMSort() override;

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

  bool getBool(const SMTExprRef &Exp) override;

  std::string getBVInBin(const SMTExprRef &Exp) override;

  SMTExprRef getArrayElement(const SMTExprRef &Array,
                             const SMTExprRef &Index) override;

  SMTExprRef mkBool(const bool b) override;

  SMTExprRef mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) override;

  SMTExprRef mkBVFromBin(const std::string &Int,
                         const SMTSortRef &Sort) override;

  SMTExprRef mkSymbol(const std::string &Name, SMTSortRef Sort) override;

  SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                          const SMTExprRef &InitValue) override;

  checkResult check() override;

  void reset() override;

  void dump() override;

  void dumpModel() override;
}; // end class STPSolver

} // namespace camada

#endif
