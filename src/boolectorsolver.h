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

#ifndef BOOLECTORSOLVER_H_
#define BOOLECTORSOLVER_H_

#include "camadafp.h"

#include <unordered_map>

extern "C" {
#include <boolector/boolector.h>
}

namespace camada {

/// Wrapper for Boolector context
class BtorContext {
public:
  Btor *Context;

  BtorContext();
  virtual ~BtorContext();

  virtual void createAndConfig();
  void reset();
}; // end class BtorContext

using BtorContextRef = std::shared_ptr<BtorContext>;

/// No need for a wrapper for Boolector Sort
using BtorSort = SolverSort<BtorContextRef, BoolectorSort>;

class BtorExpr : public SolverExpr<BtorContextRef, BoolectorNode *> {
public:
  using SolverExpr<BtorContextRef, BoolectorNode *>::SolverExpr;
  ~BtorExpr() override = default;

  /// Comparison of Expr equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class BtorExpr

class BtorSolver : public SMTFPSolver {
public:
  BtorContextRef Context;

  using SymbolTablet = std::unordered_map<std::string, SMTExprRef>;
  SymbolTablet SymbolTable;

  explicit BtorSolver();
  explicit BtorSolver(BtorContextRef C);
  ~BtorSolver() override = default;

  void addConstraint(const SMTExprRef &Exp) override;

  SMTExprRef newExprRef(const SMTExpr &Exp) const override;

  SMTSortRef mkBoolSort() override;

  SMTSortRef mkBVSort(unsigned BitWidth) override;

  SMTSortRef getBVFPSort(const unsigned ExpWidth,
                         const unsigned SigWidth) override;

  SMTSortRef getBVRMSort() override;

  SMTSortRef mkArraySort(const SMTSortRef &IndexSort,
                         const SMTSortRef &ElemSort) override;

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
}; // end class BtorSolver

} // namespace camada

#endif
