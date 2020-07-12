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

#ifndef YICESSOLVER_H_
#define YICESSOLVER_H_

#include "camadafp.h"

#include <unordered_map>
#include <vector>
#include <yices.h>

namespace camada {

/// Wrapper for Boolector context
class YicesContext {
public:
  context_t *Context;

  YicesContext();
  virtual ~YicesContext();

  virtual void createAndConfig();
  void reset();
}; // end class YicesContext

using YicesContextRef = std::shared_ptr<YicesContext>;

/// Wrapper for Yices Sort
class YicesSort : public SolverSort<YicesContextRef, type_t> {
public:
  using SolverSort<YicesContextRef, type_t>::SolverSort;
  virtual ~YicesSort() = default;

  void dump() const override;
}; // end class YicesSort

class YicesExpr : public SolverExpr<YicesContextRef, term_t> {
public:
  using SolverExpr<YicesContextRef, term_t>::SolverExpr;
  virtual ~YicesExpr() = default;

  /// Comparison of Expr equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class YicesExpr

class YicesSolver : public SMTFPSolver {
public:
  YicesContextRef Context;

  unsigned int ConstArrayCounter = 0;

  explicit YicesSolver();
  explicit YicesSolver(YicesContextRef C);
  virtual ~YicesSolver() = default;

  void addConstraint(const SMTExprRef &Exp) override;

  SMTExprRef newExprRef(const SMTExpr &Exp) const override;

  SMTSortRef getBoolSort() override;

  SMTSortRef getBVSort(unsigned BitWidth) override;

  SMTSortRef getBVFPSort(const unsigned ExpWidth,
                         const unsigned SigWidth) override;

  SMTSortRef getBVRMSort() override;

  SMTSortRef getArraySort(const SMTSortRef &IndexType,
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

protected:
  using SymbolTablet = std::unordered_map<std::string, SMTExprRef>;
  SymbolTablet SymbolTable;

  using TermVectort = std::vector<SMTExprRef>;
  TermVectort Assertions;

}; // end class YicesSolver

} // namespace camada

#endif
