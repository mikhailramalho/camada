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

#include "camadaimpl.h"

#include <unordered_map>

extern "C" {
#include <boolector/boolector.h>
}

namespace camada {

using BtorContextRef = std::shared_ptr<Btor *>;

/// Wrapper for Boolector Sort
class BtorSort : public SolverSort<BtorContextRef, BoolectorSort> {
public:
  using SolverSort<BtorContextRef, BoolectorSort>::SolverSort;
  ~BtorSort() override = default;

  unsigned getWidthFromSolver() const override;
}; // end class BtorSort

class BtorExpr : public SolverExpr<BtorContextRef, BoolectorNode *> {
public:
  using SolverExpr<BtorContextRef, BoolectorNode *>::SolverExpr;
  ~BtorExpr() override = default;

  /// Comparison of Expr equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class BtorExpr

class BtorSolver : public SMTSolverImpl {
public:
  BtorContextRef Context;

  using SymbolTablet = std::unordered_map<std::string, SMTExprRef>;
  SymbolTablet SymbolTable;

  explicit BtorSolver();
  virtual ~BtorSolver() override;

  void addConstraintImpl(const SMTExprRef &Exp) override;

  SMTExprRef newExprRefImpl(const SMTExpr &Exp) const override;

  SMTSortRef mkBoolSortImpl() override;

  SMTSortRef mkBVSortImpl(unsigned BitWidth) override;

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

  SMTExprRef mkBVRedOrImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkBVRedAndImpl(const SMTExprRef &Exp) override;

  SMTExprRef mkArraySelectImpl(const SMTExprRef &Array,
                               const SMTExprRef &Index) override;

  SMTExprRef mkArrayStoreImpl(const SMTExprRef &Array, const SMTExprRef &Index,
                              const SMTExprRef &Element) override;

  bool getBoolImpl(const SMTExprRef &Exp) override;

  std::string getBVInBinImpl(const SMTExprRef &Exp) override;

  SMTExprRef getArrayElementImpl(const SMTExprRef &Array,
                                 const SMTExprRef &Index) override;

  SMTExprRef mkBoolImpl(const bool b) override;

  SMTExprRef mkBVFromDecImpl(const int64_t Int,
                             const SMTSortRef &Sort) override;

  SMTExprRef mkBVFromBinImpl(const std::string &Int,
                             const SMTSortRef &Sort) override;

  SMTExprRef mkSymbolImpl(const std::string &Name,
                          const SMTSortRef &Sort) override;

  SMTExprRef mkArrayConstImpl(const SMTSortRef &IndexSort,
                              const SMTExprRef &InitValue) override;

  checkResult checkImpl() override;

  void resetImpl() override;

  std::string getSolverNameAndVersion() const override;

  void dumpImpl() override;

  void dumpModelImpl() override;
}; // end class BtorSolver

} // namespace camada

#endif
