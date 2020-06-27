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

#ifndef Z3SOLVER_H_
#define Z3SOLVER_H_

#include "camadafp.h"

#include <z3++.h>

namespace camada {

using Z3ContextRef = std::shared_ptr<z3::context>;

/// Wrapper for Z3 Sort
class Z3Sort : public SolverSort<Z3ContextRef, z3::sort> {
public:
  using SolverSort<Z3ContextRef, z3::sort>::SolverSort;
  virtual ~Z3Sort() = default;

  void dump() const override;
}; // end class Z3Sort

class Z3Expr : public SolverExpr<Z3ContextRef, z3::expr> {
public:
  using SolverExpr<Z3ContextRef, z3::expr>::SolverExpr;
  virtual ~Z3Expr() = default;

  /// Comparison of Expr equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class Z3Expr

class Z3Solver : public SMTFPSolver {
public:
  Z3ContextRef Context;

  z3::solver Solver;

  explicit Z3Solver();
  explicit Z3Solver(Z3ContextRef C, const z3::solver &S);
  virtual ~Z3Solver() = default;

  void addConstraint(const SMTExprRef &Exp) override;

  SMTExprRef newExprRef(const SMTExpr &Exp) const override;

  SMTSortRef getBoolSort() override;

  SMTSortRef getBVSort(unsigned BitWidth) override;

  SMTSortRef getRMSort() override;

  SMTSortRef getFPSort(const unsigned ExpWidth,
                       const unsigned SigWidth) override;

  SMTSortRef getBVFPSort(const unsigned ExpWidth,
                         const unsigned SigWidth) override;

  SMTSortRef getBVRMSort() override;

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

  SMTExprRef mkFPAbs(const SMTExprRef &Exp) override;

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override;

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) override;

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) override;

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) override;

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RM &R) override;

  SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const RM &R) override;

  SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                     const SMTExprRef &Z, const RM &R) override;

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                      const RM &R) override;

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RM &R) override;

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RM &R) override;

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) override;

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) override;

  SMTExprRef mkFPtoIntegral(const SMTExprRef &From, RM R) override;

  bool getBool(const SMTExprRef &Exp) override;

  int64_t getBV(const SMTExprRef &Exp) override;

  float getFP32(const SMTExprRef &Exp) override;

  double getFP64(const SMTExprRef &Exp) override;

  SMTExprRef mkBool(const bool b) override;

  SMTExprRef mkBV(const int64_t Int, const SMTSortRef &Sort) override;

  SMTExprRef mkSymbol(const char *Name, SMTSortRef Sort) override;

  SMTExprRef mkFP32(const float Float) override;

  SMTExprRef mkFP64(const double Double) override;

  SMTExprRef mkRM(const RM &R) override;

  SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) override;

  SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) override;

  SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp, const SMTSortRef &To) override;

  SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) override;

  checkResult check() override;

  void reset() override;

  void dump() override;

  void dumpModel() override;
}; // end class Z3Solver

} // namespace camada

#endif
