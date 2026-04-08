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

#ifndef MATHSATSOLVER_H_
#define MATHSATSOLVER_H_

#include "camadaimpl.h"

#include <mathsat.h>
#include <variant>

namespace camada {

using MathSATContextRef = msat_env *;
using MathSATNode = std::variant<msat_term, msat_decl>;

/// Wrapper for MathSAT Sort
class MathSATSort : public SolverSort<MathSATContextRef, msat_type> {
public:
  static constexpr SMTBackendKind BackendKindValue = SMTBackendKind::MathSAT;
  using SolverSort<MathSATContextRef, msat_type>::SolverSort;
  ~MathSATSort() override = default;

  SMTBackendKind getBackendKind() const override { return BackendKindValue; }

  unsigned getWidthFromSolver() const override;

  void dump() const override;
  void dump(std::string &Out) const override;
}; // end class MathSATSort

class MathSATExpr : public SolverExpr<MathSATContextRef, MathSATNode> {
public:
  static constexpr SMTBackendKind BackendKindValue = SMTBackendKind::MathSAT;
  using SolverExpr<MathSATContextRef, MathSATNode>::SolverExpr;
  MathSATExpr(SMTExprKind Kind, MathSATContextRef C, const SMTSortRef &S,
              const msat_term &T)
      : SolverExpr<MathSATContextRef, MathSATNode>(Kind, C, S, MathSATNode(T)) {
  }
  MathSATExpr(SMTExprKind Kind, MathSATContextRef C, const SMTSortRef &S,
              const msat_decl &D)
      : SolverExpr<MathSATContextRef, MathSATNode>(Kind, C, S, MathSATNode(D)) {
  }
  ~MathSATExpr() override = default;

  SMTBackendKind getBackendKind() const override { return BackendKindValue; }

  /// Comparison of Expr equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
  void dump(std::string &Out) const override;

  bool isDecl() const { return std::holds_alternative<msat_decl>(Expr); }
  bool isTerm() const { return std::holds_alternative<msat_term>(Expr); }
  const msat_decl &getDecl() const {
    assert(isDecl() && "Expected MathSAT declaration");
    return std::get<msat_decl>(Expr);
  }
  const msat_term &getTerm() const {
    assert(isTerm() && "Expected MathSAT term");
    return std::get<msat_term>(Expr);
  }
}; // end class MathSATExpr

class MathSATSolver : public SMTSolverImpl {
public:
  MathSATSolver();

  /// Create MathSAT custom configuration. User is responsible for freeing
  /// Config
  explicit MathSATSolver(const msat_config &Config);
  ~MathSATSolver() override;

protected:
  msat_env context() const { return Context; }

  void addConstraintImpl(const SMTExprRef &Exp) override;

  SMTExprRef newExprRefImpl(const SMTExpr &Exp) const override;
  SMTExprRef rewrapExprImpl(const SMTExpr &Exp, const SMTSortRef &Sort,
                            SMTExprKind Kind) const override;

  SMTSortRef mkBoolSortImpl() override;
  SMTSortRef mkIntSortImpl() override;
  SMTSortRef mkRealSortImpl() override;

  SMTSortRef mkBVSortImpl(unsigned BitWidth) override;

  SMTSortRef mkRMSortImpl() override;

  SMTSortRef mkFPSortImpl(const unsigned ExpWidth,
                          const unsigned SigWidth) override;

  SMTSortRef mkBVFPSortImpl(const unsigned ExpWidth,
                            const unsigned SigWidth) override;

  SMTSortRef mkBVRMSortImpl() override;

  SMTSortRef mkArraySortImpl(const SMTSortRef &IndexSort,
                             const SMTSortRef &ElemSort) override;

  SMTSortRef mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                                const SMTSortRef &CodomainSort) override;

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

  SMTExprRef mkBVUltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVUleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkBVSleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkArithNegImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkArithAddImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithSubImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithMulImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithDivImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithModImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithShlImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithLtImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkArithGtImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkArithLeImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkArithGeImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkInt2RealImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkReal2IntImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkIsIntImpl(const SMTExprRef &Exp) override;

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
  SMTExprRef mkApplyImpl(const SMTExprRef &Function,
                         const std::vector<SMTExprRef> &Args) override;
  SMTExprRef mkForallImpl(const std::vector<SMTExprRef> &Vars,
                          const SMTExprRef &Body) override;
  SMTExprRef mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                          const SMTExprRef &Body) override;

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

  SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

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

  std::string getIntImpl(const SMTExprRef &Exp) override;

  void getRationalImpl(const SMTExprRef &Exp, std::string &Num,
                       std::string &Den) override;

  std::string getFPInBinImpl(const SMTExprRef &Exp) override;

  SMTExprRef getArrayElementImpl(const SMTExprRef &Array,
                                 const SMTExprRef &Index) override;

  SMTExprRef mkBoolImpl(const bool b) override;
  SMTExprRef mkIntImpl(int64_t v) override;
  SMTExprRef mkIntImpl(const std::string &v) override;
  SMTExprRef mkRealImpl(const std::string &v) override;
  SMTExprRef mkRealImpl(int64_t v) override;
  SMTExprRef mkRealImpl(int64_t num, int64_t den) override;

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
  void pushImpl(unsigned nscopes) override;
  void popImpl(unsigned nscopes) override;

  std::string getSolverNameAndVersion() const override;

  void dumpImpl() override;
  void dumpImpl(std::string &Out) override;

  void dumpModelImpl() override;
  void dumpModelImpl(std::string &Out) override;

private:
  msat_env Context{};
}; // end class MathSATSolver

} // namespace camada

#endif
