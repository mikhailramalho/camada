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

#ifndef CAMADAEXPR_H_
#define CAMADAEXPR_H_

#include "camadaerror.h"
#include "camadasort.h"

namespace camada {

class SMTExpr;

enum class SMTExprKind {
  Unknown,
  Symbol,
  BoolConst,
  IntConst,
  RealConst,
  BVConst,
  FPConst,
  RMConst,
  ArrayConst,
  TupleConst,
  BVAdd,
  BVSub,
  BVMul,
  BVSRem,
  BVURem,
  BVSDiv,
  BVUDiv,
  BVShl,
  BVAshr,
  BVLshr,
  BVNeg,
  BVNot,
  BVXor,
  BVOr,
  BVAnd,
  BVXnor,
  BVNor,
  BVNand,
  BVUlt,
  BVSlt,
  BVUgt,
  BVSgt,
  BVUle,
  BVSle,
  BVUge,
  BVSge,
  Not,
  Equal,
  Implies,
  And,
  Or,
  Xor,
  ArithNeg,
  ArithAdd,
  ArithSub,
  ArithMul,
  ArithDiv,
  ArithMod,
  ArithShl,
  ArithLt,
  ArithGt,
  ArithLe,
  ArithGe,
  Int2Real,
  Real2Int,
  IsInt,
  Ite,
  BVSignExt,
  BVZeroExt,
  BVExtract,
  BVConcat,
  BVRedOr,
  BVRedAnd,
  FPAbs,
  FPNeg,
  FPIsInfinite,
  FPIsNaN,
  FPIsDenormal,
  FPIsNormal,
  FPIsZero,
  FPMul,
  FPDiv,
  FPRem,
  FPAdd,
  FPSub,
  FPSqrt,
  FPFMA,
  FPLt,
  FPGt,
  FPLe,
  FPGe,
  FPEqual,
  FPtoFP,
  SBVtoFP,
  UBVtoFP,
  FPtoSBV,
  FPtoUBV,
  FPtoIntegral,
  ArraySelect,
  ArrayStore,
  TupleSelect,
  Apply,
  Forall,
  Exists,
  BVToIEEEFP,
  IEEEFPToBV,
};

/// Diagnostic strings used by the shared handle base for expression handles.
struct SMTExprRefTraits {
  static constexpr const char *nullMessage() {
    return "Dereferencing null expression handle";
  }
  static constexpr const char *movedFromMessage() {
    return "Dereferencing moved-from expression handle";
  }
  static constexpr const char *staleMessage() {
    return "Dereferencing stale expression handle (solver was reset or "
           "destroyed)";
  }
};

/// Public handle for a solver-owned expression.
///
/// The handle is nullable by default and does not own the expression.
/// Dereferencing a null, moved-from, or stale handle aborts through
/// fatalError(). Only solver internals may construct live handles; public code
/// receives them from factory methods such as SMTSolver::mkSymbol().
class SMTExprRef : public SMTRefBase<SMTExpr, SMTExprRefTraits> {
public:
  SMTExprRef() = default;

private:
  /// Inherit the live-handle constructor privately so only friends can call it.
  using SMTRefBase<SMTExpr, SMTExprRefTraits>::SMTRefBase;

  friend class SMTSolver;
  friend class SMTSolverImpl;
};

/// Generic base class for SMT exprs
class SMTExpr {
public:
  SMTSortRef Sort;

  SMTExpr(SMTExprKind K, SMTSortRef S) : Sort(std::move(S)), Kind(K) {}
  explicit SMTExpr(SMTSortRef S)
      : SMTExpr(SMTExprKind::Unknown, std::move(S)) {}
  virtual ~SMTExpr() = default;

  virtual SMTBackendKind getBackendKind() const = 0;

  friend bool operator==(SMTExpr const &LHS, SMTExpr const &RHS) {
    return LHS.equal_to(RHS);
  }

  /// Returns true if the expr sort is bitvector
  bool isBVSort() const { return Sort->isBVSort(); }

  /// Returns true if the expr sort is boolean
  bool isBoolSort() const { return Sort->isBoolSort(); }

  /// Returns true if the expr sort is integer
  bool isIntSort() const { return Sort->isIntSort(); }

  /// Returns true if the expr sort is real
  bool isRealSort() const { return Sort->isRealSort(); }

  /// Returns true if the expr sort is arithmetic
  bool isArithSort() const { return Sort->isArithSort(); }

  /// Returns true if the expr sort is floating-point
  bool isFPSort() const { return Sort->isFPSort(); }

  /// Returns true if the expr sort is rounding mode
  bool isRMSort() const { return Sort->isRMSort(); }

  /// Returns true if the expr sort is array
  bool isArraySort() const { return Sort->isArraySort(); }

  /// Returns true if the expr sort is function
  bool isFunctionSort() const { return Sort->isFunctionSort(); }

  /// Returns this expr's sort width
  unsigned getWidth() const { return Sort->getWidth(); }

  SMTExprKind getKind() const { return Kind; }

  virtual void dump() const;
  virtual void dump(std::string &Out) const;

protected:
  /// Query the SMT solver and returns true if two Exprs are equal (same kind
  /// and bit width). This does not check if the two Exprs are the same objects.
  virtual bool equal_to(SMTExpr const &other) const = 0;

private:
  void setKind(SMTExprKind TheKind) { Kind = TheKind; }

  SMTExprKind Kind = SMTExprKind::Unknown;

  friend class SMTSolverImpl;
};

/// Template to hold Solver specific Context and Expr
template <typename SolverContextRef, typename TheExpr>
class SolverExpr : public SMTExpr {
public:
  using ContextType = SolverContextRef;
  using ExprType = TheExpr;

  SolverContextRef Context;

  TheExpr Expr;

  SolverExpr(SMTExprKind Kind, SolverContextRef C, const SMTSortRef &S,
             const TheExpr &SA)
      : SMTExpr(Kind, S), Context(std::move(C)), Expr(SA) {}

  SolverExpr(SMTExprKind Kind, SolverContextRef C, const SMTSortRef &S,
             TheExpr &&SA)
      : SMTExpr(Kind, S), Context(std::move(C)), Expr(std::move(SA)) {}

  virtual ~SolverExpr() override = default;

  bool equal_to(SMTExpr const &other) const override = 0;
};

/// Wrapper to downcast from SMTExpr to Solver specific expr
template <typename SolverExpr>
static inline const SolverExpr &toSolverExpr(const SMTExpr &S) {
  assert(S.getBackendKind() == SolverExpr::BackendKindValue &&
         "Invalid backend expression cast");
  return static_cast<const SolverExpr &>(S);
}

} // namespace camada

#endif
