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

#include "camadasort.h"

namespace camada {

class SMTExpr;
class SMTSolverImpl;

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
  Apply,
  Forall,
  Exists,
  BVToIEEEFP,
  IEEEFPToBV,
};

class SMTExprRef {
public:
  SMTExprRef() = default;

  const SMTExpr *get() const {
    validate();
    return Ptr;
  }

  const SMTExpr &operator*() const { return *get(); }

  const SMTExpr *operator->() const { return get(); }

  explicit operator bool() const { return isValid(); }

  bool isValid() const {
    return Ptr != nullptr && State && State->Generation == Generation;
  }

private:
  const SMTExpr *Ptr = nullptr;
  std::shared_ptr<const SMTHandleState> State;
  uint64_t Generation = 0;

  SMTExprRef(const SMTExpr *ThePtr,
             std::shared_ptr<const SMTHandleState> TheState,
             uint64_t TheGeneration)
      : Ptr(ThePtr), State(std::move(TheState)), Generation(TheGeneration) {}

  void validate() const {
    assert(Ptr && "Dereferencing null expression handle");
    assert(State && "Dereferencing expression handle after solver destruction");
    assert(State->Generation == Generation &&
           "Dereferencing stale expression handle after solver reset");
  }

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
  virtual bool isBVSort() const = 0;

  /// Returns true if the expr sort is boolean
  virtual bool isBoolSort() const = 0;

  /// Returns true if the expr sort is integer
  virtual bool isIntSort() const = 0;

  /// Returns true if the expr sort is real
  virtual bool isRealSort() const = 0;

  /// Returns true if the expr sort is arithmetic
  virtual bool isArithSort() const = 0;

  /// Returns true if the expr sort is floating-point
  virtual bool isFPSort() const = 0;

  /// Returns true if the expr sort is rounding mode
  virtual bool isRMSort() const = 0;

  /// Returns true if the expr sort is array
  virtual bool isArraySort() const = 0;

  /// Returns true if the expr sort is function
  virtual bool isFunctionSort() const = 0;

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

  virtual ~SolverExpr() override = default;

  bool isBVSort() const override { return Sort->isBVSort(); }

  bool isBoolSort() const override { return Sort->isBoolSort(); }

  bool isIntSort() const override { return Sort->isIntSort(); }

  bool isRealSort() const override { return Sort->isRealSort(); }

  bool isArithSort() const override { return Sort->isArithSort(); }

  bool isFPSort() const override { return Sort->isFPSort(); }

  bool isRMSort() const override { return Sort->isRMSort(); }

  bool isArraySort() const override { return Sort->isArraySort(); }

  bool isFunctionSort() const override { return Sort->isFunctionSort(); }

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
