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
    auto locked = State.lock();
    return Ptr != nullptr && locked && locked->Generation == Generation;
  }

private:
  const SMTExpr *Ptr = nullptr;
  std::weak_ptr<const SMTHandleState> State;
  uint64_t Generation = 0;

  SMTExprRef(const SMTExpr *ThePtr,
             std::weak_ptr<const SMTHandleState> TheState,
             uint64_t TheGeneration)
      : Ptr(ThePtr), State(std::move(TheState)), Generation(TheGeneration) {}

  void validate() const {
    auto locked = State.lock();
    assert(Ptr && "Dereferencing null expression handle");
    assert(locked &&
           "Dereferencing expression handle after solver destruction");
    assert(locked->Generation == Generation &&
           "Dereferencing stale expression handle after solver reset");
  }

  friend class SMTSolver;
};

/// Generic base class for SMT exprs
class SMTExpr {
public:
  SMTSortRef Sort;

  explicit SMTExpr(SMTSortRef S) : Sort(std::move(S)) {}
  virtual ~SMTExpr() = default;

  friend bool operator==(SMTExpr const &LHS, SMTExpr const &RHS) {
    return LHS.equal_to(RHS);
  }

  /// Returns true if the expr sort is bitvector
  virtual bool isBVSort() const = 0;

  /// Returns true if the expr sort is boolean
  virtual bool isBoolSort() const = 0;

  /// Returns true if the expr sort is floating-point
  virtual bool isFPSort() const = 0;

  /// Returns true if the expr sort is rounding mode
  virtual bool isRMSort() const = 0;

  /// Returns true if the expr sort is array
  virtual bool isArraySort() const = 0;

  /// Returns this expr's sort width
  unsigned getWidth() const { return Sort->getWidth(); }

  virtual void dump() const;

protected:
  /// Query the SMT solver and returns true if two Exprs are equal (same kind
  /// and bit width). This does not check if the two Exprs are the same objects.
  virtual bool equal_to(SMTExpr const &other) const = 0;
};

/// Template to hold Solver specific Context and Expr
template <typename SolverContextRef, typename TheExpr>
class SolverExpr : public SMTExpr {
public:
  using ContextType = SolverContextRef;
  using ExprType = TheExpr;

  SolverContextRef Context;

  TheExpr Expr;

  SolverExpr(SolverContextRef C, const SMTSortRef &S, const TheExpr &SA)
      : SMTExpr(S), Context(std::move(C)), Expr(SA) {}

  virtual ~SolverExpr() override = default;

  bool isBVSort() const override { return Sort->isBVSort(); }

  bool isBoolSort() const override { return Sort->isBoolSort(); }

  bool isFPSort() const override { return Sort->isFPSort(); }

  bool isRMSort() const override { return Sort->isRMSort(); }

  bool isArraySort() const override { return Sort->isArraySort(); }

  bool equal_to(SMTExpr const &other) const override = 0;
};

/// Wrapper to downcast from SMTExpr to Solver specific expr
template <typename SolverExpr>
static inline const SolverExpr &toSolverExpr(const SMTExpr &S) {
  return dynamic_cast<const SolverExpr &>(S);
}

} // namespace camada

#endif
