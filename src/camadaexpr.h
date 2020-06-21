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

#include <memory>

#include "camadasort.h"

namespace camada {

/// Generic base class for SMT exprs
class SMTExpr {
public:
  SMTSortRef Sort;

  SMTExpr(SMTSortRef S) : Sort(std::move(S)) {}
  virtual ~SMTExpr() = default;

  friend bool operator==(SMTExpr const &LHS, SMTExpr const &RHS) {
    return LHS.equal_to(RHS);
  }

  /// Returns true if the expr sort is bitvector
  virtual bool isBitvectorSort() const = 0;

  /// Returns true if the expr sort is boolean
  virtual bool isBooleanSort() const = 0;

  /// Returns true if the expr sort is floating-point
  virtual bool isFloatSort() const = 0;

  /// Returns true if the expr sort is rounding mode
  virtual bool isRoundingModeSort() = 0;

  /// Returns this expr's sort width
  unsigned getWidth() { return Sort->getWidth(); }

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
  typedef SolverContextRef ContextType;
  typedef TheExpr ExprType;

  SolverContextRef Context;

  TheExpr Expr;

  SolverExpr(SolverContextRef C, const SMTSortRef &S, const TheExpr &SA)
      : SMTExpr(S), Context(std::move(C)), Expr(SA) {}

  virtual ~SolverExpr() = default;

  virtual bool isBitvectorSort() const { return Sort->isBitvectorSort(); }

  virtual bool isBooleanSort() const { return Sort->isBooleanSort(); }

  virtual bool isFloatSort() const { return Sort->isFloatSort(); }

  virtual bool isRoundingModeSort() { return Sort->isRoundingModeSort(); }

  virtual bool equal_to(SMTExpr const &other) const = 0;
};

/// Shared pointer for SMTExprs, used by SMTSolver API.
using SMTExprRef = std::shared_ptr<SMTExpr>;

/// Wrapper to downcast from SMTExpr to Solver specific expr
template <typename SolverExpr>
static inline const SolverExpr &toSolverExpr(const SMTExpr &S) {
  return dynamic_cast<const SolverExpr &>(S);
}

} // namespace camada

#endif