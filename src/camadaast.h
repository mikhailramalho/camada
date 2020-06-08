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

#ifndef CAMADAAST_H_
#define CAMADAAST_H_

#include <memory>

#include "camadasort.h"
#include "utils.h"

namespace camada {

/// Generic base class for SMT exprs
class SMTExpr {
public:
  SMTExpr() = default;
  virtual ~SMTExpr() = default;

  friend bool operator==(SMTExpr const &LHS, SMTExpr const &RHS) {
    return LHS.equal_to(RHS);
  }

  virtual void dump() const;

protected:
  /// Query the SMT solver and returns true if two asts are equal (same kind
  /// and bit width). This does not check if the two asts are the same objects.
  virtual bool equal_to(SMTExpr const &other) const = 0;
};

/// Shared pointer for SMTExprs, used by SMTSolver API.
using SMTExprRef = std::shared_ptr<SMTExpr>;

/// Template to hold Solver specific Context and Expr
template <typename SolverContextRef, typename TheExpr>
class SolverExpr : public SMTExpr {
public:
  SolverContextRef Context;

  TheExpr Expr;

  SolverExpr(SolverContextRef C, const TheExpr &SA)
      : Context(std::move(C)), Expr(SA) {}

  virtual ~SolverExpr() = default;

  virtual bool equal_to(SMTExpr const &other) const = 0;
};

} // namespace camada

#endif