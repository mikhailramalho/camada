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

#ifndef CAMADASORT_H_
#define CAMADASORT_H_

#include <memory>

#include "utils.h"

namespace camada {

/// Generic base class for SMT sorts
class SMTSort {
public:
  SMTSort() = default;
  virtual ~SMTSort() = default;

  /// Returns true if the sort is a bitvector, calls isBitvectorSortImpl().
  virtual bool isBitvectorSort() const { return isBitvectorSortImpl(); }

  /// Returns true if the sort is a boolean, calls isBooleanSortImpl().
  virtual bool isBooleanSort() const { return isBooleanSortImpl(); }

  /// Returns true if the sort is a floating-point, calls isFloatSortImpl().
  virtual bool isFloatSort() const { return isFloatSortImpl(); }

  /// Returns true if the sort is a rounding mode, calls
  /// isRoundingModeSortImpl().
  virtual bool isRoundingModeSort() const { return isRoundingModeSortImpl(); }

  /// Returns the bitvector size, fails if the sort is not a bitvector
  /// Calls getBitvectorSortSizeImpl().
  virtual unsigned getBitvectorSortSize() const {
    abortCondWithMessage(isBitvectorSort(), "Not a bitvector sort!");
    unsigned size = getBitvectorSortSizeImpl();
    abortCondWithMessage(size, "Bitvector size is zero!");
    return size;
  };

  /// Returns the floating-point size, fails if the sort is not a floating-point
  /// Calls getFloatSortSizeImpl().
  virtual unsigned getFloatSortSize() const {
    abortCondWithMessage(isFloatSort(), "Not a floating-point sort!");
    unsigned size = getFloatSortSizeImpl();
    abortCondWithMessage(size, "Floating-point size is zero!");
    return size;
  };

  friend bool operator==(SMTSort const &LHS, SMTSort const &RHS) {
    return LHS.equal_to(RHS);
  }

  virtual void dump() const;

protected:
  /// Query the SMT solver and returns true if two sorts are equal (same kind
  /// and bit width). This does not check if the two sorts are the same objects.
  virtual bool equal_to(SMTSort const &other) const = 0;

  /// Query the SMT solver and checks if a sort is bitvector.
  virtual bool isBitvectorSortImpl() const = 0;

  /// Query the SMT solver and checks if a sort is boolean.
  virtual bool isBooleanSortImpl() const = 0;

  /// Query the SMT solver and checks if a sort is floating-point.
  virtual bool isFloatSortImpl() const = 0;

  /// Query the SMT solver and checks if a sort is rounding mode.
  virtual bool isRoundingModeSortImpl() const = 0;

  /// Query the SMT solver and returns the sort bit width.
  virtual unsigned getBitvectorSortSizeImpl() const = 0;

  /// Query the SMT solver and returns the sort bit width.
  virtual unsigned getFloatSortSizeImpl() const = 0;
};

/// Shared pointer for SMTSorts, used by SMTSolver API.
using SMTSortRef = std::shared_ptr<SMTSort>;

template <typename SolverContextRef, typename TheSort>
class SolverSort : public SMTSort {
public:
  SolverContextRef Context;

  TheSort Sort;

  SolverSort(SolverContextRef C, const TheSort &SS)
      : Context(std::move(C)), Sort(SS) {}

  virtual ~SolverSort() = default;

  virtual bool isBitvectorSortImpl() const = 0;

  virtual bool isBooleanSortImpl() const = 0;

  virtual bool isFloatSortImpl() const = 0;

  virtual bool isRoundingModeSortImpl() const = 0;

  virtual unsigned getBitvectorSortSizeImpl() const = 0;

  virtual unsigned getFloatSortSizeImpl() const = 0;

  virtual bool equal_to(SMTSort const &Other) const = 0;
};

} // namespace camada

#endif