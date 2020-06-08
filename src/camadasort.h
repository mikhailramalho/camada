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

/// Template to hold Solver specific Context and Sort
template <typename SolverContextRef, typename TheSort>
class SolverSort : public SMTSort {
public:
  typedef SolverContextRef ContextType;
  typedef TheSort SortType;

  SolverContextRef Context;

  TheSort Sort;

  SolverSort(SolverContextRef C, const TheSort &SS)
      : Context(std::move(C)), Sort(SS) {}

  virtual ~SolverSort() = default;

  virtual bool isBitvectorSortImpl() const {
    abortWithMessage("Unimplemented for current type");
  }

  virtual bool isBooleanSortImpl() const {
    abortWithMessage("Unimplemented for current type");
  }

  virtual bool isFloatSortImpl() const {
    abortWithMessage("Unimplemented for current type");
  }

  virtual bool isRoundingModeSortImpl() const {
    abortWithMessage("Unimplemented for current type");
  }

  virtual unsigned getBitvectorSortSizeImpl() const {
    abortWithMessage("Unimplemented for current type");
  }

  virtual unsigned getFloatSortSizeImpl() const {
    abortWithMessage("Unimplemented for current type");
  }

  virtual bool equal_to(SMTSort const &Other) const = 0;
};

template <typename SolverSortBase> class SolverBVSort : public SolverSortBase {
public:
  unsigned Width;

  SolverBVSort(unsigned W, typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : Width(W), SolverSortBase(C, S){};
  virtual ~SolverBVSort() = default;

  virtual bool isBitvectorSortImpl() const { return true; }

  virtual unsigned getBitvectorSortSizeImpl() const { return Width; }

  virtual bool equal_to(SMTSort const &Other) const {
    return SolverSortBase::equal_to(Other);
  }
};

template <typename SolverSortBase>
class SolverBoolSort : public SolverSortBase {
public:
  SolverBoolSort(typename SolverSortBase::ContextType C,
                 typename SolverSortBase::SortType S)
      : SolverSortBase(C, S){};
  virtual ~SolverBoolSort() = default;

  virtual bool isBooleanSortImpl() const { return true; }

  virtual unsigned getBitvectorSortSizeImpl() const { return 1; }

  virtual bool equal_to(SMTSort const &Other) const {
    return SolverSortBase::equal_to(Other);
  }
};

template <typename SolverSortBase> class SolverFPSort : public SolverSortBase {
public:
  unsigned ExpWidth;
  unsigned SigWidth;

  SolverFPSort(unsigned EW, unsigned SW, typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : ExpWidth(EW), SigWidth(SW), SolverSortBase(C, S){};
  virtual ~SolverFPSort() = default;

  virtual bool isFloatSortImpl() const { return true; }

  virtual unsigned getFloatSortSizeImpl() const { return ExpWidth + SigWidth; }

  virtual bool equal_to(SMTSort const &Other) const {
    return SolverSortBase::equal_to(Other);
  }
};

template <typename SolverSortBase> class SolverRMSort : public SolverSortBase {
public:
  SolverRMSort(typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : SolverSortBase(C, S){};
  virtual ~SolverRMSort() = default;

  virtual bool isRoundingModeSortImpl() const { return true; }

  virtual bool equal_to(SMTSort const &Other) const {
    return SolverSortBase::equal_to(Other);
  }
};

/// Shared pointer for SMTSorts, used by SMTSolver API.
using SMTSortRef = std::shared_ptr<SMTSort>;

/// Wrapper to downcast from SMTSort to Solver specific sort
template <typename SolverSort>
static inline const SolverSort &toSolverSort(const SMTSort &S) {
  return dynamic_cast<const SolverSort &>(S);
}

} // namespace camada

#endif