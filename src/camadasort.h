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

namespace camada {

/// Generic base class for SMT sorts
class SMTSort {
public:
  SMTSort() = default;
  virtual ~SMTSort() = default;

  /// Returns true if the sort is a bitvector.
  virtual bool isBitvectorSort() const;

  /// Returns true if the sort is a boolean.
  virtual bool isBooleanSort() const;

  /// Returns true if the sort is a floating-point.
  virtual bool isFloatSort() const;

  /// Returns true if the sort is a rounding mode.
  virtual bool isRoundingModeSort() const;

  /// Returns the bitvector size, fails if the sort is not a bitvector or if the
  /// size is zero. Calls getBitvectorSortSizeImpl().
  virtual unsigned getBitvectorSortSize() const;

  /// Returns the floating-point size, fails if the sort is not a floating-point
  /// floating-point or if the size is zero. Calls getFloatSortSizeImpl().
  virtual unsigned getFloatSortSize() const;

  /// Returns the floating-point significand size, fails if the sort is not a
  /// floating-point or if the size is zero. Calls
  /// getFloatSignificandSizeImpl().
  virtual unsigned getFloatSignificandSize() const;

  /// Returns the floating-point exponent size, fails if the sort is not a
  /// floating-point or if the size is zero. Calls getFloatExponentSizeImpl().
  virtual unsigned getFloatExponentSize() const;

  /// Returns true if two sorts are equal (same kind and bit width). This does
  /// not check if the two sorts are the same objects.
  friend bool operator==(SMTSort const &LHS, SMTSort const &RHS);

  virtual void dump() const;

protected:
  /// Returns the bitvector sort bit width.
  virtual unsigned getBitvectorSortSizeImpl() const;

  /// Returns the floating-point sort bit width.
  virtual unsigned getFloatSortSizeImpl() const;

  /// Returns the floating-point sort significand bit width.
  virtual unsigned getFloatSignificandSizeImpl() const;

  /// Returns the floating-point sort exponent bit width.
  virtual unsigned getFloatExponentSizeImpl() const;
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
};

template <typename SolverSortBase> class SolverBVSort : public SolverSortBase {
public:
  unsigned Width;

  SolverBVSort(unsigned W, typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : SolverSortBase(C, S), Width(W) {}
  virtual ~SolverBVSort() = default;

  virtual bool isBitvectorSort() const { return true; }

  virtual unsigned getBitvectorSortSize() const { return Width; }
};

template <typename SolverSortBase>
class SolverBoolSort : public SolverSortBase {
public:
  SolverBoolSort(typename SolverSortBase::ContextType C,
                 typename SolverSortBase::SortType S)
      : SolverSortBase(C, S) {}
  virtual ~SolverBoolSort() = default;

  virtual bool isBooleanSort() const { return true; }

  virtual unsigned getBitvectorSortSize() const { return 1; }
};

template <typename SolverSortBase> class SolverFPSort : public SolverSortBase {
public:
  unsigned ExpWidth;
  unsigned SigWidth;

  SolverFPSort(unsigned EW, unsigned SW, typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : SolverSortBase(C, S), ExpWidth(EW), SigWidth(SW) {}
  virtual ~SolverFPSort() = default;

  virtual bool isFloatSort() const { return true; }

  virtual unsigned getFloatSortSize() const { return ExpWidth + SigWidth; }

  virtual unsigned getFloatSignificandSize() const { return SigWidth; }

  virtual unsigned getFloatExponentSize() const { return ExpWidth; }
};

template <typename SolverSortBase> class SolverRMSort : public SolverSortBase {
public:
  SolverRMSort(typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : SolverSortBase(C, S) {}
  virtual ~SolverRMSort() = default;

  virtual bool isRoundingModeSort() const { return true; }
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