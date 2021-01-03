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

class SMTSort;

/// Shared pointer for SMTSorts, used by SMTSolver API.
using SMTSortRef = std::shared_ptr<SMTSort>;

/// Generic base class for SMT sorts
class SMTSort {
public:
  SMTSort() = default;
  virtual ~SMTSort() = default;

  /// Returns true if the sort is a bitvector.
  virtual bool isBVSort() const { return false; }

  /// Returns true if the sort is a boolean.
  virtual bool isBoolSort() const { return false; }

  /// Returns true if the sort is a floating-point.
  virtual bool isFPSort() const { return false; }

  /// Returns true if the sort is a rounding mode.
  virtual bool isRMSort() const { return false; }

  /// Returns true if the sort is an array.
  virtual bool isArraySort() const { return false; }

  /// Returns the sort width.
  virtual unsigned getWidth() const;

  /// Returns the sort width from the Solver.
  virtual unsigned getWidthFromSolver() const;

  /// Returns the floating-point significand width, fails if the sort is not a
  /// floating-point.
  virtual unsigned getFPSignificandWidth() const;

  /// Returns the floating-point exponent width, fails if the sort is not a
  /// floating-point.
  virtual unsigned getFPExponentWidth() const;

  /// Returns the array's index sort, fails if the sort is not an array.
  virtual SMTSortRef getIndexSort() const;

  /// Returns the array's element sort, fails if the sort is not an array.
  virtual SMTSortRef getElementSort() const;

  /// Returns true if two sorts are equal (same kind and bit width). This does
  /// not check if the two sorts are the same objects.
  bool operator==(SMTSort const &Other);

  virtual void dump() const;
};

inline bool operator==(SMTSortRef const &LHS, SMTSortRef const &RHS) {
  return (*LHS.get() == *RHS.get());
}

/// Template to hold Solver specific Context and Sort
template <typename SolverContextRef, typename TheSort>
class SolverSort : public SMTSort {
public:
  using ContextType = SolverContextRef;
  using SortType = TheSort;

  SolverContextRef Context;

  TheSort Sort;

  SolverSort(SolverContextRef C, const TheSort &SS)
      : Context(std::move(C)), Sort(SS) {}

  ~SolverSort() override = default;
};

template <typename SolverSortBase> class SolverBVSort : public SolverSortBase {
public:
  unsigned Width;

  SolverBVSort(unsigned W, typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : SolverSortBase(C, S), Width(W) {}
  ~SolverBVSort() override = default;

  bool isBVSort() const override { return true; }

  unsigned getWidth() const override { return Width; }
};

template <typename SolverSortBase>
class SolverBoolSort : public SolverSortBase {
public:
  SolverBoolSort(typename SolverSortBase::ContextType C,
                 typename SolverSortBase::SortType S)
      : SolverSortBase(C, S) {}
  ~SolverBoolSort() override = default;

  bool isBoolSort() const override { return true; }

  unsigned getWidth() const override { return 1; }
};

template <typename SolverSortBase> class SolverFPSort : public SolverSortBase {
public:
  unsigned ExpWidth;
  unsigned SigWidth;

  SolverFPSort(unsigned EW, unsigned SW, typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : SolverSortBase(C, S), ExpWidth(EW), SigWidth(SW) {}
  ~SolverFPSort() override = default;

  bool isFPSort() const override { return true; }

  unsigned getWidth() const override { return 1 + ExpWidth + SigWidth; }

  unsigned getFPSignificandWidth() const override { return SigWidth; }

  unsigned getFPExponentWidth() const override { return ExpWidth; }
};

template <typename SolverSortBase> class SolverRMSort : public SolverSortBase {
public:
  SolverRMSort(typename SolverSortBase::ContextType C,
               typename SolverSortBase::SortType S)
      : SolverSortBase(C, S) {}
  ~SolverRMSort() override = default;

  unsigned getWidth() const override { return 3; }

  bool isRMSort() const override { return true; }
};

template <typename SolverSortBase>
class SolverArraySort : public SolverSortBase {
public:
  SMTSortRef IndexSort;
  SMTSortRef ElementSort;

  SolverArraySort(SMTSortRef I, SMTSortRef E,
                  typename SolverSortBase::ContextType C,
                  typename SolverSortBase::SortType S)
      : SolverSortBase(C, S), IndexSort(std::move(I)),
        ElementSort(std::move(E)) {}
  ~SolverArraySort() override = default;

  bool isArraySort() const override { return true; }

  SMTSortRef getIndexSort() const override { return IndexSort; }

  SMTSortRef getElementSort() const override { return ElementSort; }
};

/// Wrapper to downcast from SMTSort to Solver specific sort
template <typename SolverSort>
static inline const SolverSort &toSolverSort(const SMTSort &S) {
  return dynamic_cast<const SolverSort &>(S);
}

} // namespace camada

#endif