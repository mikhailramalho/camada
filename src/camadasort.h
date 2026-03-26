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

#include <cassert>
#include <cstdint>
#include <memory>

namespace camada {

enum class SMTBackendKind { Bitwuzla, CVC5, MathSAT, STP, Yices, Z3 };
enum class SMTSortKind { Bool, BV, FP, RM, BVFP, BVRM, Array };

class SMTSort;
struct SMTHandleState {
  uint64_t Generation = 1;
};

class SMTSortRef {
public:
  SMTSortRef() = default;

  const SMTSort *get() const {
    validate();
    return Ptr;
  }

  const SMTSort &operator*() const { return *get(); }

  const SMTSort *operator->() const { return get(); }

  explicit operator bool() const { return isValid(); }

  bool isValid() const {
    return Ptr != nullptr && State && State->Generation == Generation;
  }

private:
  const SMTSort *Ptr = nullptr;
  std::shared_ptr<const SMTHandleState> State;
  uint64_t Generation = 0;

  SMTSortRef(const SMTSort *ThePtr,
             std::shared_ptr<const SMTHandleState> TheState,
             uint64_t TheGeneration)
      : Ptr(ThePtr), State(std::move(TheState)), Generation(TheGeneration) {}

  void validate() const {
    assert(Ptr && "Dereferencing null sort handle");
    assert(State && "Dereferencing sort handle after solver destruction");
    assert(State->Generation == Generation &&
           "Dereferencing stale sort handle after solver reset");
  }

  friend class SMTSolver;
};

/// Generic base class for SMT sorts
class SMTSort {
public:
  explicit SMTSort(SMTSortKind K, unsigned W = 0, unsigned EW = 0,
                   unsigned SW = 0, SMTSortRef I = {}, SMTSortRef E = {})
      : Kind(K), Width(W), ExpWidth(EW), SigWidth(SW), IndexSort(std::move(I)),
        ElementSort(std::move(E)) {}
  virtual ~SMTSort() = default;

  virtual SMTBackendKind getBackendKind() const = 0;

  SMTSortKind getSortKind() const { return Kind; }

  /// Returns true if the sort is a bitvector.
  bool isBVSort() const {
    return Kind == SMTSortKind::BV || Kind == SMTSortKind::BVFP ||
           Kind == SMTSortKind::BVRM;
  }

  /// Returns true if the sort is a boolean.
  bool isBoolSort() const { return Kind == SMTSortKind::Bool; }

  /// Returns true if the sort is a floating-point.
  bool isFPSort() const {
    return Kind == SMTSortKind::FP || Kind == SMTSortKind::BVFP;
  }

  /// Returns true if the sort is a rounding mode.
  bool isRMSort() const {
    return Kind == SMTSortKind::RM || Kind == SMTSortKind::BVRM;
  }

  /// Returns true if the sort is an array.
  bool isArraySort() const { return Kind == SMTSortKind::Array; }

  /// Returns the sort width.
  unsigned getWidth() const;

  /// Returns the sort width from the Solver.
  virtual unsigned getWidthFromSolver() const;

  /// Returns the floating-point significand width, fails if the sort is not a
  /// floating-point.
  unsigned getFPSignificandWidth() const;

  /// Returns the floating-point exponent width, fails if the sort is not a
  /// floating-point.
  unsigned getFPExponentWidth() const;

  /// Returns the array's index sort, fails if the sort is not an array.
  SMTSortRef getIndexSort() const;

  /// Returns the array's element sort, fails if the sort is not an array.
  SMTSortRef getElementSort() const;

  /// Returns true if two sorts are equal (same kind and bit width). This does
  /// not check if the two sorts are the same objects.
  bool operator==(SMTSort const &Other) const;

  /// Returns whether the solver width matches our internal representation.
  bool validateSortWidth() const;

#ifndef NDEBUG
  bool isWidthValidated() const { return WidthValidated; }
  void markWidthValidated() { WidthValidated = true; }
#endif

  virtual void dump() const;

protected:
  SMTSortKind Kind;
  unsigned Width = 0;
  unsigned ExpWidth = 0;
  unsigned SigWidth = 0;
  SMTSortRef IndexSort;
  SMTSortRef ElementSort;
#ifndef NDEBUG
  bool WidthValidated = false;
#endif
};

inline bool operator==(SMTSortRef const &LHS, SMTSortRef const &RHS) {
  return (*LHS == *RHS);
}

inline bool operator!=(SMTSortRef const &LHS, SMTSortRef const &RHS) {
  return !(LHS == RHS);
}

/// Template to hold Solver specific Context and Sort
template <typename SolverContextRef, typename TheSort>
class SolverSort : public SMTSort {
public:
  using ContextType = SolverContextRef;
  using SortType = TheSort;

  SolverContextRef Context;

  TheSort Sort;

  SolverSort(SMTSortKind K, SolverContextRef C, const TheSort &SS,
             unsigned W = 0, unsigned EW = 0, unsigned SW = 0,
             SMTSortRef I = {}, SMTSortRef E = {})
      : SMTSort(K, W, EW, SW, std::move(I), std::move(E)),
        Context(std::move(C)), Sort(SS) {}

  virtual ~SolverSort() override = default;
};

/// Wrapper to downcast from SMTSort to Solver specific sort
template <typename SolverSort>
static inline const SolverSort &toSolverSort(const SMTSort &S) {
  assert(S.getBackendKind() == SolverSort::BackendKindValue &&
         "Invalid backend sort cast");
  return static_cast<const SolverSort &>(S);
}

} // namespace camada

#endif
