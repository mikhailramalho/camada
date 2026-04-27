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
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "camadahandle.h"

namespace camada {

enum class SMTBackendKind { Bitwuzla, CVC5, MathSAT, STP, Yices, Z3 };
enum class SMTSortKind {
  Bool,
  Int,
  Real,
  BV,
  FP,
  RM,
  BVFP,
  BVRM,
  Array,
  Function,
  Tuple
};

class SMTSort;

/// Diagnostic strings used by the shared handle base for sort handles.
struct SMTSortRefTraits {
  static constexpr const char *nullMessage() {
    return "Dereferencing null sort handle";
  }
  static constexpr const char *movedFromMessage() {
    return "Dereferencing moved-from sort handle";
  }
  static constexpr const char *staleMessage() {
    return "Dereferencing stale sort handle (solver was reset or destroyed)";
  }
};

/// Public handle for a solver-owned sort.
///
/// The handle is nullable by default and does not own the sort. Dereferencing a
/// null, moved-from, or stale handle aborts through fatalError(). Only solver
/// internals may construct live handles; public code receives them from factory
/// methods such as SMTSolver::mkBVSort().
class SMTSortRef : public SMTRefBase<SMTSort, SMTSortRefTraits> {
public:
  SMTSortRef() = default;

private:
  /// Inherit the live-handle constructor privately so only friends can call it.
  using SMTRefBase<SMTSort, SMTSortRefTraits>::SMTRefBase;

  friend class SMTSolverImpl;
};

/// Generic base class for SMT sorts
class SMTSort {
public:
  /// Width payload for scalar sorts whose identity is determined by a single
  /// bit width, such as Bool, BV, RM, and BVRM.
  struct ScalarSortData {
    unsigned Width = 0;
  };

  /// Width payload for floating-point sorts.
  ///
  /// Width is the total encoded width. ExpWidth is the exponent width. SigWidth
  /// follows Camada's public convention for the specific sort kind: native FP
  /// sorts store the public significand-width argument, while BVFP sorts store
  /// the encoded significand width used by the bit-vector representation.
  struct FPSortData {
    unsigned Width = 0;
    unsigned ExpWidth = 0;
    unsigned SigWidth = 0;
  };

  /// Payload for array sorts: index sort and element sort.
  struct ArraySortData {
    SMTSortRef IndexSort;
    SMTSortRef ElementSort;
  };

  /// Payload for uninterpreted-function sorts.
  ///
  /// DomainSorts is ordered by argument position and CodomainSort is the return
  /// sort.
  struct FunctionSortData {
    std::vector<SMTSortRef> DomainSorts;
    SMTSortRef CodomainSort;
  };

  /// Payload for tuple sorts, ordered by tuple element index.
  struct TupleSortData {
    std::vector<SMTSortRef> ElementSorts;
  };

  using SortData = std::variant<std::monostate, ScalarSortData, FPSortData,
                                ArraySortData, FunctionSortData, TupleSortData>;

  explicit SMTSort(SMTSortKind K, SortData D = {})
      : Kind(K), Data(std::move(D)) {}
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

  /// Returns true if the sort is an integer.
  bool isIntSort() const { return Kind == SMTSortKind::Int; }

  /// Returns true if the sort is a real.
  bool isRealSort() const { return Kind == SMTSortKind::Real; }

  /// Returns true if the sort is an arithmetic sort.
  bool isArithSort() const { return isIntSort() || isRealSort(); }

  /// Returns true if the sort is a floating-point.
  bool isFPSort() const {
    return Kind == SMTSortKind::FP || Kind == SMTSortKind::BVFP;
  }

  /// Returns true if the sort is a Camada-encoded floating-point.
  bool isBVFPSort() const { return Kind == SMTSortKind::BVFP; }

  /// Returns true if the sort is a rounding mode.
  bool isRMSort() const {
    return Kind == SMTSortKind::RM || Kind == SMTSortKind::BVRM;
  }

  /// Returns true if the sort is a Camada-encoded rounding mode.
  bool isBVRMSort() const { return Kind == SMTSortKind::BVRM; }

  /// Returns true if the sort is an array.
  bool isArraySort() const { return Kind == SMTSortKind::Array; }

  /// Returns true if the sort is a function.
  bool isFunctionSort() const { return Kind == SMTSortKind::Function; }

  /// Returns true if the sort is a tuple.
  bool isTupleSort() const { return Kind == SMTSortKind::Tuple; }

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

  /// Returns the function's domain sorts, fails if the sort is not a function.
  const std::vector<SMTSortRef> &getDomainSorts() const;

  /// Returns the function's codomain sort, fails if the sort is not a function.
  SMTSortRef getCodomainSort() const;

  /// Returns the tuple's element sorts, fails if the sort is not a tuple.
  const std::vector<SMTSortRef> &getTupleElementSorts() const;

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
  virtual void dump(std::string &Out) const;

protected:
  unsigned getStoredWidth() const;

  SMTSortKind Kind;
  SortData Data;
  mutable unsigned SolverWidth = 0;
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
             SortData D = {})
      : SMTSort(K, std::move(D)), Context(std::move(C)), Sort(SS) {}

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
