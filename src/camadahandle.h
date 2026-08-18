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

#ifndef CAMADAHANDLE_H_
#define CAMADAHANDLE_H_

#include <atomic>
#include <cstdint>
#include <limits>

#include "camadaerrors.h"
#include "camadafeatures.h"

namespace camada {

/// Shared liveness state for handles to solver-owned objects. Generation is
/// atomic so that a handle held by one thread can be safely dereferenced
/// (or asked isValid()) while the owning solver is reset or destroyed on
/// another. Note that this only makes the handle's liveness check race-free;
/// it does not make the underlying SMTSolver thread-safe — see camada.h for
/// the full threading contract.
struct SMTHandleState {
  std::atomic<uint64_t> Generation{1};

  /// Bump the generation, aborting before it would wrap to zero. Wrapping is
  /// unsafe because Generation == 0 is the value carried by default-constructed
  /// handles, so a stale handle could collide with a freshly-bumped state.
  ///
  /// The store uses release ordering so that any writes the owning solver
  /// performs before the bump (cache clears, destructor sequencing) become
  /// observable to a reader that uses acquire — though the standard handle
  /// liveness check uses relaxed, since it only needs to detect the change in
  /// value, not synchronize with prior writes.
  void bumpGeneration() {
    uint64_t Prev = Generation.fetch_add(1, std::memory_order_release);
    fatalErrorIf(Prev == std::numeric_limits<uint64_t>::max(),
                 "SMT handle generation counter overflow");
  }
};

/// Allocate a handle state that lives for the rest of the process. Handles
/// keep a raw pointer to their solver's state, so the state must stay
/// readable even after the solver is destroyed — that is what lets a
/// dangling handle abort with "stale" instead of reading freed memory. The
/// cost is ~one allocation per solver ever constructed, reachable from a
/// static registry (so leak checkers see it as still-reachable, not lost).
SMTHandleState *makeProcessLifetimeHandleState();

/// Shared implementation for public solver-owned object handles.
///
/// Handles are lightweight, copyable references to objects owned by a solver's
/// arena. They do not own the pointed-to object.
///
/// With CAMADA_CHECKED_HANDLES (the default) a handle also carries a pointer
/// to the owning solver's generation state plus the generation it was created
/// under (24 bytes total), so dereferencing it after reset or destruction
/// fails deterministically instead of reading freed arena memory. Configured
/// with -DCAMADA_CHECKED_HANDLES=OFF, a handle is a single raw pointer
/// (8 bytes) and stale use is undefined behavior, exactly like a raw
/// `const SMTExpr *`.
///
/// The non-ownership invariant is load-bearing: handle destruction must not
/// touch the pointed-to object, because cached handles inside the owning
/// solver are destroyed *after* the solver bumps its generation and after the
/// arena destroys their backing objects. Do not add ownership semantics
/// (ref-counting, RAII cleanup) to this base without auditing the reset and
/// destructor paths in SMTSolverImpl.

// GCC 13+ has emitted false-positive -Wmaybe-uninitialized for SMTRefBase's
// implicitly-generated copy/move when CAMADA_ALWAYS_INLINE expands them
// through std::variant<..., SortData, ...> templates deeply enough that flow
// analysis loses track of the source object's initialized state. The data
// members all have NSDMIs, so the warning is bogus, but it would otherwise
// turn into an error under -Werror. Suppress narrowly here.
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

template <typename T, typename Traits> class SMTRefBase {
public:
  SMTRefBase() = default;

  CAMADA_ALWAYS_INLINE const T *get() const {
    validate();
    return Ptr;
  }

  CAMADA_ALWAYS_INLINE const T &operator*() const { return *get(); }

  CAMADA_ALWAYS_INLINE const T *operator->() const { return get(); }

  explicit operator bool() const { return isValid(); }

#if CAMADA_CHECKED_HANDLES
  CAMADA_ALWAYS_INLINE bool isValid() const {
    return Ptr != nullptr && State &&
           State->Generation.load(std::memory_order_relaxed) == Generation;
  }
#else
  /// Unchecked mode cannot see resets: a non-null handle answers valid
  /// even when the solver it came from is gone.
  CAMADA_ALWAYS_INLINE bool isValid() const { return Ptr != nullptr; }
#endif

protected:
  /// Construct a live handle. Kept protected so only concrete handle wrappers
  /// can decide which solver internals are allowed to create valid handles.
  /// The state/generation arguments are accepted (and ignored) in unchecked
  /// mode so construction sites compile identically under both layouts.
  /// Each branch is a complete declaration — clang-format mis-parses a
  /// preprocessor conditional inside a member-initializer list.
#if CAMADA_CHECKED_HANDLES
  SMTRefBase(const T *ThePtr, const SMTHandleState *TheState,
             uint64_t TheGeneration)
      : Ptr(ThePtr), State(TheState), Generation(TheGeneration) {}
#else
  SMTRefBase(const T *ThePtr, const SMTHandleState *TheState,
             uint64_t TheGeneration)
      : Ptr(ThePtr) {
    (void)TheState;
    (void)TheGeneration;
  }
#endif

private:
  CAMADA_ALWAYS_INLINE void validate() const {
#if CAMADA_CHECKED_HANDLES
    if (Ptr && State &&
        State->Generation.load(std::memory_order_relaxed) == Generation)
      return;
#else
    if (Ptr)
      return;
#endif
    reportInvalid();
  }

  // Cold slow path — kept out of the inlined fast path so every dereference
  // site only pays for the hot liveness check, not the diagnostic branches.
  CAMADA_COLD_NOINLINE void reportInvalid() const {
    fatalErrorIf(!Ptr, Traits::nullMessage());
#if CAMADA_CHECKED_HANDLES
    fatalErrorIf(!State, Traits::movedFromMessage());
    fatalErrorIf(State->Generation.load(std::memory_order_relaxed) !=
                     Generation,
                 Traits::staleMessage());
#endif
  }

  const T *Ptr = nullptr;
#if CAMADA_CHECKED_HANDLES
  const SMTHandleState *State = nullptr;
  uint64_t Generation = 0;
#endif
};

#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic pop
#endif

} // namespace camada

#endif
