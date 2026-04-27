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
#include <memory>
#include <utility>

#include "camadacommon.h"

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

/// Shared implementation for public solver-owned object handles.
///
/// Handles are lightweight, copyable references to objects owned by a solver's
/// arena. They do not own the pointed-to object. Instead, they keep a shared
/// generation state from the owning solver so dereferencing a handle after
/// reset or destruction fails deterministically instead of reading freed arena
/// memory.
///
/// The non-ownership invariant is load-bearing: handle destruction must not
/// touch the pointed-to object, because cached handles inside the owning
/// solver are destroyed *after* the solver bumps its generation and after the
/// arena destroys their backing objects. Do not add ownership semantics
/// (ref-counting, RAII cleanup) to this base without auditing the reset and
/// destructor paths in SMTSolverImpl.
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

  CAMADA_ALWAYS_INLINE bool isValid() const {
    return Ptr != nullptr && State &&
           State->Generation.load(std::memory_order_relaxed) == Generation;
  }

protected:
  /// Construct a live handle. Kept protected so only concrete handle wrappers
  /// can decide which solver internals are allowed to create valid handles.
  SMTRefBase(const T *ThePtr, std::shared_ptr<const SMTHandleState> TheState,
             uint64_t TheGeneration)
      : Ptr(ThePtr), State(std::move(TheState)), Generation(TheGeneration) {}

private:
  CAMADA_ALWAYS_INLINE void validate() const {
    if (Ptr && State &&
        State->Generation.load(std::memory_order_relaxed) == Generation)
      return;
    reportInvalid();
  }

  // Cold slow path — kept out of the inlined fast path so every dereference
  // site only pays for the hot Ptr/State/Generation check, not the three
  // diagnostic branches.
  CAMADA_COLD_NOINLINE void reportInvalid() const {
    fatalErrorIf(!Ptr, Traits::nullMessage());
    fatalErrorIf(!State, Traits::movedFromMessage());
    fatalErrorIf(State->Generation.load(std::memory_order_relaxed) !=
                     Generation,
                 Traits::staleMessage());
  }

  const T *Ptr = nullptr;
  std::shared_ptr<const SMTHandleState> State;
  uint64_t Generation = 0;
};

} // namespace camada

#endif
