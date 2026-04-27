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

#include <cstdint>
#include <memory>
#include <utility>

#include "camadaerror.h"

namespace camada {

struct SMTHandleState {
  uint64_t Generation = 1;
};

/// Shared implementation for public solver-owned object handles.
///
/// Handles are lightweight, copyable references to objects owned by a solver's
/// arena. They do not own the pointed-to object. Instead, they keep a shared
/// generation state from the owning solver so dereferencing a handle after
/// reset or destruction fails deterministically instead of reading freed arena
/// memory.
template <typename T, typename Traits> class SMTRefBase {
public:
  SMTRefBase() = default;

  const T *get() const {
    validate();
    return Ptr;
  }

  const T &operator*() const { return *get(); }

  const T *operator->() const { return get(); }

  explicit operator bool() const { return isValid(); }

  bool isValid() const {
    return Ptr != nullptr && State && State->Generation == Generation;
  }

protected:
  /// Construct a live handle. Kept protected so only concrete handle wrappers
  /// can decide which solver internals are allowed to create valid handles.
  SMTRefBase(const T *ThePtr, std::shared_ptr<const SMTHandleState> TheState,
             uint64_t TheGeneration)
      : Ptr(ThePtr), State(std::move(TheState)), Generation(TheGeneration) {}

private:
  void validate() const {
    if (Ptr && State && State->Generation == Generation)
      return;
    fatalErrorIf(!Ptr, Traits::nullMessage());
    fatalErrorIf(!State, Traits::movedFromMessage());
    fatalErrorIf(State->Generation != Generation, Traits::staleMessage());
  }

  const T *Ptr = nullptr;
  std::shared_ptr<const SMTHandleState> State;
  uint64_t Generation = 0;
};

} // namespace camada

#endif
