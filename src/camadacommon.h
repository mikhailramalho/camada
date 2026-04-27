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

#ifndef CAMADACOMMON_H_
#define CAMADACOMMON_H_

#include <bitset>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>

// Compiler-specific function attributes used to keep small hot helpers (handle
// liveness checks, etc.) inlined into every call site, and to keep cold error
// paths out of that inlined hot code. GCC and Clang accept the C++11 attribute
// syntax; MSVC has its own spellings; unknown compilers fall back to the
// standard hint-only `inline` and an empty cold/noinline (correct, if less
// performant).
#if defined(__GNUC__) || defined(__clang__)
#define CAMADA_ALWAYS_INLINE [[gnu::always_inline]] inline
#define CAMADA_COLD_NOINLINE [[gnu::cold, gnu::noinline]]
#elif defined(_MSC_VER)
#define CAMADA_ALWAYS_INLINE __forceinline
#define CAMADA_COLD_NOINLINE __declspec(noinline)
#else
#define CAMADA_ALWAYS_INLINE inline
#define CAMADA_COLD_NOINLINE
#endif

namespace camada {

[[noreturn]] static inline void fatalError(const char *Message) {
  std::fprintf(stderr, "%s\n", Message);
  std::abort();
}

[[noreturn]] static inline void unsupportedFeature(const char *Feature) {
  std::fprintf(stderr, "%s is not supported by this backend\n", Feature);
  std::abort();
}

static inline void fatalErrorIf(bool Cond, const char *Message) {
  if (!Cond)
    return;
  fatalError(Message);
}

static inline std::string toTwosComplementBin(int64_t Value, unsigned Width) {
  const uint64_t RawBits = static_cast<uint64_t>(Value);
  std::string Bits = std::bitset<64>(RawBits).to_string();
  if (Width < 64)
    Bits = Bits.substr(64 - Width);
  else if (Width > 64)
    Bits.insert(Bits.begin(), Width - 64, Value < 0 ? '1' : '0');
  return Bits;
}

} // namespace camada

#endif
