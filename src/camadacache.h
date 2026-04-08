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

#ifndef CAMADACACHE_H_
#define CAMADACACHE_H_

#include <cstdint>
#include <functional>
#include <string>
#include <vector>

namespace camada {

class SMTSort;
enum class FPSpecialValueKind : uint8_t { NaN, Zero, Inf, One };

struct FPSortCacheKey {
  unsigned ExpWidth;
  unsigned SigWidth;

  bool operator==(const FPSortCacheKey &Other) const {
    return ExpWidth == Other.ExpWidth && SigWidth == Other.SigWidth;
  }
};

struct FPSortCacheKeyHash {
  std::size_t operator()(const FPSortCacheKey &Key) const {
    return (static_cast<std::size_t>(Key.ExpWidth) << 32) ^ Key.SigWidth;
  }
};

struct ArraySortCacheKey {
  const SMTSort *IndexSort;
  const SMTSort *ElementSort;

  bool operator==(const ArraySortCacheKey &Other) const {
    return IndexSort == Other.IndexSort && ElementSort == Other.ElementSort;
  }
};

struct ArraySortCacheKeyHash {
  std::size_t operator()(const ArraySortCacheKey &Key) const {
    auto Index = reinterpret_cast<std::uintptr_t>(Key.IndexSort);
    auto Element = reinterpret_cast<std::uintptr_t>(Key.ElementSort);
    return static_cast<std::size_t>(Index ^ (Element << 1));
  }
};

struct FunctionSortCacheKey {
  std::vector<const SMTSort *> DomainSorts;
  const SMTSort *CodomainSort;

  bool operator==(const FunctionSortCacheKey &Other) const {
    return CodomainSort == Other.CodomainSort &&
           DomainSorts == Other.DomainSorts;
  }
};

struct TupleSortCacheKey {
  std::vector<const SMTSort *> ElementSorts;

  bool operator==(const TupleSortCacheKey &Other) const {
    return ElementSorts == Other.ElementSorts;
  }
};

struct TupleSortCacheKeyHash {
  std::size_t operator()(const TupleSortCacheKey &Key) const {
    std::size_t Hash = 1469598103934665603ULL;
    for (const SMTSort *Sort : Key.ElementSorts) {
      auto Ptr = reinterpret_cast<std::uintptr_t>(Sort);
      Hash ^= static_cast<std::size_t>(Ptr + 0x9e3779b97f4a7c15ULL +
                                       (Hash << 6) + (Hash >> 2));
    }
    return Hash;
  }
};

struct FunctionSortCacheKeyHash {
  std::size_t operator()(const FunctionSortCacheKey &Key) const {
    std::size_t Hash = reinterpret_cast<std::uintptr_t>(Key.CodomainSort) *
                       1469598103934665603ULL;
    for (const SMTSort *Sort : Key.DomainSorts) {
      auto Ptr = reinterpret_cast<std::uintptr_t>(Sort);
      Hash ^= static_cast<std::size_t>(Ptr + 0x9e3779b97f4a7c15ULL +
                                       (Hash << 6) + (Hash >> 2));
    }
    return Hash;
  }
};

struct SymbolExprCacheKey {
  const SMTSort *Sort;
  std::string Name;

  bool operator==(const SymbolExprCacheKey &Other) const {
    return Sort == Other.Sort && Name == Other.Name;
  }
};

struct FPSpecialExprCacheKey {
  unsigned ExpWidth;
  unsigned SigWidth;
  FPSpecialValueKind Kind;
  bool Sign;

  bool operator==(const FPSpecialExprCacheKey &Other) const {
    return ExpWidth == Other.ExpWidth && SigWidth == Other.SigWidth &&
           Kind == Other.Kind && Sign == Other.Sign;
  }
};

struct FPSpecialExprCacheKeyHash {
  std::size_t operator()(const FPSpecialExprCacheKey &Key) const {
    std::size_t Hash = static_cast<std::size_t>(Key.ExpWidth);
    Hash ^= static_cast<std::size_t>(Key.SigWidth) << 8;
    Hash ^= static_cast<std::size_t>(Key.Kind) << 16;
    Hash ^= static_cast<std::size_t>(Key.Sign) << 24;
    return Hash;
  }
};

struct SymbolExprCacheKeyHash {
  std::size_t operator()(const SymbolExprCacheKey &Key) const {
    auto SortPtr = reinterpret_cast<std::uintptr_t>(Key.Sort);
    auto NameHash = std::hash<std::string>{}(Key.Name);
    return static_cast<std::size_t>(SortPtr ^ (NameHash << 1));
  }
};

} // namespace camada

#endif
