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

#ifndef CAMADAARENA_H_
#define CAMADAARENA_H_

#include <cstddef>
#include <cstdint>
#include <memory>
#include <new>
#include <utility>
#include <vector>

namespace camada {

/// Simple bump-pointer arena for solver-owned objects.
///
/// Objects are placement-new'ed into growable byte blocks and never moved after
/// construction. The arena records a destructor callback per object so clear()
/// can destroy them in reverse creation order while keeping the allocated
/// blocks for reuse.
class ObjectArena {
public:
  explicit ObjectArena(std::size_t InitialBlockSize = 16384)
      : InitialBlockSize(InitialBlockSize) {}

  ObjectArena(const ObjectArena &) = delete;
  ObjectArena &operator=(const ObjectArena &) = delete;

  ObjectArena(ObjectArena &&) = delete;
  ObjectArena &operator=(ObjectArena &&) = delete;

  ~ObjectArena() { clear(); }

  /// Construct an object inside the arena and return its stable address.
  template <typename T, typename... Args> T *create(Args &&...ArgsV) {
    void *Storage = allocate(sizeof(T), alignof(T));
    T *Object = new (Storage) T(std::forward<Args>(ArgsV)...);
    Destructors.push_back(DestructorRecord{
        Object, [](void *Ptr) { static_cast<T *>(Ptr)->~T(); }});
    return Object;
  }

  /// Destroy all live objects and reset block offsets so future allocations
  /// can reuse the existing storage.
  void clear() {
    for (auto It = Destructors.rbegin(); It != Destructors.rend(); ++It)
      It->Destroy(It->Ptr);
    Destructors.clear();
    for (auto &Block : Blocks)
      Block.Offset = 0;
  }

private:
  struct Block {
    std::unique_ptr<std::byte[]> Storage;
    std::size_t Capacity;
    std::size_t Offset = 0;
  };

  struct DestructorRecord {
    void *Ptr;
    void (*Destroy)(void *);
  };

  void *allocate(std::size_t Size, std::size_t Alignment) {
    if (Blocks.empty() || !hasCapacity(Blocks.back(), Size, Alignment))
      addBlock(Size, Alignment);

    Block &Block = Blocks.back();
    auto Base =
        reinterpret_cast<std::uintptr_t>(Block.Storage.get() + Block.Offset);
    auto Padding = alignmentPadding(Base, Alignment);
    Block.Offset += Padding;
    void *Result = Block.Storage.get() + Block.Offset;
    Block.Offset += Size;
    return Result;
  }

  static bool hasCapacity(const Block &Block, std::size_t Size,
                          std::size_t Alignment) {
    auto Base =
        reinterpret_cast<std::uintptr_t>(Block.Storage.get() + Block.Offset);
    auto Padding = alignmentPadding(Base, Alignment);
    return Block.Offset + Padding + Size <= Block.Capacity;
  }

  void addBlock(std::size_t Size, std::size_t Alignment) {
    std::size_t Capacity = InitialBlockSize;
    if (!Blocks.empty())
      Capacity = Blocks.back().Capacity * 2;

    Capacity = std::max(Capacity, Size + Alignment);
    Blocks.push_back(
        Block{std::make_unique<std::byte[]>(Capacity), Capacity, 0});
  }

  static std::size_t alignmentPadding(std::uintptr_t Base,
                                      std::size_t Alignment) {
    auto Misalignment = Base % Alignment;
    return Misalignment == 0 ? 0 : Alignment - Misalignment;
  }

  std::size_t InitialBlockSize;
  std::vector<Block> Blocks;
  std::vector<DestructorRecord> Destructors;
};

} // namespace camada

#endif
