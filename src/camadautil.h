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

#ifndef CAMADAUTIL_H_
#define CAMADAUTIL_H_

#include <bitset>
#include <cstdint>
#include <string>

namespace camada {

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
