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

#ifndef CAMADADECIMAL_H_
#define CAMADADECIMAL_H_

#include <string>

namespace camada {

// Multiplies a non-negative decimal string in place by a small factor.
inline void mulDecimal(std::string &Dec, int Factor) {
  int Carry = 0;
  for (auto It = Dec.rbegin(); It != Dec.rend(); ++It) {
    int Value = (*It - '0') * Factor + Carry;
    *It = static_cast<char>('0' + Value % 10);
    Carry = Value / 10;
  }
  for (; Carry != 0; Carry /= 10)
    Dec.insert(Dec.begin(), static_cast<char>('0' + Carry % 10));
}

} // namespace camada

#endif
