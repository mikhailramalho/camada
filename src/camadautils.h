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

#ifndef CAMADAUTILS_H_
#define CAMADAUTILS_H_

#include <string>

namespace camada {

/// Return camada version
std::string getCamadaVersion();

/// Abort program if Cond is false and prints Msg to stderr
void abortCondWithMessage(bool Cond, const std::string &Msg);

/// Abort program and prints Msg to stderr
[[noreturn]] void abortWithMessage(const std::string &Msg);

enum class checkResult { SAT, UNSAT, UNKNOWN };

enum class RoundingMode {
  ROUND_TO_EVEN,
  ROUND_TO_AWAY,
  ROUND_TO_PLUS_INF,
  ROUND_TO_MINUS_INF,
  ROUND_TO_ZERO
};

} // namespace camada

#endif