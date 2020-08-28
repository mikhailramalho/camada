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

#include "camadasort.h"

#include <cassert>
#include <iostream>

void camada::SMTSort::dump() const {
  std::string k;
  if (isBoolSort())
    k = "Bool";
  else if (isBVSort())
    k = "Bitvector";
  else if (isRMSort())
    k = "RoundingMode";
  else if (isFPSort())
    k = "Floating-point";

  std::cerr << "kind: " << k << '\n';
  std::cerr << "width: " << getWidth();
  if (isFPSort())
    std::cerr << " (exp: " << getFPExponentWidth()
              << ", sig: " << getFPSignificandWidth() << ")";
  std::cerr << '\n';
}

unsigned camada::SMTSort::getWidth() const {
  assert(0 && "Unimplemented for current type");
  __builtin_unreachable();
}

unsigned camada::SMTSort::getFPSignificandWidth() const {
  assert(0 && "Unimplemented for current type");
  __builtin_unreachable();
}

unsigned camada::SMTSort::getFPExponentWidth() const {
  assert(0 && "Unimplemented for current type");
  __builtin_unreachable();
}

camada::SMTSortRef camada::SMTSort::getIndexSort() const {
  assert(0 && "Unimplemented for current type");
  __builtin_unreachable();
}

camada::SMTSortRef camada::SMTSort::getElementSort() const {
  assert(0 && "Unimplemented for current type");
  __builtin_unreachable();
}

bool operator==(camada::SMTSort const &LHS, camada::SMTSort const &RHS) {
  if (LHS.isBoolSort() && RHS.isBoolSort())
    return true;

  if (LHS.isRMSort() && RHS.isRMSort())
    return true;

  if (LHS.getWidth() != RHS.getWidth())
    return false;

  if (LHS.isBVSort() && RHS.isBVSort())
    return true; // Width was already checked

  if (LHS.isFPSort() && RHS.isFPSort())
    return (LHS.getFPSignificandWidth() == RHS.getFPSignificandWidth()) &&
           (LHS.getFPExponentWidth() == RHS.getFPExponentWidth());

  return false;
}
