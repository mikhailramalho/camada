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
#include <cstdio>
#include <cstdlib>
#include <string>

void camada::SMTSort::dump() const {
  std::string k;
  if (isBoolSort())
    k = "Bool";
  else if (isIntSort())
    k = "Int";
  else if (isRealSort())
    k = "Real";
  else if (isBVSort() && isFPSort())
    k = "BV Floating-point";
  else if (isBVSort())
    k = "Bitvector";
  else if (isRMSort())
    k = "RoundingMode";
  else if (isFPSort())
    k = "Floating-point";
  else if (isArraySort())
    k = "Array";
  else if (isFunctionSort())
    k = "Function";
  else {
    std::fprintf(stderr, "Unknown sort.\n");
    abort();
  }

  std::fprintf(stderr, "kind: %s\n", k.c_str());
  if (isArraySort()) {
    std::fprintf(stderr, "Index: ");
    getIndexSort()->dump();
    std::fprintf(stderr, "Element: ");
    getElementSort()->dump();
    return;
  }

  if (isFunctionSort()) {
    std::fprintf(stderr, "Domain:\n");
    for (const auto &Sort : getDomainSorts())
      Sort->dump();
    std::fprintf(stderr, "Codomain: ");
    getCodomainSort()->dump();
    return;
  }

  if (isArithSort()) {
    std::fprintf(stderr, "\n");
    return;
  }

  std::fprintf(stderr, "width: %u, solver: %u", getWidth(),
               getWidthFromSolver());
  if (isFPSort())
    std::fprintf(stderr, " (exp: %u, sig: %u)", getFPExponentWidth(),
                 getFPSignificandWidth());
  std::fprintf(stderr, "\n");
}

unsigned camada::SMTSort::getWidth() const {
  assert(!isArraySort() && !isFunctionSort() && !isArithSort() &&
         "Width is not defined for array, function, or arithmetic sorts");
  return Width;
}

unsigned camada::SMTSort::getWidthFromSolver() const {
  assert(0 && "Unimplemented for current type");
  __builtin_unreachable();
}

unsigned camada::SMTSort::getFPSignificandWidth() const {
  assert(isFPSort() && "Significand width is only defined for FP sorts");
  return SigWidth;
}

unsigned camada::SMTSort::getFPExponentWidth() const {
  assert(isFPSort() && "Exponent width is only defined for FP sorts");
  return ExpWidth;
}

camada::SMTSortRef camada::SMTSort::getIndexSort() const {
  assert(isArraySort() && "Index sort is only defined for array sorts");
  return IndexSort;
}

camada::SMTSortRef camada::SMTSort::getElementSort() const {
  assert(isArraySort() && "Element sort is only defined for array sorts");
  return ElementSort;
}

const std::vector<camada::SMTSortRef> &camada::SMTSort::getDomainSorts() const {
  assert(isFunctionSort() &&
         "Domain sorts are only defined for function sorts");
  return DomainSorts;
}

camada::SMTSortRef camada::SMTSort::getCodomainSort() const {
  assert(isFunctionSort() &&
         "Codomain sort is only defined for function sorts");
  return CodomainSort;
}

bool camada::SMTSort::validateSortWidth() const {
  // Don't check array/function/arithmetic sort widths for now
  if (isArraySort() || isFunctionSort() || isArithSort())
    return true;

  return getWidthFromSolver() == getWidth();
}

bool camada::SMTSort::operator==(camada::SMTSort const &Other) const {
  if (isBoolSort() && Other.isBoolSort())
    return true;

  if (isIntSort() && Other.isIntSort())
    return true;

  if (isRealSort() && Other.isRealSort())
    return true;

  if (isRMSort() && Other.isRMSort())
    return true;

  if (isArraySort())
    return Other.isArraySort() && (getIndexSort() == Other.getIndexSort()) &&
           (getElementSort() == Other.getElementSort());

  if (isFunctionSort()) {
    return Other.isFunctionSort() &&
           getDomainSorts() == Other.getDomainSorts() &&
           getCodomainSort() == Other.getCodomainSort();
  }

  if (Width != Other.Width)
    return false;

  if (getWidthFromSolver() != Other.getWidthFromSolver())
    return false;

  if (isFPSort() && Other.isFPSort())
    return !(isBVSort() ^ Other.isBVSort()) && ExpWidth == Other.ExpWidth &&
           SigWidth == Other.SigWidth;

  if (isBVSort() && Other.isBVSort())
    return true;

  return false;
}
