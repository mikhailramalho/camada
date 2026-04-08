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
#include "camadaerror.h"

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <string>

namespace camada {

void SMTSort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTSort::dump(std::string &Out) const {
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
  else if (isTupleSort())
    k = "Tuple";
  else {
    Out = "Unknown sort.\n";
    abort();
  }

  Out = "kind: " + k + "\n";
  if (isArraySort()) {
    std::string Index;
    std::string Element;
    getIndexSort()->dump(Index);
    getElementSort()->dump(Element);
    Out += "Index: " + Index;
    Out += "Element: " + Element;
    return;
  }

  if (isFunctionSort()) {
    Out += "Domain:\n";
    for (const auto &Sort : getDomainSorts()) {
      std::string Domain;
      Sort->dump(Domain);
      Out += Domain;
    }
    Out += "Codomain: ";
    {
      std::string Codomain;
      getCodomainSort()->dump(Codomain);
      Out += Codomain;
    }
    return;
  }

  if (isTupleSort()) {
    Out += "Elements:\n";
    for (const auto &Sort : getTupleElementSorts()) {
      std::string Element;
      Sort->dump(Element);
      Out += Element;
    }
    return;
  }

  if (isArithSort()) {
    Out += "\n";
    return;
  }

  Out += "width: " + std::to_string(getWidth()) +
         ", solver: " + std::to_string(getWidthFromSolver());
  if (isFPSort())
    Out += " (exp: " + std::to_string(getFPExponentWidth()) +
           ", sig: " + std::to_string(getFPSignificandWidth()) + ")";
  Out += "\n";
}

unsigned SMTSort::getWidth() const {
  assert(
      !isArraySort() && !isFunctionSort() && !isTupleSort() && !isArithSort() &&
      "Width is not defined for array, function, tuple, or arithmetic sorts");
  if (isFPSort())
    return std::get<FPSortData>(Data).Width;

  return std::get<ScalarSortData>(Data).Width;
}

unsigned SMTSort::getWidthFromSolver() const {
  fatalError("Unimplemented for current type");
}

unsigned SMTSort::getFPSignificandWidth() const {
  assert(isFPSort() && "Significand width is only defined for FP sorts");
  return std::get<FPSortData>(Data).SigWidth;
}

unsigned SMTSort::getFPExponentWidth() const {
  assert(isFPSort() && "Exponent width is only defined for FP sorts");
  return std::get<FPSortData>(Data).ExpWidth;
}

SMTSortRef SMTSort::getIndexSort() const {
  assert(isArraySort() && "Index sort is only defined for array sorts");
  return std::get<ArraySortData>(Data).IndexSort;
}

SMTSortRef SMTSort::getElementSort() const {
  assert(isArraySort() && "Element sort is only defined for array sorts");
  return std::get<ArraySortData>(Data).ElementSort;
}

const std::vector<SMTSortRef> &SMTSort::getDomainSorts() const {
  assert(isFunctionSort() &&
         "Domain sorts are only defined for function sorts");
  return std::get<FunctionSortData>(Data).DomainSorts;
}

SMTSortRef SMTSort::getCodomainSort() const {
  assert(isFunctionSort() &&
         "Codomain sort is only defined for function sorts");
  return std::get<FunctionSortData>(Data).CodomainSort;
}

const std::vector<SMTSortRef> &SMTSort::getTupleElementSorts() const {
  assert(isTupleSort() &&
         "Tuple element sorts are only defined for tuple sorts");
  return std::get<TupleSortData>(Data).ElementSorts;
}

bool SMTSort::validateSortWidth() const {
  // Don't check array/function/arithmetic sort widths for now
  if (isArraySort() || isFunctionSort() || isTupleSort() || isArithSort())
    return true;

  return getWidthFromSolver() == getWidth();
}

bool SMTSort::operator==(SMTSort const &Other) const {
  if (isBoolSort() && Other.isBoolSort())
    return true;

  if (isIntSort() && Other.isIntSort())
    return true;

  if (isRealSort() && Other.isRealSort())
    return true;

  if (isRMSort() && Other.isRMSort())
    return isBVRMSort() == Other.isBVRMSort();

  if (isArraySort())
    return Other.isArraySort() && (getIndexSort() == Other.getIndexSort()) &&
           (getElementSort() == Other.getElementSort());

  if (isFunctionSort()) {
    return Other.isFunctionSort() &&
           getDomainSorts() == Other.getDomainSorts() &&
           getCodomainSort() == Other.getCodomainSort();
  }

  if (isTupleSort())
    return Other.isTupleSort() &&
           getTupleElementSorts() == Other.getTupleElementSorts();

  if (getWidth() != Other.getWidth())
    return false;

  if (getWidthFromSolver() != Other.getWidthFromSolver())
    return false;

  if (isFPSort() && Other.isFPSort())
    return isBVFPSort() == Other.isBVFPSort() &&
           getFPExponentWidth() == Other.getFPExponentWidth() &&
           getFPSignificandWidth() == Other.getFPSignificandWidth();

  if (isBVSort() && Other.isBVSort())
    return true;

  return false;
}

} // namespace camada
