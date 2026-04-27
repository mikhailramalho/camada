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

#include <cstdio>
#include <string>
#include <type_traits>

namespace camada {

void SMTSort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTSort::dump(std::string &Out) const {
  switch (Kind) {
  case SMTSortKind::Bool:
    Out = "kind: Bool\n";
    Out += "width: " + std::to_string(getWidth()) +
           ", solver: " + std::to_string(getWidthFromSolver()) + "\n";
    return;
  case SMTSortKind::Int:
    Out = "kind: Int\n\n";
    return;
  case SMTSortKind::Real:
    Out = "kind: Real\n\n";
    return;
  case SMTSortKind::BV:
    Out = "kind: Bitvector\n";
    Out += "width: " + std::to_string(getWidth()) +
           ", solver: " + std::to_string(getWidthFromSolver()) + "\n";
    return;
  case SMTSortKind::RM:
  case SMTSortKind::BVRM:
    Out = "kind: RoundingMode\n";
    Out += "width: " + std::to_string(getWidth()) +
           ", solver: " + std::to_string(getWidthFromSolver()) + "\n";
    return;
  case SMTSortKind::FP:
    Out = "kind: Floating-point\n";
    break;
  case SMTSortKind::BVFP:
    Out = "kind: BV Floating-point\n";
    break;
  case SMTSortKind::Array:
    Out = "kind: Array\n";
    break;
  case SMTSortKind::Function:
    Out = "kind: Function\n";
    break;
  case SMTSortKind::Tuple:
    Out = "kind: Tuple\n";
    break;
  }

  std::visit(
      [this, &Out](const auto &DataValue) {
        using T = std::decay_t<decltype(DataValue)>;
        if constexpr (std::is_same_v<T, std::monostate>) {
          return;
        } else if constexpr (std::is_same_v<T, ScalarSortData>) {
          Out += "width: " + std::to_string(DataValue.Width) +
                 ", solver: " + std::to_string(getWidthFromSolver()) + "\n";
        } else if constexpr (std::is_same_v<T, FPSortData>) {
          Out += "width: " + std::to_string(DataValue.Width) +
                 ", solver: " + std::to_string(getWidthFromSolver()) +
                 " (exp: " + std::to_string(DataValue.ExpWidth) +
                 ", sig: " + std::to_string(DataValue.SigWidth) + ")\n";
        } else if constexpr (std::is_same_v<T, ArraySortData>) {
          std::string Index;
          std::string Element;
          DataValue.IndexSort->dump(Index);
          DataValue.ElementSort->dump(Element);
          Out += "Index: " + Index;
          Out += "Element: " + Element;
        } else if constexpr (std::is_same_v<T, FunctionSortData>) {
          Out += "Domain:\n";
          for (const auto &Sort : DataValue.DomainSorts) {
            std::string Domain;
            Sort->dump(Domain);
            Out += Domain;
          }
          Out += "Codomain: ";
          std::string Codomain;
          DataValue.CodomainSort->dump(Codomain);
          Out += Codomain;
        } else if constexpr (std::is_same_v<T, TupleSortData>) {
          Out += "Elements:\n";
          for (const auto &Sort : DataValue.ElementSorts) {
            std::string Element;
            Sort->dump(Element);
            Out += Element;
          }
        }
      },
      Data);
}

unsigned SMTSort::getWidth() const {
  fatalErrorIf(
      isArraySort() || isFunctionSort() || isTupleSort() || isArithSort(),
      "Width is not defined for array, function, tuple, or arithmetic sorts");
  if (isFPSort())
    return std::get<FPSortData>(Data).Width;

  return std::get<ScalarSortData>(Data).Width;
}

unsigned SMTSort::getWidthFromSolver() const {
  fatalError("Unimplemented for current type");
}

unsigned SMTSort::getFPSignificandWidth() const {
  fatalErrorIf(!isFPSort(), "Significand width is only defined for FP sorts");
  return std::get<FPSortData>(Data).SigWidth;
}

unsigned SMTSort::getFPExponentWidth() const {
  fatalErrorIf(!isFPSort(), "Exponent width is only defined for FP sorts");
  return std::get<FPSortData>(Data).ExpWidth;
}

SMTSortRef SMTSort::getIndexSort() const {
  fatalErrorIf(!isArraySort(), "Index sort is only defined for array sorts");
  return std::get<ArraySortData>(Data).IndexSort;
}

SMTSortRef SMTSort::getElementSort() const {
  fatalErrorIf(!isArraySort(), "Element sort is only defined for array sorts");
  return std::get<ArraySortData>(Data).ElementSort;
}

const std::vector<SMTSortRef> &SMTSort::getDomainSorts() const {
  fatalErrorIf(!isFunctionSort(),
               "Domain sorts are only defined for function sorts");
  return std::get<FunctionSortData>(Data).DomainSorts;
}

SMTSortRef SMTSort::getCodomainSort() const {
  fatalErrorIf(!isFunctionSort(),
               "Codomain sort is only defined for function sorts");
  return std::get<FunctionSortData>(Data).CodomainSort;
}

const std::vector<SMTSortRef> &SMTSort::getTupleElementSorts() const {
  fatalErrorIf(!isTupleSort(),
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
  if (Kind != Other.Kind)
    return false;

  // Arithmetic sorts do not carry width-style payload data in Camada, so
  // sort-kind equality is the whole comparison for them.
  if (Kind == SMTSortKind::Int || Kind == SMTSortKind::Real)
    return true;

  if (Data.index() != Other.Data.index())
    return false;

  return std::visit(
      [this, &Other](const auto &ThisData, const auto &OtherData) -> bool {
        using T = std::decay_t<decltype(ThisData)>;
        using U = std::decay_t<decltype(OtherData)>;
        if constexpr (!std::is_same_v<T, U>) {
          return false;
        } else if constexpr (std::is_same_v<T, std::monostate>) {
          return true;
        } else if constexpr (std::is_same_v<T, ScalarSortData>) {
          return ThisData.Width == OtherData.Width &&
                 getWidthFromSolver() == Other.getWidthFromSolver();
        } else if constexpr (std::is_same_v<T, FPSortData>) {
          return ThisData.Width == OtherData.Width &&
                 ThisData.ExpWidth == OtherData.ExpWidth &&
                 ThisData.SigWidth == OtherData.SigWidth &&
                 getWidthFromSolver() == Other.getWidthFromSolver();
        } else if constexpr (std::is_same_v<T, ArraySortData>) {
          return ThisData.IndexSort == OtherData.IndexSort &&
                 ThisData.ElementSort == OtherData.ElementSort;
        } else if constexpr (std::is_same_v<T, FunctionSortData>) {
          return ThisData.DomainSorts == OtherData.DomainSorts &&
                 ThisData.CodomainSort == OtherData.CodomainSort;
        } else if constexpr (std::is_same_v<T, TupleSortData>) {
          return ThisData.ElementSorts == OtherData.ElementSorts;
        }
      },
      Data, Other.Data);
}

} // namespace camada
