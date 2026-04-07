/**************************************************************************
 *
 * Licensed to the Apache Software Foundation Impl(ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 Impl(the
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

#include "camadaimpl.h"

#include <cstdio>
#include <cstdlib>

namespace camada {
static std::string power2Dec(unsigned int N) {
  std::string result = "1";
  for (unsigned int I = 0; I < N; ++I) {
    int Carry = 0;
    for (auto It = result.rbegin(); It != result.rend(); ++It) {
      int Digit = (*It - '0') * 2 + Carry;
      *It = static_cast<char>('0' + (Digit % 10));
      Carry = Digit / 10;
    }
    if (Carry != 0)
      result.insert(result.begin(), static_cast<char>('0' + Carry));
  }
  return result;
}

[[noreturn]] void
SMTSolverImpl::unsupportedFeatureImpl(const char *Feature) const {
  std::fprintf(stderr, "%s is not supported by this backend\n", Feature);
  std::abort();
}

SMTSortRef SMTSolverImpl::mkFunctionSortImpl(const std::vector<SMTSortRef> &,
                                             const SMTSortRef &) {
  unsupportedFeatureImpl("Uninterpreted functions");
}

SMTExprRef SMTSolverImpl::mkArithNegImpl(const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithAddImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithSubImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithMulImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithDivImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithModImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeatureImpl("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithShlImpl(const SMTExprRef &Exp,
                                         unsigned Amount) {
  return mkArithMul(Exp, mkInt(power2Dec(Amount)));
}

SMTExprRef SMTSolverImpl::mkArithShlImpl(const SMTExprRef &,
                                         const SMTExprRef &) {
  unsupportedFeatureImpl("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithLtImpl(const SMTExprRef &,
                                        const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithGtImpl(const SMTExprRef &,
                                        const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithLeImpl(const SMTExprRef &,
                                        const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkArithGeImpl(const SMTExprRef &,
                                        const SMTExprRef &) {
  unsupportedFeatureImpl("Arithmetic");
}

SMTExprRef SMTSolverImpl::mkInt2RealImpl(const SMTExprRef &) {
  unsupportedFeatureImpl("Real arithmetic");
}

SMTExprRef SMTSolverImpl::mkReal2IntImpl(const SMTExprRef &) {
  unsupportedFeatureImpl("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkIsIntImpl(const SMTExprRef &) {
  unsupportedFeatureImpl("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkIntImpl(int64_t) {
  unsupportedFeatureImpl("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkIntImpl(const std::string &) {
  unsupportedFeatureImpl("Integer arithmetic");
}

SMTExprRef SMTSolverImpl::mkRealImpl(const std::string &) {
  unsupportedFeatureImpl("Real arithmetic");
}

SMTExprRef SMTSolverImpl::mkRealImpl(int64_t) {
  unsupportedFeatureImpl("Real arithmetic");
}

SMTExprRef SMTSolverImpl::mkRealImpl(int64_t, int64_t) {
  unsupportedFeatureImpl("Real arithmetic");
}

SMTExprRef SMTSolverImpl::mkApplyImpl(const SMTExprRef &,
                                      const std::vector<SMTExprRef> &) {
  unsupportedFeatureImpl("Uninterpreted functions");
}

SMTExprRef SMTSolverImpl::mkForallImpl(const std::vector<SMTExprRef> &,
                                       const SMTExprRef &) {
  unsupportedFeatureImpl("Quantifiers");
}

SMTExprRef SMTSolverImpl::mkExistsImpl(const std::vector<SMTExprRef> &,
                                       const SMTExprRef &) {
  unsupportedFeatureImpl("Quantifiers");
}

std::string SMTSolverImpl::getIntImpl(const SMTExprRef &) {
  unsupportedFeatureImpl("Integer arithmetic");
}

void SMTSolverImpl::getRationalImpl(const SMTExprRef &, std::string &,
                                    std::string &) {
  unsupportedFeatureImpl("Real arithmetic");
}

void SMTSolverImpl::dumpImpl() {
  std::string Out;
  dumpImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTSolverImpl::dumpImpl(std::string &Out) {
  Out = "SMTSolver dump not implemented.\n";
}

void SMTSolverImpl::dumpModelImpl() {
  std::string Out;
  dumpModelImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTSolverImpl::dumpModelImpl(std::string &Out) {
  Out = "SMTSolver model dump not implemented.\n";
}

} // namespace camada
