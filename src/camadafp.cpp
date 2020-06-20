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

#include "camadafp.h"

using namespace camada;

SMTSortRef SMTFPSolverBase::getRoundingModeSortImpl() {}

SMTSortRef SMTFPSolverBase::getFloatSortImpl(const unsigned ExpWidth,
                                             const unsigned SigWidth) {}

SMTExprRef SMTFPSolverBase::mkFPNegImpl(const SMTExprRef &Exp) {}

SMTExprRef SMTFPSolverBase::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {}

SMTExprRef SMTFPSolverBase::mkFPIsNaNImpl(const SMTExprRef &Exp) {}

SMTExprRef SMTFPSolverBase::mkFPIsNormalImpl(const SMTExprRef &Exp) {}

SMTExprRef SMTFPSolverBase::mkFPIsZeroImpl(const SMTExprRef &Exp) {}

SMTExprRef SMTFPSolverBase::mkFPMulImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPDivImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPRemImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {}

SMTExprRef SMTFPSolverBase::mkFPAddImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPSubImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPSqrtImpl(const SMTExprRef &Exp,
                                         const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPFMAImpl(const SMTExprRef &X,
                                        const SMTExprRef &Y,
                                        const SMTExprRef &Z,
                                        const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPLtImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {}

SMTExprRef SMTFPSolverBase::mkFPLeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {}

SMTExprRef SMTFPSolverBase::mkFPEqualImpl(const SMTExprRef &LHS,
                                          const SMTExprRef &RHS) {}

SMTExprRef SMTFPSolverBase::mkFPtoFPImpl(const SMTExprRef &From,
                                         const SMTSortRef &To,
                                         const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkSBVtoFPImpl(const SMTExprRef &From,
                                          const SMTSortRef &To,
                                          const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkUBVtoFPImpl(const SMTExprRef &From,
                                          const SMTSortRef &To,
                                          const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkFPtoSBVImpl(const SMTExprRef &From,
                                          unsigned ToWidth) {}

SMTExprRef SMTFPSolverBase::mkFPtoUBVImpl(const SMTExprRef &From,
                                          unsigned ToWidth) {}

SMTExprRef SMTFPSolverBase::mkFPtoIntegralImpl(const SMTExprRef &From,
                                               RoundingMode R) {}

float SMTFPSolverBase::getFloatImpl(const SMTExprRef &Exp) {}

double SMTFPSolverBase::getDoubleImpl(const SMTExprRef &Exp) {}

bool SMTFPSolverBase::getInterpretationImpl(const SMTExprRef &Exp,
                                            float &Float) {}

bool SMTFPSolverBase::getInterpretationImpl(const SMTExprRef &Exp,
                                            double &Double) {}

SMTExprRef SMTFPSolverBase::mkFloatImpl(const float Float) {}

SMTExprRef SMTFPSolverBase::mkDoubleImpl(const double Double) {}

SMTExprRef SMTFPSolverBase::mkRoundingModeImpl(const RoundingMode R) {}

SMTExprRef SMTFPSolverBase::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                                      const unsigned SigWidth) {}

SMTExprRef SMTFPSolverBase::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                                      const unsigned SigWidth) {}
