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

#ifndef CAMADATUPLE_H_
#define CAMADATUPLE_H_

#include "camada.h"

#include <string>
#include <vector>

namespace camada {

class SMTSolverImpl;

/// Camada-managed tuple lowering for backends without native datatype
/// support (bitwuzla, mathsat, stp, yices). Tuples are represented as
/// dedicated SMTSort/SMTExpr classes (no backend term), and operations
/// are decomposed into per-field operations against the backend's BV/
/// Bool/array machinery.
///
/// Native-tuple backends (z3, cvc5, smtlib) are unaffected; SMTSolverImpl
/// dispatches here only when nativeTupleSupport() is false.

SMTSortRef mkCamadaTupleSort(SMTSolverImpl &Solver,
                             const std::vector<SMTSortRef> &ElementSorts);

SMTExprRef mkCamadaTupleSymbol(SMTSolverImpl &Solver, const std::string &Name,
                               const SMTSortRef &Sort);

SMTExprRef mkCamadaTuple(SMTSolverImpl &Solver,
                         const std::vector<SMTExprRef> &Elements);

SMTExprRef mkCamadaTupleSelect(SMTSolverImpl &Solver, const SMTExprRef &Tuple,
                               unsigned Index);

SMTExprRef mkCamadaTupleEqual(SMTSolverImpl &Solver, const SMTExprRef &LHS,
                              const SMTExprRef &RHS);

SMTExprRef mkCamadaTupleIte(SMTSolverImpl &Solver, const SMTExprRef &Cond,
                            const SMTExprRef &T, const SMTExprRef &F);

} // namespace camada

#endif
