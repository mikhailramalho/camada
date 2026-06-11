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

/// True when Sort is a tuple sort or an array sort whose element sort
/// (recursively) involves a tuple. Drives the decomposed tuple-array
/// dispatch: such sorts have no backend representation on backends
/// without native datatype support.
bool sortContainsTuple(const SMTSortRef &Sort);

/// Camada-managed arrays of tuples: an `Array<Idx, T>` where T involves a
/// tuple is represented as a bundle of per-leaf-field backend arrays —
/// `Array<Idx, Tuple{BV32, Tuple{Bool}}>` becomes `{Array<Idx, BV32>,
/// Array<Idx, Bool>}`. The tuple structure is dissolved at the Camada
/// layer; all array reasoning stays in the backend's native theory.
/// Operations recurse leaf-wise, so arbitrary tuple/array nesting
/// flattens to native nested-arrays-of-scalars.

SMTSortRef mkCamadaTupleArraySort(SMTSolverImpl &Solver,
                                  const SMTSortRef &IndexSort,
                                  const SMTSortRef &ElemSort);

SMTExprRef mkCamadaTupleArraySymbol(SMTSolverImpl &Solver,
                                    const std::string &Name,
                                    const SMTSortRef &Sort);

SMTExprRef mkCamadaTupleArraySelect(SMTSolverImpl &Solver,
                                    const SMTExprRef &Array,
                                    const SMTExprRef &Index);

SMTExprRef mkCamadaTupleArrayStore(SMTSolverImpl &Solver,
                                   const SMTExprRef &Array,
                                   const SMTExprRef &Index,
                                   const SMTExprRef &Element);

SMTExprRef mkCamadaTupleArrayConst(SMTSolverImpl &Solver,
                                   const SMTSortRef &IndexSort,
                                   const SMTExprRef &InitValue,
                                   ConstArrayLowering Lowering);

SMTExprRef mkCamadaTupleArrayEqual(SMTSolverImpl &Solver, const SMTExprRef &LHS,
                                   const SMTExprRef &RHS);

SMTExprRef mkCamadaTupleArrayIte(SMTSolverImpl &Solver, const SMTExprRef &Cond,
                                 const SMTExprRef &T, const SMTExprRef &F);

} // namespace camada

#endif
