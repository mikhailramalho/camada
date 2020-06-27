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

#include "camada.h"
#include "ac_config.h"

#include <iostream>

using namespace camada;

#if SOLVER_Z3_ENABLED
#include "z3solver.h"
#endif

#if SOLVER_MATHSAT_ENABLED
#include "mathsatsolver.h"
#endif

#if SOLVER_CVC4_ENABLED
#include "cvc4solver.h"
#endif

#if SOLVER_BOOLECTOR_ENABLED
#include "boolectorsolver.h"
#endif

#if SOLVER_YICES_ENABLED
#include "yicessolver.h"
#endif

std::string camada::getCamadaVersion() { return CAMADA_VERSION; }

[[noreturn]] void camada::abortWithMessage(const std::string &Msg) {
  std::cerr << Msg << '\n';
  abort();
}

void camada::abortCondWithMessage(bool Cond, const std::string &Msg) {
  if (!Cond)
    abortWithMessage(Msg);
}

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

void camada::SMTExpr::dump() const {
  std::cerr << "SMTExpr dump not implemented.\n";
}

void camada::SMTSolver::dump() {
  std::cerr << "SMTSolver dump not implemented.\n";
}

void camada::SMTSolver::dumpModel() {
  std::cerr << "SMTSolver model dump not implemented.\n";
}

unsigned SMTSort::getWidth() const {
  abortWithMessage("Unimplemented for current type");
}

unsigned SMTSort::getFPSignificandWidth() const {
  abortCondWithMessage(isFPSort(), "Not a floating-point sort!");
  return getFPSignificandWidthImpl();
}

unsigned SMTSort::getFPExponentWidth() const {
  abortCondWithMessage(isFPSort(), "Not a floating-point sort!");
  return getFPExponentWidthImpl();
}

bool operator==(SMTSort const &LHS, SMTSort const &RHS) {
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

bool SMTSort::isBVSort() const { return false; }

bool SMTSort::isBoolSort() const { return false; }

bool SMTSort::isFPSort() const { return false; }

bool SMTSort::isRMSort() const { return false; }

unsigned SMTSort::getFPSignificandWidthImpl() const {
  abortWithMessage("Unimplemented for current type");
}

unsigned SMTSort::getFPExponentWidthImpl() const {
  abortWithMessage("Unimplemented for current type");
}

camada::SMTSolverRef camada::createZ3Solver() {
#if SOLVER_Z3_ENABLED
  return std::make_shared<Z3Solver>();
#else
  std::cerr << "Camada was not compiled with Z3 support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_Z3=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createMathSATSolver() {
#if SOLVER_MATHSAT_ENABLED
  return std::make_shared<MathSATSolver>();
#else
  std::cerr << "Camada was not compiled with MathSAT support, rebuild "
               "with -DCAMADA_ENABLE_SOLVER_MATHSAT=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createCVC4Solver() {
#if SOLVER_CVC4_ENABLED
  return std::make_shared<CVC4Solver>();
#else
  std::cerr << "Camada was not compiled with CVC4 support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_CVC4=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createBoolectorSolver() {
#if SOLVER_BOOLECTOR_ENABLED
  return std::make_shared<BtorSolver>();
#else
  std::cerr << "Camada was not compiled with Boolector support, rebuild "
               "with -DCAMADA_ENABLE_SOLVER_BOOLECTOR=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createYicesSolver() {
#if SOLVER_YICES_ENABLED
  return std::make_shared<YicesSolver>();
#else
  std::cerr << "Camada was not compiled with YICES support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_YICES=ON\n";
  abort();
#endif
}
