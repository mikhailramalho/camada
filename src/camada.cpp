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

#include <fmt/printf.h>

std::string camada::getCamadaVersion() { return CAMADA_VERSION; }

[[noreturn]] void camada::abortWithMessage(const std::string &Msg) {
  fmt::print(stderr, Msg + "\n");
  abort();
}

void camada::abortCondWithMessage(bool Cond, const std::string &Msg) {
  if (!Cond)
    abortWithMessage(Msg);
}

void camada::SMTSort::dump() const {
  fmt::printf("SMTSort dump not implemented.\n");
}

void camada::SMTExpr::dump() const {
  fmt::printf("SMTExpr dump not implemented.\n");
}

void camada::SMTSolver::dump() {
  fmt::printf("SMTSolver dump not implemented.\n");
}

void camada::SMTSolver::dumpModel() {
  fmt::printf("SMTSolver model dump not implemented.\n");
}

unsigned SMTSort::getWidth() const {
  abortWithMessage("Unimplemented for current type");
}

unsigned SMTSort::getFloatSignificandWidth() const {
  abortCondWithMessage(isFloatSort(), "Not a floating-point sort!");
  return getFloatSignificandWidthImpl();
}

unsigned SMTSort::getFloatExponentWidth() const {
  abortCondWithMessage(isFloatSort(), "Not a floating-point sort!");
  return getFloatExponentWidthImpl();
}

bool operator==(SMTSort const &LHS, SMTSort const &RHS) {
  if (LHS.isBooleanSort() && RHS.isBooleanSort())
    return true;

  if (LHS.isRoundingModeSort() && RHS.isRoundingModeSort())
    return true;

  if (LHS.getWidth() != RHS.getWidth())
    return false;

  if (LHS.isBitvectorSort() && RHS.isBitvectorSort())
    return true; // Width was already checked

  if (LHS.isFloatSort() && RHS.isFloatSort())
    return (LHS.getFloatSignificandWidth() == RHS.getFloatSignificandWidth()) &&
           (LHS.getFloatExponentWidth() == RHS.getFloatExponentWidth());

  return false;
}

bool SMTSort::isBitvectorSort() const {
  abortWithMessage("Unimplemented for current type");
}

bool SMTSort::isBooleanSort() const {
  abortWithMessage("Unimplemented for current type");
}

bool SMTSort::isFloatSort() const {
  abortWithMessage("Unimplemented for current type");
}

bool SMTSort::isRoundingModeSort() const {
  abortWithMessage("Unimplemented for current type");
}

unsigned SMTSort::getFloatSignificandWidthImpl() const {
  abortWithMessage("Unimplemented for current type");
}

unsigned SMTSort::getFloatExponentWidthImpl() const {
  abortWithMessage("Unimplemented for current type");
}

camada::SMTSolverRef camada::createZ3Solver() {
#if SOLVER_Z3_ENABLED
  return std::make_shared<Z3Solver>();
#else
  fmt::print(stderr, "Camada was not compiled with Z3 support, rebuild with "
                     "-DCAMADA_ENABLE_SOLVER_Z3=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createMathSATSolver() {
#if SOLVER_MATHSAT_ENABLED
  return std::make_shared<MathSATSolver>();
#else
  fmt::print(stderr, "Camada was not compiled with MathSAT support, rebuild "
                     "with -DCAMADA_ENABLE_SOLVER_MATHSAT=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createCVC4Solver() {
#if SOLVER_CVC4_ENABLED
  return std::make_shared<CVC4Solver>();
#else
  fmt::print(stderr, "Camada was not compiled with CVC4 support, rebuild with "
                     "-DCAMADA_ENABLE_SOLVER_CVC4=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createBoolectorSolver() {
#if SOLVER_BOOLECTOR_ENABLED
  return std::make_shared<BtorSolver>();
#else
  fmt::print(stderr, "Camada was not compiled with Boolector support, rebuild "
                     "with -DCAMADA_ENABLE_SOLVER_BOOLECTOR=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createYicesSolver() {
#if SOLVER_YICES_ENABLED
  return std::make_shared<YicesSolver>();
#else
  fmt::print(stderr, "Camada was not compiled with YICES support, rebuild with "
                     "-DCAMADA_ENABLE_SOLVER_YICES=ON\n");
  abort();
#endif
}
