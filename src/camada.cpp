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
#include "camadautils.h"

#include <bitset>

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
  abortWithMessage("Unimplemented for current type");
}

unsigned SMTSort::getFPExponentWidth() const {
  abortWithMessage("Unimplemented for current type");
}

SMTSortRef SMTSort::getIndexSort() const {
  abortWithMessage("Unimplemented for current type");
}

SMTSortRef SMTSort::getElementSort() const {
  abortWithMessage("Unimplemented for current type");
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

int64_t SMTSolver::getBV(const SMTExprRef &Exp) {
  const std::string bv = getBVInBin(Exp);
  char *buffer_end;
  int64_t res = std::strtoll(bv.c_str(), &buffer_end, 2);
  if (res & (1 << (Exp->getWidth() - 1)))
    res |= ~((1 << Exp->getWidth()) - 1);
  return res;
}

template <typename FPType, typename IntType>
static inline IntType FPAsInt(const FPType FP) {
  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  camada::abortCondWithMessage(sizeof(FPType) == sizeof(IntType),
                               "Cannot convert int to floating-point");
  IntType FPAsInt;
  memcpy(&FPAsInt, &FP, sizeof(FPType));
  return FPAsInt;
}

camada::SMTExprRef SMTSolver::mkFP32(const float Float) {
  uint32_t fp = FPAsInt<float, uint32_t>(Float);
  return mkFPFromBin(std::bitset<32>(fp).to_string(), 8);
}

camada::SMTExprRef SMTSolver::mkFP64(const double Double) {
  uint64_t fp = FPAsInt<double, uint64_t>(Double);
  return mkFPFromBin(std::bitset<64>(fp).to_string(), 11);
}

template <typename FPType, typename IntType>
static inline FPType IntAsFP(const IntType Int) {
  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  camada::abortCondWithMessage(sizeof(FPType) == sizeof(IntType),
                               "Cannot convert int to floating-point");
  FPType IntAsFP;
  memcpy(&IntAsFP, &Int, sizeof(IntType));
  return IntAsFP;
}

float SMTSolver::getFP32(const SMTExprRef &Exp) {
  char *buffer_end = nullptr;
  return IntAsFP<float, uint32_t>(
      std::strtol(getFPInBin(Exp).c_str(), &buffer_end, 2));
}

double SMTSolver::getFP64(const SMTExprRef &Exp) {
  char *buffer_end = nullptr;
  return IntAsFP<double, uint64_t>(
      std::strtol(getFPInBin(Exp).c_str(), &buffer_end, 2));
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
