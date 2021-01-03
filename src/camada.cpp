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

#include <bitset>
#include <cassert>
#include <cstring>
#include <iostream>

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

#if SOLVER_STP_ENABLED
#include "stpsolver.h"
#endif

std::string camada::getCamadaVersion() { return CAMADA_VERSION; }

camada::SMTSolver::SMTSolver() = default;

camada::SMTSolver::~SMTSolver() = default;

void camada::SMTSolver::dump() {
  std::cerr << "SMTSolver dump not implemented.\n";
}

void camada::SMTSolver::dumpModel() {
  std::cerr << "SMTSolver model dump not implemented.\n";
}

int64_t camada::SMTSolver::getBV(const SMTExprRef &Exp) {
  const std::string bv = getBVInBin(Exp);
  char *buffer_end;
  uint64_t res = std::strtoull(bv.c_str(), &buffer_end, 2);
  if (res & (1ULL << (Exp->getWidth() - 1)))
    res |= ~((1ULL << Exp->getWidth()) - 1);
  return res;
}

template <typename FPType, typename IntType>
static inline IntType FPAsInt(const FPType FP) {
  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  assert(sizeof(FPType) == sizeof(IntType) &&
         "Cannot convert int to floating-point");

  IntType FPAsInt;
  memcpy(&FPAsInt, &FP, sizeof(FPType));
  return FPAsInt;
}

camada::SMTExprRef camada::SMTSolver::mkFP32(const float Float) {
  uint32_t fp = FPAsInt<float, uint32_t>(Float);
  return mkFPFromBin(std::bitset<32>(fp).to_string(), 8);
}

camada::SMTExprRef camada::SMTSolver::mkFP64(const double Double) {
  uint64_t fp = FPAsInt<double, uint64_t>(Double);
  return mkFPFromBin(std::bitset<64>(fp).to_string(), 11);
}

template <typename FPType, typename IntType>
static inline FPType IntAsFP(const IntType Int) {
  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  assert(sizeof(FPType) == sizeof(IntType) &&
         "Cannot convert int to floating-point");

  FPType IntAsFP;
  memcpy(&IntAsFP, &Int, sizeof(IntType));
  return IntAsFP;
}

float camada::SMTSolver::getFP32(const SMTExprRef &Exp) {
  char *buffer_end = nullptr;
  return IntAsFP<float, uint32_t>(
      std::strtol(getFPInBin(Exp).c_str(), &buffer_end, 2));
}

double camada::SMTSolver::getFP64(const SMTExprRef &Exp) {
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

camada::SMTSolverRef camada::createSTPSolver() {
#if SOLVER_STP_ENABLED
  return std::make_shared<STPSolver>();
#else
  std::cerr << "Camada was not compiled with STP support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_STP=ON\n";
  abort();
#endif
}
