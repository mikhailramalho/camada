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

camada::SMTSolverRef camada::createZ3Solver() {
#if SOLVER_Z3_ENABLED
  return new Z3Solver();
#else
  std::cerr << "Camada was not compiled with Z3 support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_Z3=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createMathSATSolver() {
#if SOLVER_MATHSAT_ENABLED
  return new MathSATSolver();
#else
  std::cerr << "Camada was not compiled with MathSAT support, rebuild "
               "with -DCAMADA_ENABLE_SOLVER_MATHSAT=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createCVC4Solver() {
#if SOLVER_CVC4_ENABLED
  return new CVC4Solver();
#else
  std::cerr << "Camada was not compiled with CVC4 support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_CVC4=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createBoolectorSolver() {
#if SOLVER_BOOLECTOR_ENABLED
  return new BtorSolver();
#else
  std::cerr << "Camada was not compiled with Boolector support, rebuild "
               "with -DCAMADA_ENABLE_SOLVER_BOOLECTOR=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createYicesSolver() {
#if SOLVER_YICES_ENABLED
  return new YicesSolver();
#else
  std::cerr << "Camada was not compiled with YICES support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_YICES=ON\n";
  abort();
#endif
}

camada::SMTSolverRef camada::createSTPSolver() {
#if SOLVER_STP_ENABLED
  return new STPSolver();
#else
  std::cerr << "Camada was not compiled with STP support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_STP=ON\n";
  abort();
#endif
}
