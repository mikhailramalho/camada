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

#if SOLVER_Z3_ENABLED
#include "z3solver.h"
#endif

#if SOLVER_MATHSAT_ENABLED
#include "mathsatsolver.h"
#endif

#if SOLVER_CVC5_ENABLED
#include "cvc5solver.h"
#endif

#if SOLVER_BITWUZLA_ENABLED
#include "bitwuzlasolver.h"
#endif

#if SOLVER_YICES_ENABLED
#include "yicessolver.h"
#endif

#if SOLVER_STP_ENABLED
#include "stpsolver.h"
#endif

namespace camada {

std::string getCamadaVersion() { return CAMADA_VERSION; }

SMTSolverRef createZ3Solver() {
#if SOLVER_Z3_ENABLED
  return std::make_unique<Z3Solver>();
#else
  std::fprintf(stderr, "Camada was not compiled with Z3 support, rebuild with "
                       "-DCAMADA_ENABLE_SOLVER_Z3=ON\n");
  abort();
#endif
}

SMTSolverRef createMathSATSolver() {
#if SOLVER_MATHSAT_ENABLED
  return std::make_unique<MathSATSolver>();
#else
  std::fprintf(stderr, "Camada was not compiled with MathSAT support, rebuild "
                       "with -DCAMADA_ENABLE_SOLVER_MATHSAT=ON\n");
  abort();
#endif
}

SMTSolverRef createCVC5Solver() {
#if SOLVER_CVC5_ENABLED
  return std::make_unique<CVC5Solver>();
#else
  std::fprintf(stderr, "Camada was not compiled with CVC5 support, rebuild "
                       "with -DCAMADA_ENABLE_SOLVER_CVC5=ON\n");
  abort();
#endif
}

SMTSolverRef createBitwuzlaSolver() {
#if SOLVER_BITWUZLA_ENABLED
  return std::make_unique<BitwuzlaSolver>();
#else
  std::fprintf(stderr, "Camada was not compiled with Bitwuzla support, rebuild "
                       "with -DCAMADA_ENABLE_SOLVER_BITWUZLA=ON\n");
  abort();
#endif
}

SMTSolverRef createYicesSolver() {
#if SOLVER_YICES_ENABLED
  return std::make_unique<YicesSolver>();
#else
  std::fprintf(stderr, "Camada was not compiled with YICES support, rebuild "
                       "with -DCAMADA_ENABLE_SOLVER_YICES=ON\n");
  abort();
#endif
}

SMTSolverRef createSTPSolver() {
#if SOLVER_STP_ENABLED
  return std::make_unique<STPSolver>();
#else
  std::fprintf(stderr, "Camada was not compiled with STP support, rebuild with "
                       "-DCAMADA_ENABLE_SOLVER_STP=ON\n");
  abort();
#endif
}

} // namespace camada
