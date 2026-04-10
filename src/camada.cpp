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
#include "camadaerror.h"

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
  fatalError("Camada was not compiled with Z3 support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_Z3=ON");
#endif
}

SMTSolverRef createMathSATSolver() {
#if SOLVER_MATHSAT_ENABLED
  return std::make_unique<MathSATSolver>();
#else
  fatalError("Camada was not compiled with MathSAT support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_MATHSAT=ON");
#endif
}

SMTSolverRef createCVC5Solver() {
#if SOLVER_CVC5_ENABLED
  return std::make_unique<CVC5Solver>();
#else
  fatalError("Camada was not compiled with CVC5 support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_CVC5=ON");
#endif
}

SMTSolverRef createBitwuzlaSolver() {
#if SOLVER_BITWUZLA_ENABLED
  return std::make_unique<BitwuzlaSolver>();
#else
  fatalError("Camada was not compiled with Bitwuzla support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_BITWUZLA=ON");
#endif
}

SMTSolverRef createYicesSolver() {
#if SOLVER_YICES_ENABLED
  return std::make_unique<YicesSolver>();
#else
  fatalError("Camada was not compiled with YICES support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_YICES=ON");
#endif
}

SMTSolverRef createSTPSolver() {
#if SOLVER_STP_ENABLED
  return std::make_unique<STPSolver>();
#else
  fatalError("Camada was not compiled with STP support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_STP=ON");
#endif
}

} // namespace camada
