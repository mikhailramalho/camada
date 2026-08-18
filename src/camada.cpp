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
#include "solvers/z3solver.h"
#endif

#if SOLVER_MATHSAT_ENABLED
#include "solvers/mathsatsolver.h"
#endif

#if SOLVER_CVC5_ENABLED
#include "solvers/cvc5solver.h"
#endif

#if SOLVER_BITWUZLA_ENABLED
#include "solvers/bitwuzlasolver.h"
#endif

#if SOLVER_YICES_ENABLED
#include "solvers/yicessolver.h"
#endif

#if SOLVER_STP_ENABLED
#include "solvers/stpsolver.h"
#endif

// The SMT-LIB pipeline backend has no native solver dep — it drives an
// external SMT-LIB-speaking process via fork/exec/setrlimit/select, so it
// is POSIX-only and gated behind SOLVER_SMTLIB_ENABLED.
#if SOLVER_SMTLIB_ENABLED
#include "solvers/smtlibsolver.h"
#endif

namespace camada {

std::string getCamadaVersion() { return CAMADA_VERSION; }

SMTSolverRef createZ3Solver(ArrayEncoding ArrayMode) {
#if SOLVER_Z3_ENABLED
  return std::make_unique<Z3Solver>(ArrayMode);
#else
  (void)ArrayMode;
  fatalError("Camada was not compiled with Z3 support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_Z3=ON");
#endif
}

SMTSolverRef createMathSATSolver(ArrayEncoding ArrayMode) {
#if SOLVER_MATHSAT_ENABLED
  return std::make_unique<MathSATSolver>(ArrayMode);
#else
  (void)ArrayMode;
  fatalError("Camada was not compiled with MathSAT support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_MATHSAT=ON");
#endif
}

SMTSolverRef createCVC5Solver(UnsatAssumptionsMode Mode,
                              ArrayEncoding ArrayMode) {
#if SOLVER_CVC5_ENABLED
  return std::make_unique<CVC5Solver>(Mode, ArrayMode);
#else
  (void)Mode;
  (void)ArrayMode;
  fatalError("Camada was not compiled with CVC5 support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_CVC5=ON");
#endif
}

SMTSolverRef createBitwuzlaSolver(UnsatAssumptionsMode Mode,
                                  ArrayEncoding ArrayMode) {
#if SOLVER_BITWUZLA_ENABLED
  return std::make_unique<BitwuzlaSolver>(Mode, ArrayMode);
#else
  (void)Mode;
  (void)ArrayMode;
  fatalError("Camada was not compiled with Bitwuzla support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_BITWUZLA=ON");
#endif
}

SMTSolverRef createYicesSolver(ArrayEncoding ArrayMode) {
#if SOLVER_YICES_ENABLED
  return std::make_unique<YicesSolver>(ArrayMode);
#else
  (void)ArrayMode;
  fatalError("Camada was not compiled with YICES support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_YICES=ON");
#endif
}

SMTSolverRef createSTPSolver(ArrayEncoding ArrayMode) {
#if SOLVER_STP_ENABLED
  return std::make_unique<STPSolver>(ArrayMode);
#else
  (void)ArrayMode;
  fatalError("Camada was not compiled with STP support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_STP=ON");
#endif
}

SMTSolverRef createSMTLIBSolver(const std::vector<std::string> &Argv,
                                TupleEncoding TupleMode,
                                ArrayEncoding ArrayMode) {
#if SOLVER_SMTLIB_ENABLED
  return std::make_unique<SMTLIBSolver>(SMTLIBProcessTag{}, Argv, TupleMode, "",
                                        ArrayMode);
#else
  (void)Argv;
  (void)TupleMode;
  (void)ArrayMode;
  fatalError("Camada was not compiled with the SMT-LIB pipeline backend "
             "(unsupported on this platform)");
#endif
}

SMTSolverRef createSMTLIBSolver(const std::vector<std::string> &Argv,
                                const std::string &OutputPath,
                                TupleEncoding TupleMode,
                                ArrayEncoding ArrayMode) {
#if SOLVER_SMTLIB_ENABLED
  return std::make_unique<SMTLIBSolver>(SMTLIBProcessTag{}, Argv, OutputPath,
                                        TupleMode, "", ArrayMode);
#else
  (void)Argv;
  (void)OutputPath;
  (void)TupleMode;
  (void)ArrayMode;
  fatalError("Camada was not compiled with the SMT-LIB pipeline backend "
             "(unsupported on this platform)");
#endif
}

} // namespace camada
