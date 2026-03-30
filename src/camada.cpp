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

#include <cstdio>
#include <cstdlib>

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

std::string camada::getCamadaVersion() { return CAMADA_VERSION; }

void camada::SMTSolver::invalidateGeneratedObjects() {
  clearSortCaches();
  clearExprCaches();
  ++HandleState->Generation;
  ExprArena.clear();
  SortArena.clear();
}

void camada::SMTSolver::clearSortCaches() {
  CachedBoolSort = {};
  CachedIntSort = {};
  CachedRealSort = {};
  CachedNativeRMSort = {};
  CachedEncodedRMSort = {};
  BVSortCache.clear();
  NativeFPSortCache.clear();
  EncodedFPSortCache.clear();
  ArraySortCache.clear();
  FunctionSortCache.clear();
}

void camada::SMTSolver::clearExprCaches() {
  CachedBoolExprs.fill({});
  CachedBVOne1Expr = {};
  CachedSmallBVZeroExprs.fill({});
  CachedRMBVExprs.fill({});
  CachedBVNegOneExprs.clear();
  CachedBVZeroExprs.clear();
  CachedBVOneExprs.clear();
  SymbolExprCache.clear();
  FPSpecialExprCache.clear();
}

void camada::SMTSolver::initializeCommonSingletons() {
  CachedBoolExprs[0] = mkBool(false);
  CachedBoolExprs[1] = mkBool(true);
  CachedBVOne1Expr = mkBVFromBin("1", 1);
  CachedSmallBVZeroExprs[1] = mkBVFromBin("0", 1);
  CachedSmallBVZeroExprs[2] = mkBVFromBin("00", 2);
  CachedSmallBVZeroExprs[3] = mkBVFromBin("000", 3);
  CachedSmallBVZeroExprs[4] = mkBVFromBin("0000", 4);
  CachedBVZeroExprs.resize(5);
  CachedBVZeroExprs[1] = CachedSmallBVZeroExprs[1];
  CachedBVZeroExprs[2] = CachedSmallBVZeroExprs[2];
  CachedBVZeroExprs[3] = CachedSmallBVZeroExprs[3];
  CachedBVZeroExprs[4] = CachedSmallBVZeroExprs[4];
  CachedBVOneExprs.resize(2);
  CachedBVOneExprs[1] = CachedBVOne1Expr;
  CachedBVNegOneExprs.resize(2);
  CachedBVNegOneExprs[1] = CachedBVOne1Expr;
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_EVEN)] =
      mkBVFromBin("000", 3);
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_AWAY)] =
      mkBVFromBin("001", 3);
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_PLUS_INF)] =
      mkBVFromBin("010", 3);
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_MINUS_INF)] =
      mkBVFromBin("011", 3);
  CachedRMBVExprs[static_cast<std::size_t>(RM::ROUND_TO_ZERO)] =
      mkBVFromBin("100", 3);
}

camada::SMTSolverRef camada::createZ3Solver() {
#if SOLVER_Z3_ENABLED
  return std::make_unique<Z3Solver>();
#else
  std::fprintf(stderr, "Camada was not compiled with Z3 support, rebuild with "
                       "-DCAMADA_ENABLE_SOLVER_Z3=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createMathSATSolver() {
#if SOLVER_MATHSAT_ENABLED
  return std::make_unique<MathSATSolver>();
#else
  std::fprintf(stderr,
               "Camada was not compiled with MathSAT support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_MATHSAT=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createCVC5Solver() {
#if SOLVER_CVC5_ENABLED
  return std::make_unique<CVC5Solver>();
#else
  std::fprintf(stderr,
               "Camada was not compiled with CVC5 support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_CVC5=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createBitwuzlaSolver() {
#if SOLVER_BITWUZLA_ENABLED
  return std::make_unique<BitwuzlaSolver>();
#else
  std::fprintf(stderr,
               "Camada was not compiled with Bitwuzla support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_BITWUZLA=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createYicesSolver() {
#if SOLVER_YICES_ENABLED
  return std::make_unique<YicesSolver>();
#else
  std::fprintf(stderr,
               "Camada was not compiled with YICES support, rebuild with "
               "-DCAMADA_ENABLE_SOLVER_YICES=ON\n");
  abort();
#endif
}

camada::SMTSolverRef camada::createSTPSolver() {
#if SOLVER_STP_ENABLED
  return std::make_unique<STPSolver>();
#else
  std::fprintf(stderr, "Camada was not compiled with STP support, rebuild with "
                       "-DCAMADA_ENABLE_SOLVER_STP=ON\n");
  abort();
#endif
}
