#include "ac_config.h"
#include "camada.h"

#if SOLVER_SMTLIB_ENABLED
#include "smtlibsolver.h"
#endif

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iomanip>
#include <stdexcept>
#include <string>
#include <unistd.h>
#include <utility>
#include <vector>

namespace {

using Clock = std::chrono::steady_clock;

std::size_t readCurrentRSSKiB() {
  std::ifstream Statm("/proc/self/statm");
  std::size_t total_pages = 0;
  std::size_t resident_pages = 0;
  if (!(Statm >> total_pages >> resident_pages))
    throw std::runtime_error("Failed to read /proc/self/statm");

  const long page_size = sysconf(_SC_PAGESIZE);
  if (page_size <= 0)
    throw std::runtime_error("Failed to read page size");

  return (resident_pages * static_cast<std::size_t>(page_size)) / 1024;
}

// Array encoding applied to the chosen backend (--ack flag).
camada::ArrayEncoding arrayMode = camada::ArrayEncoding::Native;

camada::SMTSolverRef createSolver(const std::string &backend) {
  if (backend == "bitwuzla") {
#if SOLVER_BITWUZLA_ENABLED
    return camada::createBitwuzlaSolver(camada::UnsatAssumptionsMode::Off,
                                        arrayMode);
#else
    throw std::runtime_error("Bitwuzla backend is not enabled");
#endif
  }

  if (backend == "cvc5") {
#if SOLVER_CVC5_ENABLED
    return camada::createCVC5Solver(camada::UnsatAssumptionsMode::Off,
                                    arrayMode);
#else
    throw std::runtime_error("CVC5 backend is not enabled");
#endif
  }

  if (backend == "mathsat") {
#if SOLVER_MATHSAT_ENABLED
    return camada::createMathSATSolver(arrayMode);
#else
    throw std::runtime_error("MathSAT backend is not enabled");
#endif
  }

  if (backend == "stp") {
#if SOLVER_STP_ENABLED
    return camada::createSTPSolver(arrayMode);
#else
    throw std::runtime_error("STP backend is not enabled");
#endif
  }

  if (backend == "yices") {
#if SOLVER_YICES_ENABLED
    return camada::createYicesSolver(arrayMode);
#else
    throw std::runtime_error("Yices backend is not enabled");
#endif
  }

  if (backend == "z3") {
#if SOLVER_Z3_ENABLED
    return camada::createZ3Solver(arrayMode);
#else
    throw std::runtime_error("Z3 backend is not enabled");
#endif
  }

  if (backend == "smtlib") {
#if SOLVER_SMTLIB_ENABLED
    // Write-only mode to /dev/null: measures the text-emission layer without
    // a child solver. The bench cases are construction-only, so the UNKNOWN
    // check() result in this mode is irrelevant.
    return std::make_unique<camada::SMTLIBSolver>(
        "/dev/null", camada::TupleEncoding::Native, "", arrayMode);
#else
    throw std::runtime_error("SMTLIB backend is not enabled");
#endif
  }

  throw std::runtime_error("Unknown backend: " + backend);
}

std::string defaultBackend() {
#if SOLVER_BITWUZLA_ENABLED
  return "bitwuzla";
#elif SOLVER_CVC5_ENABLED
  return "cvc5";
#elif SOLVER_Z3_ENABLED
  return "z3";
#elif SOLVER_MATHSAT_ENABLED
  return "mathsat";
#elif SOLVER_STP_ENABLED
  return "stp";
#elif SOLVER_YICES_ENABLED
  return "yices";
#else
  throw std::runtime_error("No solver backend is enabled");
#endif
}

bool backendSupportsTuples(const std::string &backend) {
  return backend == "cvc5" || backend == "z3" || backend == "smtlib";
}

// STP has no uninterpreted functions; mkFunctionSort aborts there.
bool backendSupportsUF(const std::string &backend) { return backend != "stp"; }

// Optional substring filter on benchmark case names (third CLI argument).
// Empty means "run everything".
std::string caseFilter;
std::size_t casesRun = 0;

void runCase(const std::string &backend, const std::string &name,
             std::size_t iterations,
             const std::function<void(camada::SMTSolver &, std::size_t)> &fn) {
  if (!caseFilter.empty() && name.find(caseFilter) == std::string::npos)
    return;
  ++casesRun;
  const std::size_t rss_before_kb = readCurrentRSSKiB();
  auto start = Clock::now();
  {
    auto solver = createSolver(backend);
    fn(*solver, iterations);
  }
  auto end = Clock::now();
  const std::size_t rss_after_kb = readCurrentRSSKiB();

  auto total_ns =
      std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
  auto per_iter_ns =
      iterations == 0 ? 0.0 : static_cast<double>(total_ns) / iterations;
  const long long rss_delta_kb = static_cast<long long>(rss_after_kb) -
                                 static_cast<long long>(rss_before_kb);

  std::printf(
      "benchmark=%s backend=%s iterations=%zu total_ns=%lld ns_per_iter=%.*f "
      "rss_after_kb=%zu rss_delta_kb=%lld\n",
      name.c_str(), backend.c_str(), iterations,
      static_cast<long long>(total_ns), 2, per_iter_ns, rss_after_kb,
      rss_delta_kb);
}

void benchmarkBVSort(camada::SMTSolver &solver, std::size_t iterations) {
  volatile std::size_t sink = 0;
  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkBVSort(32)->getWidth();
  (void)sink;
}

void benchmarkBVConstSame(camada::SMTSolver &solver, std::size_t iterations) {
  volatile std::size_t sink = 0;
  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkBVFromDec(0, 32)->getWidth();
  (void)sink;
}

void benchmarkBVConstVaried(camada::SMTSolver &solver, std::size_t iterations) {
  volatile std::size_t sink = 0;
  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkBVFromDec(static_cast<int64_t>(i & 0xff), 32)->getWidth();
  (void)sink;
}

void benchmarkBVExprChain(camada::SMTSolver &solver, std::size_t iterations) {
  auto x = solver.mkSymbol("bench_x", solver.mkBVSort(32));
  auto y = solver.mkSymbol("bench_y", solver.mkBVSort(32));
  auto expr = x;

  for (std::size_t i = 0; i < iterations; ++i) {
    auto c = solver.mkBVFromDec(static_cast<int64_t>(i & 0x7f), 32);
    expr = solver.mkBVAdd(expr, y);
    expr = solver.mkBVXor(expr, c);
    expr = solver.mkBVMul(expr, solver.mkBVFromDec(3, 32));
  }

  volatile std::size_t sink = expr->getWidth();
  (void)sink;
}

void benchmarkExprConstructionOnly(camada::SMTSolver &solver,
                                   std::size_t iterations) {
  auto x = solver.mkSymbol("construct_x", solver.mkBVSort(32));
  auto y = solver.mkSymbol("construct_y", solver.mkBVSort(32));
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i) {
    auto c0 = solver.mkBVFromDec(static_cast<int64_t>(i & 0xff), 32);
    auto c1 = solver.mkBVFromDec(static_cast<int64_t>((i + 1) & 0xff), 32);
    auto c2 = solver.mkBVFromDec(static_cast<int64_t>((i + 3) & 0xff), 32);

    auto add = solver.mkBVAdd(x, c0);
    auto mul = solver.mkBVMul(add, y);
    auto xor_term = solver.mkBVXor(mul, c1);
    auto sub = solver.mkBVSub(xor_term, c2);
    auto and_term = solver.mkBVAnd(sub, solver.mkBVNot(c0));
    auto eq = solver.mkEqual(and_term, solver.mkBVOr(c1, c2));
    auto ite = solver.mkIte(eq, solver.mkBVAdd(and_term, c1),
                            solver.mkBVXor(and_term, c2));

    sink += ite->getWidth() + eq->isBoolSort();
  }

  (void)sink;
}

void benchmarkArrayStoreChain(camada::SMTSolver &solver,
                              std::size_t iterations) {
  auto idx_sort = solver.mkBVSort(8);
  auto elem_sort = solver.mkBVSort(32);
  auto init = solver.mkBVFromDec(0, elem_sort);
  auto array = solver.mkArrayConst(idx_sort, init);

  for (std::size_t i = 0; i < iterations; ++i) {
    auto idx = solver.mkBVFromDec(static_cast<int64_t>(i & 0xff), idx_sort);
    auto val = solver.mkBVFromDec(static_cast<int64_t>(i), elem_sort);
    array = solver.mkArrayStore(array, idx, val);
  }

  auto last_idx = solver.mkBVFromDec(
      static_cast<int64_t>((iterations - 1) & 0xff), idx_sort);
  volatile std::size_t sink = solver.mkArraySelect(array, last_idx)->getWidth();
  (void)sink;
}

// Unlike the construction-only cases, this one calls check(): the array
// encoding trade (native theory vs Ackermann ground constraints) only
// shows up in solve time. Each cycle builds a small store chain, a few
// symbolic reads with equalities, solves, and resets.
void benchmarkArraySolve(camada::SMTSolver &solver, std::size_t iterations) {
  volatile std::size_t sink = 0;

  for (std::size_t cycle = 0; cycle < iterations; ++cycle) {
    auto idx_sort = solver.mkBVSort(8);
    auto elem_sort = solver.mkBVSort(32);
    auto array =
        solver.mkSymbol("solve_a", solver.mkArraySort(idx_sort, elem_sort));
    for (std::size_t i = 0; i < 16; ++i)
      array = solver.mkArrayStore(
          array, solver.mkBVFromDec(static_cast<int64_t>(i), idx_sort),
          solver.mkBVFromDec(static_cast<int64_t>(i * 3), elem_sort));

    for (std::size_t r = 0; r < 4; ++r) {
      auto k = solver.mkSymbol("solve_k" + std::to_string(r), idx_sort);
      solver.addConstraint(solver.mkBVUlt(
          solver.mkArraySelect(array, k),
          solver.mkBVFromDec(static_cast<int64_t>(40 + r), elem_sort)));
    }

    sink += solver.check() == camada::checkResult::SAT;
    solver.reset();
  }

  (void)sink;
}

void benchmarkFunctionSortCacheHit(camada::SMTSolver &solver,
                                   std::size_t iterations) {
  auto bv8 = solver.mkBVSort(8);
  auto bv16 = solver.mkBVSort(16);
  auto bv32 = solver.mkBVSort(32);
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  std::vector<camada::SMTSortRef> domain{bv8, bv16, bv32};
  solver.mkFunctionSort(domain, fp32);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFunctionSort(domain, fp32)->getDomainSorts().size();

  (void)sink;
}

void benchmarkTupleSortCacheHit(camada::SMTSolver &solver,
                                std::size_t iterations) {
  auto bv8 = solver.mkBVSort(8);
  auto bv16 = solver.mkBVSort(16);
  auto bv32 = solver.mkBVSort(32);
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  std::vector<camada::SMTSortRef> elements{bv8, bv16, bv32, fp32};
  solver.mkTupleSort(elements);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkTupleSort(elements)->getTupleElementSorts().size();

  (void)sink;
}

void benchmarkFPConstruct(camada::SMTSolver &solver, std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i) {
    auto a_bv = solver.mkBVFromDec(static_cast<int64_t>((i & 0xffff) + 1), 32);
    auto b_bv =
        solver.mkBVFromDec(static_cast<int64_t>(((i + 3) & 0xffff) + 1), 32);
    auto a = solver.mkSBVtoFP(a_bv, fp32, rm);
    auto b = solver.mkUBVtoFP(b_bv, fp32, rm);
    auto sum = solver.mkFPAdd(a, b, rm);
    auto div =
        solver.mkFPDiv(sum, solver.mkFP32(3.5f, camada::FPEncoding::BV), rm);
    auto integral = solver.mkFPtoIntegral(div, rm);
    sink += solver.mkIEEEFPToBV(integral)->getWidth();
  }

  (void)sink;
}

void benchmarkFPFromBV(camada::SMTSolver &solver, std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i) {
    auto a_bv = solver.mkBVFromDec(static_cast<int64_t>((i & 0xffff) + 1), 32);
    auto b_bv =
        solver.mkBVFromDec(static_cast<int64_t>(((i + 3) & 0xffff) + 1), 32);
    auto a = solver.mkSBVtoFP(a_bv, fp32, rm);
    auto b = solver.mkUBVtoFP(b_bv, fp32, rm);
    sink += a->getWidth() + b->getWidth();
  }

  (void)sink;
}

void benchmarkFPAddOnly(camada::SMTSolver &solver, std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  auto a = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto b = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPAdd(a, b, rm)->getWidth();

  (void)sink;
}

void benchmarkFPDivOnly(camada::SMTSolver &solver, std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  auto a = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto b = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  auto sum = solver.mkFPAdd(a, b, rm);
  auto denom = solver.mkFP32(3.5f, camada::FPEncoding::BV);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPDiv(sum, denom, rm)->getWidth();

  (void)sink;
}

void benchmarkFPIntegralOnly(camada::SMTSolver &solver,
                             std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  auto a = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto b = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  auto sum = solver.mkFPAdd(a, b, rm);
  auto div =
      solver.mkFPDiv(sum, solver.mkFP32(3.5f, camada::FPEncoding::BV), rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPtoIntegral(div, rm)->getWidth();

  (void)sink;
}

void benchmarkFPIEEEToBVOnly(camada::SMTSolver &solver,
                             std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  auto a = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto b = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  auto sum = solver.mkFPAdd(a, b, rm);
  auto div =
      solver.mkFPDiv(sum, solver.mkFP32(3.5f, camada::FPEncoding::BV), rm);
  auto integral = solver.mkFPtoIntegral(div, rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkIEEEFPToBV(integral)->getWidth();

  (void)sink;
}

void benchmarkFPSqrtOnly(camada::SMTSolver &solver, std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  auto a = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPSqrt(a, rm)->getWidth();

  (void)sink;
}

void benchmarkFPFMAOnly(camada::SMTSolver &solver, std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  auto x = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto y = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  auto z = solver.mkFP32(1.25f, camada::FPEncoding::BV);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPFMA(x, y, z, rm)->getWidth();

  (void)sink;
}

void benchmarkFPRemOnly(camada::SMTSolver &solver, std::size_t iterations) {
  auto fp32 = solver.mkFP32Sort(camada::FPEncoding::BV);
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
  auto x = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto y = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPRem(x, y)->getWidth();

  (void)sink;
}

// Solve-time FP case: proving add commutativity UNSAT drags the solver
// through the whole bit-blasted adder -- unpack, alignment, rounding and
// the renormalization leading-zero count -- on two symbolic operands.
// Encoding-structure changes (e.g. chain vs tree lzc) only show up in
// solve time, never in the construction-only fp cases above.
void benchmarkFPSolveAdd(camada::SMTSolver &solver, std::size_t iterations) {
  volatile std::size_t sink = 0;

  for (std::size_t cycle = 0; cycle < iterations; ++cycle) {
    // A toy 8-bit format: the same circuit structure as fp32, but the
    // proof stays in the milliseconds range (fp32 takes seconds per
    // check, fp16 still ~2s).
    auto fp8 = solver.mkFPSort(4, 3, camada::FPEncoding::BV);
    auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
    auto x = solver.mkSymbol("fp_solve_x", fp8);
    auto y = solver.mkSymbol("fp_solve_y", fp8);
    auto lhs = solver.mkFPAdd(x, y, rm);
    auto rhs = solver.mkFPAdd(y, x, rm);
    solver.addConstraint(solver.mkNot(solver.mkEqual(lhs, rhs)));
    sink += solver.check() == camada::checkResult::UNSAT;
    solver.reset();
  }

  (void)sink;
}

// fma(x,y,z) == fma(y,x,z): the product is commutative, so proving the
// negation UNSAT forces both FMA circuits (alignment, sticky handling,
// renormalization) end to end.
void benchmarkFPSolveFMA(camada::SMTSolver &solver, std::size_t iterations) {
  volatile std::size_t sink = 0;

  for (std::size_t cycle = 0; cycle < iterations; ++cycle) {
    auto fp8 = solver.mkFPSort(4, 3, camada::FPEncoding::BV);
    auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
    auto x = solver.mkSymbol("fp_solve_x", fp8);
    auto y = solver.mkSymbol("fp_solve_y", fp8);
    auto z = solver.mkSymbol("fp_solve_z", fp8);
    auto lhs = solver.mkFPFMA(x, y, z, rm);
    auto rhs = solver.mkFPFMA(y, x, z, rm);
    solver.addConstraint(solver.mkNot(solver.mkEqual(lhs, rhs)));
    sink += solver.check() == camada::checkResult::UNSAT;
    solver.reset();
  }

  (void)sink;
}

// Correctly rounded sqrt is weakly monotone: 0 <= x <= y implies
// sqrt(x) <= sqrt(y). Proving the negation UNSAT forces two sqrt
// digit-recurrence circuits plus the comparison logic.
void benchmarkFPSolveSqrt(camada::SMTSolver &solver, std::size_t iterations) {
  volatile std::size_t sink = 0;

  for (std::size_t cycle = 0; cycle < iterations; ++cycle) {
    auto fp8 = solver.mkFPSort(4, 3, camada::FPEncoding::BV);
    auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
    auto x = solver.mkSymbol("fp_solve_x", fp8);
    auto y = solver.mkSymbol("fp_solve_y", fp8);
    auto zero =
        solver.mkFPFromBin(std::string(8, '0'), 4, camada::FPEncoding::BV);
    solver.addConstraint(solver.mkFPLe(zero, x));
    solver.addConstraint(solver.mkFPLe(x, y));
    solver.addConstraint(solver.mkNot(
        solver.mkFPLe(solver.mkFPSqrt(x, rm), solver.mkFPSqrt(y, rm))));
    sink += solver.check() == camada::checkResult::UNSAT;
    solver.reset();
  }

  (void)sink;
}

// IEEE remainder ignores the divisor's sign: rem(x, y) == rem(x, -y).
// Proving the negation UNSAT forces two remainder circuits end to end.
void benchmarkFPSolveRem(camada::SMTSolver &solver, std::size_t iterations) {
  volatile std::size_t sink = 0;

  for (std::size_t cycle = 0; cycle < iterations; ++cycle) {
    auto fp8 = solver.mkFPSort(4, 3, camada::FPEncoding::BV);
    auto x = solver.mkSymbol("fp_solve_x", fp8);
    auto y = solver.mkSymbol("fp_solve_y", fp8);
    auto lhs = solver.mkFPRem(x, y);
    auto rhs = solver.mkFPRem(x, solver.mkFPNeg(y));
    solver.addConstraint(solver.mkNot(solver.mkEqual(lhs, rhs)));
    sink += solver.check() == camada::checkResult::UNSAT;
    solver.reset();
  }

  (void)sink;
}

void benchmarkResetCycleMemory(camada::SMTSolver &solver,
                               std::size_t iterations) {
  volatile std::size_t sink = 0;

  for (std::size_t cycle = 0; cycle < iterations; ++cycle) {
    auto x = solver.mkSymbol("reset_x", solver.mkBVSort(32));
    auto y = solver.mkSymbol("reset_y", solver.mkBVSort(32));
    auto expr = x;

    // Build a moderate expression tree each cycle to force arena growth.
    for (std::size_t i = 0; i < 200; ++i) {
      auto c = solver.mkBVFromDec(static_cast<int64_t>(i & 0x7f), 32);
      expr = solver.mkBVAdd(expr, y);
      expr = solver.mkBVXor(expr, c);
      expr = solver.mkBVMul(expr, solver.mkBVFromDec(3, 32));
    }

    sink += expr->getWidth();
    solver.reset();
  }

  (void)sink;
}

void benchmarkResetCycleExprChain(camada::SMTSolver &solver,
                                  std::size_t iterations) {
  volatile std::size_t sink = 0;

  for (std::size_t cycle = 0; cycle < iterations; ++cycle) {
    auto x = solver.mkSymbol("chain_x", solver.mkBVSort(32));
    auto y = solver.mkSymbol("chain_y", solver.mkBVSort(32));

    // Build a wider expression tree to stress arena allocation.
    for (std::size_t i = 0; i < 200; ++i) {
      auto c0 = solver.mkBVFromDec(static_cast<int64_t>(i & 0xff), 32);
      auto c1 = solver.mkBVFromDec(static_cast<int64_t>((i + 1) & 0xff), 32);
      auto c2 = solver.mkBVFromDec(static_cast<int64_t>((i + 3) & 0xff), 32);

      auto add = solver.mkBVAdd(x, c0);
      auto mul = solver.mkBVMul(add, y);
      auto xor_term = solver.mkBVXor(mul, c1);
      auto sub = solver.mkBVSub(xor_term, c2);
      auto and_term = solver.mkBVAnd(sub, solver.mkBVNot(c0));
      auto eq = solver.mkEqual(and_term, solver.mkBVOr(c1, c2));
      auto ite = solver.mkIte(eq, solver.mkBVAdd(and_term, c1),
                              solver.mkBVXor(and_term, c2));

      sink += ite->getWidth() + eq->isBoolSort();
    }

    solver.reset();
  }

  (void)sink;
}

void printUsage(const char *argv0) {
  std::fprintf(stderr,
               "Usage: %s [--ack] [backend] [iterations] [case-substring]\n"
               "Backends: bitwuzla cvc5 mathsat stp yices z3 smtlib\n"
               "  --ack  use the Ackermann array encoding "
               "(ArrayEncoding::Ackermann)\n",
               argv0);
}

} // namespace

int main(int argc, char **argv) {
  try {
    std::vector<std::string> args;
    for (int i = 1; i < argc; ++i) {
      if (std::string(argv[i]) == "--ack")
        arrayMode = camada::ArrayEncoding::Ackermann;
      else
        args.emplace_back(argv[i]);
    }

    std::string backend = !args.empty() ? args[0] : defaultBackend();
    std::size_t iterations =
        args.size() > 1 ? static_cast<std::size_t>(
                              std::strtoull(args[1].c_str(), nullptr, 10))
                        : 1000;

    if (iterations == 0)
      throw std::runtime_error("iterations must be greater than zero");

    if (args.size() > 2)
      caseFilter = args[2];

    runCase(backend, "bv_sort_same", iterations, benchmarkBVSort);
    runCase(backend, "bv_const_same", iterations, benchmarkBVConstSame);
    runCase(backend, "bv_const_varied", iterations, benchmarkBVConstVaried);
    runCase(backend, "bv_expr_chain", iterations, benchmarkBVExprChain);
    runCase(backend, "expr_construction_only", iterations,
            benchmarkExprConstructionOnly);
    runCase(backend, "array_store_chain", iterations, benchmarkArrayStoreChain);
    // Write-only smtlib never solves; array_solve would just measure text
    // emission there.
    if (backend != "smtlib")
      runCase(backend, "array_solve", iterations, benchmarkArraySolve);
    if (backendSupportsUF(backend))
      runCase(backend, "function_sort_cache_hit", iterations,
              benchmarkFunctionSortCacheHit);
    if (backendSupportsTuples(backend))
      runCase(backend, "tuple_sort_cache_hit", iterations,
              benchmarkTupleSortCacheHit);
    runCase(backend, "fp_from_bv", iterations, benchmarkFPFromBV);
    runCase(backend, "fp_add_only", iterations, benchmarkFPAddOnly);
    runCase(backend, "fp_div_only", iterations, benchmarkFPDivOnly);
    runCase(backend, "fp_integral_only", iterations, benchmarkFPIntegralOnly);
    runCase(backend, "fp_ieee_to_bv_only", iterations, benchmarkFPIEEEToBVOnly);
    runCase(backend, "fp_sqrt_only", iterations, benchmarkFPSqrtOnly);
    runCase(backend, "fp_fma_only", iterations, benchmarkFPFMAOnly);
    runCase(backend, "fp_rem_only", iterations, benchmarkFPRemOnly);
    runCase(backend, "fp_construct", iterations, benchmarkFPConstruct);
    // One check() per iteration and each is a real UNSAT proof, so this
    // case runs at 1/100th of the requested iterations to keep the
    // default run's wall clock sane.
    if (backend != "smtlib") {
      const std::size_t solveIters = std::max<std::size_t>(1, iterations / 100);
      runCase(backend, "fp_solve_add", solveIters, benchmarkFPSolveAdd);
      runCase(backend, "fp_solve_fma", solveIters, benchmarkFPSolveFMA);
      runCase(backend, "fp_solve_sqrt", solveIters, benchmarkFPSolveSqrt);
      runCase(backend, "fp_solve_rem", solveIters, benchmarkFPSolveRem);
    }
    runCase(backend, "reset_cycle_memory", iterations,
            benchmarkResetCycleMemory);
    runCase(backend, "reset_cycle_expr_chain", iterations,
            benchmarkResetCycleExprChain);

    if (casesRun == 0) {
      std::fprintf(stderr, "No benchmark case matched filter '%s'\n",
                   caseFilter.c_str());
      return 1;
    }
    return 0;
  } catch (const std::exception &Exn) {
    std::fprintf(stderr, "%s\n", Exn.what());
    printUsage(argv[0]);
    return 1;
  }
}
