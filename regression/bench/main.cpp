#include "ac_config.h"
#include "camada.h"

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <iomanip>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

using Clock = std::chrono::steady_clock;

camada::SMTSolverRef createSolver(const std::string &backend) {
  if (backend == "bitwuzla") {
#if SOLVER_BITWUZLA_ENABLED
    return camada::createBitwuzlaSolver();
#else
    throw std::runtime_error("Bitwuzla backend is not enabled");
#endif
  }

  if (backend == "cvc5") {
#if SOLVER_CVC5_ENABLED
    return camada::createCVC5Solver();
#else
    throw std::runtime_error("CVC5 backend is not enabled");
#endif
  }

  if (backend == "mathsat") {
#if SOLVER_MATHSAT_ENABLED
    return camada::createMathSATSolver();
#else
    throw std::runtime_error("MathSAT backend is not enabled");
#endif
  }

  if (backend == "stp") {
#if SOLVER_STP_ENABLED
    return camada::createSTPSolver();
#else
    throw std::runtime_error("STP backend is not enabled");
#endif
  }

  if (backend == "yices") {
#if SOLVER_YICES_ENABLED
    return camada::createYicesSolver();
#else
    throw std::runtime_error("Yices backend is not enabled");
#endif
  }

  if (backend == "z3") {
#if SOLVER_Z3_ENABLED
    return camada::createZ3Solver();
#else
    throw std::runtime_error("Z3 backend is not enabled");
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

void runCase(const std::string &backend, const std::string &name,
             std::size_t iterations,
             const std::function<void(camada::SMTSolver &, std::size_t)> &fn) {
  auto solver = createSolver(backend);
  auto start = Clock::now();
  fn(*solver, iterations);
  auto end = Clock::now();

  auto total_ns =
      std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
  auto per_iter_ns =
      iterations == 0 ? 0.0 : static_cast<double>(total_ns) / iterations;

  std::printf(
      "benchmark=%s backend=%s iterations=%zu total_ns=%lld ns_per_iter=%.*f\n",
      name.c_str(), backend.c_str(), iterations,
      static_cast<long long>(total_ns), 2, per_iter_ns);
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

void benchmarkFPConstruct(camada::SMTSolver &solver, std::size_t iterations) {
  bool old_use_camada_fp = solver.useCamadaFP;
  solver.useCamadaFP = true;

  auto fp32 = solver.mkFP32Sort();
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i) {
    auto a_bv = solver.mkBVFromDec(static_cast<int64_t>((i & 0xffff) + 1), 32);
    auto b_bv =
        solver.mkBVFromDec(static_cast<int64_t>(((i + 3) & 0xffff) + 1), 32);
    auto a = solver.mkSBVtoFP(a_bv, fp32, rm);
    auto b = solver.mkUBVtoFP(b_bv, fp32, rm);
    auto sum = solver.mkFPAdd(a, b, rm);
    auto div = solver.mkFPDiv(sum, solver.mkFP32(3.5f), rm);
    auto integral = solver.mkFPtoIntegral(div, rm);
    sink += solver.mkIEEEFPToBV(integral)->getWidth();
  }

  solver.useCamadaFP = old_use_camada_fp;
  (void)sink;
}

void benchmarkFPFromBV(camada::SMTSolver &solver, std::size_t iterations) {
  bool old_use_camada_fp = solver.useCamadaFP;
  solver.useCamadaFP = true;

  auto fp32 = solver.mkFP32Sort();
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i) {
    auto a_bv = solver.mkBVFromDec(static_cast<int64_t>((i & 0xffff) + 1), 32);
    auto b_bv =
        solver.mkBVFromDec(static_cast<int64_t>(((i + 3) & 0xffff) + 1), 32);
    auto a = solver.mkSBVtoFP(a_bv, fp32, rm);
    auto b = solver.mkUBVtoFP(b_bv, fp32, rm);
    sink += a->getWidth() + b->getWidth();
  }

  solver.useCamadaFP = old_use_camada_fp;
  (void)sink;
}

void benchmarkFPAddOnly(camada::SMTSolver &solver, std::size_t iterations) {
  bool old_use_camada_fp = solver.useCamadaFP;
  solver.useCamadaFP = true;

  auto fp32 = solver.mkFP32Sort();
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN);
  auto a = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto b = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPAdd(a, b, rm)->getWidth();

  solver.useCamadaFP = old_use_camada_fp;
  (void)sink;
}

void benchmarkFPDivOnly(camada::SMTSolver &solver, std::size_t iterations) {
  bool old_use_camada_fp = solver.useCamadaFP;
  solver.useCamadaFP = true;

  auto fp32 = solver.mkFP32Sort();
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN);
  auto a = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto b = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  auto sum = solver.mkFPAdd(a, b, rm);
  auto denom = solver.mkFP32(3.5f);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPDiv(sum, denom, rm)->getWidth();

  solver.useCamadaFP = old_use_camada_fp;
  (void)sink;
}

void benchmarkFPIntegralOnly(camada::SMTSolver &solver,
                             std::size_t iterations) {
  bool old_use_camada_fp = solver.useCamadaFP;
  solver.useCamadaFP = true;

  auto fp32 = solver.mkFP32Sort();
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN);
  auto a = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto b = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  auto sum = solver.mkFPAdd(a, b, rm);
  auto div = solver.mkFPDiv(sum, solver.mkFP32(3.5f), rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPtoIntegral(div, rm)->getWidth();

  solver.useCamadaFP = old_use_camada_fp;
  (void)sink;
}

void benchmarkFPIEEEToBVOnly(camada::SMTSolver &solver,
                             std::size_t iterations) {
  bool old_use_camada_fp = solver.useCamadaFP;
  solver.useCamadaFP = true;

  auto fp32 = solver.mkFP32Sort();
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN);
  auto a = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto b = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  auto sum = solver.mkFPAdd(a, b, rm);
  auto div = solver.mkFPDiv(sum, solver.mkFP32(3.5f), rm);
  auto integral = solver.mkFPtoIntegral(div, rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkIEEEFPToBV(integral)->getWidth();

  solver.useCamadaFP = old_use_camada_fp;
  (void)sink;
}

void benchmarkFPSqrtOnly(camada::SMTSolver &solver, std::size_t iterations) {
  bool old_use_camada_fp = solver.useCamadaFP;
  solver.useCamadaFP = true;

  auto fp32 = solver.mkFP32Sort();
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN);
  auto a = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPSqrt(a, rm)->getWidth();

  solver.useCamadaFP = old_use_camada_fp;
  (void)sink;
}

void benchmarkFPFMAOnly(camada::SMTSolver &solver, std::size_t iterations) {
  bool old_use_camada_fp = solver.useCamadaFP;
  solver.useCamadaFP = true;

  auto fp32 = solver.mkFP32Sort();
  auto rm = solver.mkRM(camada::RM::ROUND_TO_EVEN);
  auto x = solver.mkSBVtoFP(solver.mkBVFromDec(123, 32), fp32, rm);
  auto y = solver.mkUBVtoFP(solver.mkBVFromDec(456, 32), fp32, rm);
  auto z = solver.mkFP32(1.25f);
  volatile std::size_t sink = 0;

  for (std::size_t i = 0; i < iterations; ++i)
    sink += solver.mkFPFMA(x, y, z, rm)->getWidth();

  solver.useCamadaFP = old_use_camada_fp;
  (void)sink;
}

void printUsage(const char *argv0) {
  std::fprintf(stderr,
               "Usage: %s [backend] [iterations]\n"
               "Backends: bitwuzla cvc5 mathsat stp yices z3\n",
               argv0);
}

} // namespace

int main(int argc, char **argv) {
  try {
    std::string backend = argc > 1 ? argv[1] : defaultBackend();
    std::size_t iterations =
        argc > 2 ? static_cast<std::size_t>(std::strtoull(argv[2], nullptr, 10))
                 : 1000;

    if (iterations == 0)
      throw std::runtime_error("iterations must be greater than zero");

    runCase(backend, "bv_sort_same", iterations, benchmarkBVSort);
    runCase(backend, "bv_const_same", iterations, benchmarkBVConstSame);
    runCase(backend, "bv_const_varied", iterations, benchmarkBVConstVaried);
    runCase(backend, "bv_expr_chain", iterations, benchmarkBVExprChain);
    runCase(backend, "array_store_chain", iterations, benchmarkArrayStoreChain);
    runCase(backend, "fp_from_bv", iterations, benchmarkFPFromBV);
    runCase(backend, "fp_add_only", iterations, benchmarkFPAddOnly);
    runCase(backend, "fp_div_only", iterations, benchmarkFPDivOnly);
    runCase(backend, "fp_integral_only", iterations, benchmarkFPIntegralOnly);
    runCase(backend, "fp_ieee_to_bv_only", iterations, benchmarkFPIEEEToBVOnly);
    runCase(backend, "fp_sqrt_only", iterations, benchmarkFPSqrtOnly);
    runCase(backend, "fp_fma_only", iterations, benchmarkFPFMAOnly);
    runCase(backend, "fp_construct", iterations, benchmarkFPConstruct);
    return 0;
  } catch (const std::exception &Exn) {
    std::fprintf(stderr, "%s\n", Exn.what());
    printUsage(argv[0]);
    return 1;
  }
}
