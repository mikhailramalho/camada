// Execution-oracle cross-check for the fixed-point encoding: every
// vector in fxp_oracle_tables.h was computed by running Clang-compiled
// -ffixed-point arithmetic (see scripts/fxp_oracle_gen.py for the
// pinned configuration); the fixture pins camada's BV encoding to the
// observed raw bits. UB cases were filtered at generation, so every
// vector is a defined-behavior comparison.

#ifndef CAMADA_REGRESSION_FXPORACLE_TEST_H_
#define CAMADA_REGRESSION_FXPORACLE_TEST_H_

#include "camada.h"
#include "fxp_oracle_tables.h"

#include <catch2/catch_test_macros.hpp>

#include <cstddef>
#include <cstdint>
#include <string>

namespace camada_fxp_oracle {

inline std::string rawBits(uint64_t Raw, unsigned Width) {
  std::string Bits(Width, '0');
  for (unsigned I = 0; I < Width; ++I)
    if ((Raw >> I) & 1)
      Bits[Width - 1 - I] = '1';
  return Bits;
}

inline camada::SMTExprRef mkFXP(const camada::SMTSolverRef &S, uint64_t Raw,
                                unsigned W, unsigned N, bool Signed) {
  return S->mkFXPFromBin(rawBits(Raw, W), S->mkFXPSort(W, N, Signed));
}

// Ground constant equalities check by SAT in chunks — one check proves
// every conjunct in the chunk at once. Each chunk resets the solver
// FIRST and only then builds its conjuncts: expressions do not survive
// reset(), so building ahead of the reset would leave stale handles.
template <typename BuildFn>
inline void checkVectorsChunked(const camada::SMTSolverRef &S,
                                std::size_t Count, BuildFn &&Build) {
  constexpr std::size_t Chunk = 4096;
  for (std::size_t Base = 0; Base < Count; Base += Chunk) {
    S->reset();
    camada::SMTExprRef All;
    for (std::size_t I = Base; I < Base + Chunk && I < Count; ++I) {
      camada::SMTExprRef C = Build(I);
      All = All ? S->mkAnd(All, C) : C;
    }
    S->addConstraint(All);
    REQUIRE(S->check() == camada::checkResult::SAT);
  }
}

inline void fxp_oracle_semantics(const camada::SMTSolverRef &solver) {
  const std::size_t NArith = sizeof(kArith) / sizeof(kArith[0]);
  checkVectorsChunked(solver, NArith, [&](std::size_t I) {
    const OrArith &V = kArith[I];
    camada::SMTExprRef A = mkFXP(solver, V.a, V.w, V.n, V.s != 0);
    camada::SMTExprRef R;
    switch (V.op) {
    case OrOp::Add:
      R = solver->mkFXPAdd(A, mkFXP(solver, V.b, V.w, V.n, V.s != 0));
      break;
    case OrOp::Sub:
      R = solver->mkFXPSub(A, mkFXP(solver, V.b, V.w, V.n, V.s != 0));
      break;
    case OrOp::Mul:
      R = solver->mkFXPMul(A, mkFXP(solver, V.b, V.w, V.n, V.s != 0));
      break;
    case OrOp::Div:
      R = solver->mkFXPDiv(A, mkFXP(solver, V.b, V.w, V.n, V.s != 0));
      break;
    case OrOp::Neg:
      R = solver->mkFXPNeg(A);
      break;
    case OrOp::Shl:
      R = solver->mkFXPShl(A, static_cast<unsigned>(V.b));
      break;
    case OrOp::Shr:
      R = solver->mkFXPShr(A, static_cast<unsigned>(V.b));
      break;
    case OrOp::AddSat:
      R = solver->mkFXPAddSat(A, mkFXP(solver, V.b, V.w, V.n, V.s != 0));
      break;
    case OrOp::SubSat:
      R = solver->mkFXPSubSat(A, mkFXP(solver, V.b, V.w, V.n, V.s != 0));
      break;
    case OrOp::MulSat:
      R = solver->mkFXPMulSat(A, mkFXP(solver, V.b, V.w, V.n, V.s != 0));
      break;
    case OrOp::DivSat:
      R = solver->mkFXPDivSat(A, mkFXP(solver, V.b, V.w, V.n, V.s != 0));
      break;
    case OrOp::NegSat:
      R = solver->mkFXPNegSat(A);
      break;
    case OrOp::ShlSat:
      R = solver->mkFXPShlSat(A, static_cast<unsigned>(V.b));
      break;
    }
    return solver->mkFXPEqual(R, mkFXP(solver, V.r, V.w, V.n, V.s != 0));
  });

  const std::size_t NConv = sizeof(kConvSat) / sizeof(kConvSat[0]);
  checkVectorsChunked(solver, NConv, [&](std::size_t I) {
    const OrConv &V = kConvSat[I];
    camada::SMTExprRef A = mkFXP(solver, V.a, V.fw, V.fn, V.fs != 0);
    camada::SMTSortRef To = solver->mkFXPSort(V.tw, V.tn, V.ts != 0);
    return solver->mkFXPEqual(solver->mkFXPToFXPSat(A, To),
                              mkFXP(solver, V.r, V.tw, V.tn, V.ts != 0));
  });

  // In-range by generation-time filtering, so the plain conversion is
  // defined and the saturating one must agree with it (two conjuncts per
  // vector, handled by index halving).
  const std::size_t NToBV = sizeof(kToBV) / sizeof(kToBV[0]);
  checkVectorsChunked(solver, 2 * NToBV, [&](std::size_t I) {
    const OrToBV &V = kToBV[I / 2];
    camada::SMTExprRef A = mkFXP(solver, V.a, V.fw, V.fn, V.fs != 0);
    camada::SMTExprRef R = (I % 2) == 0
                               ? solver->mkFXPToBV(A, V.tw)
                               : solver->mkFXPToBVSat(A, V.tw, V.ts != 0);
    return solver->mkEqual(R, solver->mkBVFromBin(rawBits(V.r, V.tw), V.tw));
  });
}

} // namespace camada_fxp_oracle

using camada_fxp_oracle::fxp_oracle_semantics;

#endif // CAMADA_REGRESSION_FXPORACLE_TEST_H_
