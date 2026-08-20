
#include "camada.h"

#include <catch2/catch_test_macros.hpp>
#include <cmath>
#include <limits>
#include <tuple>
#include <utility>

inline void fp_native_bv_predicate_parity(const camada::SMTSolverRef &solver) {
  const auto backend = solver->mkBool(true)->getBackendKind();
  if (backend != camada::SMTBackendKind::Bitwuzla &&
      backend != camada::SMTBackendKind::CVC5 &&
      backend != camada::SMTBackendKind::MathSAT &&
      backend != camada::SMTBackendKind::Z3) {
    return;
  }

  const auto check_predicate = [&](const std::string &name, auto predicate) {
    solver->reset();

    auto bits = solver->mkSymbol(name + "_bits", solver->mkBVSort(32));
    auto native_fp = solver->mkBVToIEEEFP(
        bits, solver->mkFP32Sort(camada::FPEncoding::Native));
    auto bv_fp =
        solver->mkBVToIEEEFP(bits, solver->mkFP32Sort(camada::FPEncoding::BV));

    auto native_pred = predicate(native_fp);
    auto bv_pred = predicate(bv_fp);

    REQUIRE(native_pred->getKind() == bv_pred->getKind());
    solver->addConstraint(solver->mkNot(solver->mkEqual(native_pred, bv_pred)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  };

  check_predicate("is_nan", [&](const camada::SMTExprRef &fp) {
    return solver->mkFPIsNaN(fp);
  });
  check_predicate("is_inf", [&](const camada::SMTExprRef &fp) {
    return solver->mkFPIsInfinite(fp);
  });
  check_predicate("is_zero", [&](const camada::SMTExprRef &fp) {
    return solver->mkFPIsZero(fp);
  });
  check_predicate("is_denormal", [&](const camada::SMTExprRef &fp) {
    return solver->mkFPIsSubnormal(fp);
  });
  check_predicate("is_normal", [&](const camada::SMTExprRef &fp) {
    return solver->mkFPIsNormal(fp);
  });
}

inline void fp_neg_nan_native_bv_parity(const camada::SMTSolverRef &solver) {
  const auto backend = solver->mkBool(true)->getBackendKind();
  if (backend != camada::SMTBackendKind::Bitwuzla &&
      backend != camada::SMTBackendKind::CVC5 &&
      backend != camada::SMTBackendKind::MathSAT &&
      backend != camada::SMTBackendKind::Z3) {
    return;
  }

  const auto check_neg = [&](const std::string &name,
                             camada::FPNegBehavior behavior) {
    solver->reset();

    auto bits = solver->mkSymbol(name + "_bits", solver->mkBVSort(32));
    auto native_fp = solver->mkBVToIEEEFP(
        bits, solver->mkFP32Sort(camada::FPEncoding::Native));
    auto bv_fp =
        solver->mkBVToIEEEFP(bits, solver->mkFP32Sort(camada::FPEncoding::BV));

    auto native_neg = solver->mkFPNeg(native_fp, behavior);
    auto bv_neg = solver->mkFPNeg(bv_fp, behavior);
    auto flipped_bits =
        solver->mkBVConcat(solver->mkBVNot(solver->mkBVExtract(31, 31, bits)),
                           solver->mkBVExtract(30, 0, bits));
    auto expected_bits =
        behavior == camada::FPNegBehavior::FlipSignBit
            ? flipped_bits
            : solver->mkIte(solver->mkFPIsNaN(bv_fp), bits, flipped_bits);
    auto expected_native = solver->mkBVToIEEEFP(expected_bits, native_fp->Sort);
    auto expected_bv = solver->mkBVToIEEEFP(expected_bits, bv_fp->Sort);

    INFO(name);
    solver->addConstraint(
        solver->mkNot(solver->mkEqual(native_neg, expected_native)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);

    solver->reset();
    bits = solver->mkSymbol(name + "_bits_bv_expected", solver->mkBVSort(32));
    bv_fp =
        solver->mkBVToIEEEFP(bits, solver->mkFP32Sort(camada::FPEncoding::BV));
    bv_neg = solver->mkFPNeg(bv_fp, behavior);
    flipped_bits =
        solver->mkBVConcat(solver->mkBVNot(solver->mkBVExtract(31, 31, bits)),
                           solver->mkBVExtract(30, 0, bits));
    expected_bits =
        behavior == camada::FPNegBehavior::FlipSignBit
            ? flipped_bits
            : solver->mkIte(solver->mkFPIsNaN(bv_fp), bits, flipped_bits);
    expected_bv = solver->mkBVToIEEEFP(expected_bits, bv_fp->Sort);
    solver->addConstraint(solver->mkNot(solver->mkEqual(bv_neg, expected_bv)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  };

  check_neg("fp_neg_flip_sign", camada::FPNegBehavior::FlipSignBit);
  check_neg("fp_neg_standard", camada::FPNegBehavior::PreserveNaNPayload);
}

// Pin the IEEE-754 binary representation Camada returns for the FP infinity
// constant. Native FP backends emit `(_ +oo eb sb)` model values; BV-encoded
// FP returns the bitstring directly. Either way the result must be the
// canonical sign + all-ones-exponent + zero-significand pattern.
inline void fp_infinity_model_value(const camada::SMTSolverRef &solver,
                                    camada::FPEncoding Encoding) {
  auto fp32 = solver->mkFP32Sort(Encoding);
  auto x = solver->mkSymbol("x", fp32);
  // SigWidth here counts the hidden bit (FP32 = 8 + 24).
  solver->addConstraint(
      solver->mkEqual(x, solver->mkInf(false, 8, 24, Encoding)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto bin = solver->getFPInBin(x);
  REQUIRE(bin);
  // +inf in IEEE-754 single precision: 0 11111111 00000000000000000000000.
  REQUIRE(bin.value() == "01111111100000000000000000000000");
}

// Pin model parsing for NaN. Native FP backends emit `(_ NaN eb sb)`; the
// returned bitstring must be a structurally-valid NaN (sign 0, exp all
// ones, significand non-zero).
inline void fp_nan_model_value(const camada::SMTSolverRef &solver,
                               camada::FPEncoding Encoding) {
  auto fp32 = solver->mkFP32Sort(Encoding);
  auto x = solver->mkSymbol("x", fp32);
  solver->addConstraint(solver->mkFPIsNaN(x));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  auto bin = solver->getFPInBin(x);
  REQUIRE(bin);
  // IEEE-754 NaN: exponent all-ones (bits [1..8] for FP32), significand
  // non-zero. The sign bit is unspecified — solvers may return either
  // "quiet NaN" pattern with sign 0 or 1.
  REQUIRE(bin.value().substr(1, 8) == "11111111");
  REQUIRE(bin.value().substr(9).find('1') != std::string::npos);
}

// `mkFPNeg` with `FPNegBehavior::FlipSignBit` must toggle the sign bit
// unconditionally — even on NaN, where SMT-LIB's standard `(fp.neg x)`
// (PreserveNaNPayload) would be allowed to leave NaNs unchanged. The
// implementation must therefore round-trip through `mkIEEEFPToBV` /
// `mkBVToIEEEFP`. This fixture pins that path: take an arbitrary NaN, neg
// it with FlipSignBit, and assert the IEEE bit pattern matches the input
// with bit [N-1] xored.
inline void
fp_neg_flip_nan_via_bv_round_trip(const camada::SMTSolverRef &solver,
                                  camada::FPEncoding Encoding) {
  auto fp32 = solver->mkFP32Sort(Encoding);
  auto x = solver->mkSymbol("x", fp32);
  solver->addConstraint(solver->mkFPIsNaN(x));

  auto negged = solver->mkFPNeg(x, camada::FPNegBehavior::FlipSignBit);
  auto x_bits = solver->mkIEEEFPToBV(x);
  auto negged_bits = solver->mkIEEEFPToBV(negged);

  // bit [31] of negged_bits must be the complement of bit [31] of x_bits.
  auto x_sign = solver->mkBVExtract(31, 31, x_bits);
  auto n_sign = solver->mkBVExtract(31, 31, negged_bits);
  solver->addConstraint(solver->mkEqual(n_sign, solver->mkBVNot(x_sign)));

  // bits [30:0] must match.
  auto x_rest = solver->mkBVExtract(30, 0, x_bits);
  auto n_rest = solver->mkBVExtract(30, 0, negged_bits);
  solver->addConstraint(solver->mkEqual(n_rest, x_rest));

  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void fp_arithmetics(const camada::SMTSolverRef &solver,
                           camada::FPEncoding Encoding) {
  auto x = solver->mkFP32(0.750000059604644775390625f, Encoding);
  auto y = solver->mkFP32(0.750000059604644775390625f, Encoding);
  REQUIRE(x->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(y->getKind() == camada::SMTExprKind::FPConst);

  auto zero = solver->mkFP32(0.f, Encoding);
  auto one = solver->mkFP32(1.f, Encoding);
  auto two = solver->mkFP32(2.f, Encoding);
  REQUIRE(zero->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(one->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(two->getKind() == camada::SMTExprKind::FPConst);

  auto r = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);
  REQUIRE(r->getKind() == camada::SMTExprKind::RMConst);

  // Add
  auto neg = solver->mkFPNeg(y);
  auto add = solver->mkFPAdd(x, neg, r);
  auto add_eq = solver->mkEqual(add, zero);
  REQUIRE(neg->getKind() == camada::SMTExprKind::FPNeg);
  REQUIRE(add->getKind() == camada::SMTExprKind::FPAdd);
  REQUIRE(add_eq->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(add_eq);

  // sub
  auto sub = solver->mkFPSub(x, y, r);
  auto sub_eq = solver->mkEqual(sub, zero);
  REQUIRE(sub->getKind() == camada::SMTExprKind::FPSub);
  REQUIRE(sub_eq->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(sub_eq);

  // mul
  auto mul = solver->mkFP32(0.562500119209f, Encoding);
  auto mul_expr = solver->mkFPMul(x, y, r);
  auto mul_eq = solver->mkEqual(mul_expr, mul);
  REQUIRE(mul_expr->getKind() == camada::SMTExprKind::FPMul);
  REQUIRE(mul_eq->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(mul_eq);

  // div
  auto div = solver->mkFPDiv(x, y, r);
  auto div_eq = solver->mkEqual(div, one);
  REQUIRE(div->getKind() == camada::SMTExprKind::FPDiv);
  REQUIRE(div_eq->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(div_eq);

  // sqrt
  auto sqrt = solver->mkFPSqrt(one, r);
  auto sqrt_eq = solver->mkEqual(sqrt, one);
  REQUIRE(sqrt->getKind() == camada::SMTExprKind::FPSqrt);
  REQUIRE(sqrt_eq->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(sqrt_eq);

  // rem
  auto rem = solver->mkFPRem(x, y);
  auto rem_eq = solver->mkEqual(rem, zero);
  REQUIRE(rem->getKind() == camada::SMTExprKind::FPRem);
  REQUIRE(rem_eq->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(rem_eq);

  // fma
  auto fma = solver->mkFPFMA(one, two, zero, r);
  auto fma_eq = solver->mkEqual(fma, two);
  REQUIRE(fma->getKind() == camada::SMTExprKind::FPFMA);
  REQUIRE(fma_eq->getKind() == camada::SMTExprKind::Equal);
  solver->addConstraint(fma_eq);

  // And check for satisfiability
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void fp_round_to_away(const camada::SMTSolverRef &solver,
                             camada::FPEncoding Encoding) {
  auto one = solver->mkFP32(1.0f, Encoding);
  if (Encoding == camada::FPEncoding::Native &&
      one->getBackendKind() == camada::SMTBackendKind::MathSAT) {
    // MathSAT's native FP API does not support ROUND_TO_AWAY.
    return;
  }
  auto half_ulp = solver->mkFP32(std::ldexp(1.0f, -24), Encoding);
  auto rne = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);
  auto rna = solver->mkRM(camada::RM::ROUND_TO_AWAY, Encoding);

  REQUIRE(one->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(half_ulp->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(rne->getKind() == camada::SMTExprKind::RMConst);
  REQUIRE(rna->getKind() == camada::SMTExprKind::RMConst);

  auto even_sum = solver->mkFPAdd(one, half_ulp, rne);
  auto away_sum = solver->mkFPAdd(one, half_ulp, rna);
  REQUIRE(even_sum->getKind() == camada::SMTExprKind::FPAdd);
  REQUIRE(away_sum->getKind() == camada::SMTExprKind::FPAdd);

  auto even_expected = solver->mkFP32(1.0f, Encoding);
  auto away_expected = solver->mkFP32(std::nextafterf(1.0f, 2.0f), Encoding);

  solver->addConstraint(solver->mkEqual(even_sum, even_expected));
  solver->addConstraint(solver->mkEqual(away_sum, away_expected));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void fp_bv_conversions(const camada::SMTSolverRef &solver,
                              camada::FPEncoding Encoding) {
  auto rtz = solver->mkRM(camada::RM::ROUND_TO_ZERO, Encoding);
  auto fp32 = solver->mkFP32Sort(Encoding);
  auto all_ones = solver->mkBVFromBin("11111111", 8);

  REQUIRE(rtz->getKind() == camada::SMTExprKind::RMConst);
  REQUIRE(all_ones->getKind() == camada::SMTExprKind::BVConst);

  auto signed_fp = solver->mkSBVToFP(all_ones, fp32, rtz);
  auto unsigned_fp = solver->mkUBVToFP(all_ones, fp32, rtz);
  REQUIRE(signed_fp->getKind() == camada::SMTExprKind::SBVtoFP);
  REQUIRE(unsigned_fp->getKind() == camada::SMTExprKind::UBVtoFP);

  auto minus_one = solver->mkFP32(-1.0f, Encoding);
  auto two_fifty_five = solver->mkFP32(255.0f, Encoding);
  solver->addConstraint(solver->mkEqual(signed_fp, minus_one));
  solver->addConstraint(solver->mkEqual(unsigned_fp, two_fifty_five));

  auto signed_bv = solver->mkFPToSBV(signed_fp, 8);
  auto unsigned_bv = solver->mkFPToUBV(unsigned_fp, 8);
  REQUIRE(signed_bv->getKind() == camada::SMTExprKind::FPtoSBV);
  REQUIRE(unsigned_bv->getKind() == camada::SMTExprKind::FPtoUBV);

  solver->addConstraint(solver->mkEqual(signed_bv, all_ones));
  solver->addConstraint(solver->mkEqual(unsigned_bv, all_ones));

  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// Regression for the ESBMC fp.to_ieee_bv round-trip report: bit-exact
// fp<->bv correspondence wherever camada can prove the bits.
inline void fp_ieee_bv_bitexact_roundtrip(const camada::SMTSolverRef &solver,
                                          camada::FPEncoding Encoding) {
  auto fp32 = [&]() { return solver->mkFP32Sort(Encoding); };
  auto bv32 = [&]() { return solver->mkBVSort(32); };

  // 1. Direct round-trip is exact for EVERY pattern, NaN payloads
  // included: bits(to_fp(b)) == b universally. fp.to_ieee_bv alone cannot
  // provide this (it is underspecified at NaN); the provenance shadow
  // makes it a term-level identity.
  {
    auto b = solver->mkSymbol("rt_b", bv32());
    auto f = solver->mkBVToIEEEFP(b, fp32());
    solver->addConstraint(
        solver->mkNot(solver->mkEqual(solver->mkIEEEFPToBV(f), b)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
  solver->reset();

  // 2. ESBMC's byte-write laundering chain: an uninitialized float
  // written byte-by-byte (0x40490FDB, little-endian), each step
  // round-tripping the partial state through the FP sort via a fresh SSA
  // symbol tied by an asserted equality. Before the shadow, any
  // partial-write state encoding NaN let the solver discard the bytes
  // already written; the final byte read must nevertheless be exact.
  {
    auto byteAt = [&](const camada::SMTExprRef &bits, unsigned lo) {
      return solver->mkBVExtract(lo + 7, lo, bits);
    };
    const uint64_t Bytes[4] = {0xDB, 0x0F, 0x49, 0x40};
    auto f = solver->mkSymbol("lc_f0", fp32());
    for (unsigned i = 0; i < 4; ++i) {
      auto bits = solver->mkIEEEFPToBV(f);
      auto wr = solver->mkBVFromDec(static_cast<int64_t>(Bytes[i]), 8);
      // Rebuild the 32-bit pattern with byte i replaced.
      camada::SMTExprRef nbits;
      if (i == 0)
        nbits = solver->mkBVConcat(solver->mkBVExtract(31, 8, bits), wr);
      else if (i == 3)
        nbits = solver->mkBVConcat(wr, solver->mkBVExtract(23, 0, bits));
      else
        nbits = solver->mkBVConcat(
            solver->mkBVConcat(solver->mkBVExtract(31, 8 * (i + 1), bits), wr),
            solver->mkBVExtract(8 * i - 1, 0, bits));
      auto next = solver->mkSymbol("lc_f" + std::to_string(i + 1), fp32());
      solver->addConstraint(
          solver->mkEqual(solver->mkBVToIEEEFP(nbits, fp32()), next));
      f = next;
    }
    auto finalBits = solver->mkIEEEFPToBV(f);
    solver->addConstraint(solver->mkNot(
        solver->mkEqual(byteAt(finalBits, 0), solver->mkBVFromDec(0xDB, 8))));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
  solver->reset();

  // 3. Assert-derived provenance dies with its push scope: after the
  // tying equality is popped, the bits are unconstrained again, so a
  // divergent pattern must be satisfiable.
  {
    auto g = solver->mkSymbol("sc_g", fp32());
    auto pat = solver->mkBVFromDec(0x40490FDB, 32);
    solver->push();
    solver->addConstraint(
        solver->mkEqual(g, solver->mkBVToIEEEFP(pat, fp32())));
    solver->pop();
    solver->addConstraint(
        solver->mkNot(solver->mkEqual(solver->mkIEEEFPToBV(g), pat)));
    REQUIRE(solver->check() == camada::CheckResult::SAT);
  }
}

// Regression for the second ESBMC fp.to_ieee_bv report
// (github_3719_4-nondet): mkIEEEFPToBV must be functionally consistent —
// value-equal FP terms report equal bits, matching z3's native
// primitive. The fresh-symbol emulation minted unrelated constants per
// call, so an equality asserted BEFORE either side had provenance left
// the two symbols free to diverge at NaN.
inline void fp_ieee_bv_consistency(const camada::SMTSolverRef &solver,
                                   camada::FPEncoding Encoding) {
  auto fp32 = [&]() { return solver->mkFP32Sort(Encoding); };

  // 1. Equality-before-provenance: two plain FP symbols asserted equal
  // before any fp->bv conversion exists must report equal bits, NaN
  // included.
  {
    auto y = solver->mkSymbol("cy", fp32());
    auto z = solver->mkSymbol("cz", fp32());
    solver->addConstraint(solver->mkEqual(y, z));
    auto by = solver->mkIEEEFPToBV(y);
    auto bz = solver->mkIEEEFPToBV(z);
    solver->addConstraint(solver->mkNot(solver->mkEqual(by, bz)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
  solver->reset();

  // 2. Repeated reads of one term cannot diverge.
  {
    auto f = solver->mkSymbol("cf", fp32());
    auto b1 = solver->mkIEEEFPToBV(f);
    auto b2 = solver->mkIEEEFPToBV(f);
    solver->addConstraint(solver->mkNot(solver->mkEqual(b1, b2)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
  solver->reset();

  // 3. Exactness where the encoding is injective: a non-NaN value's bits
  // are fully determined.
  {
    auto f = solver->mkSymbol("cg", fp32());
    solver->addConstraint(solver->mkEqual(f, solver->mkFP32(1.5f, Encoding)));
    auto bits = solver->mkIEEEFPToBV(f);
    solver->addConstraint(solver->mkNot(
        solver->mkEqual(bits, solver->mkBVFromDec(0x3FC00000, 32))));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
}

// Regression: mkIEEEFPToBV must return a PLAIN BV sort, not BVFP. The
// native backends used to tag the bit pattern with the BVFP sort, which
// leaked into caller sort comparisons — ESBMC's float→int bitcast
// produced a term whose sort disagreed with its own BV type, aborting on
// the first mkEqual against an ordinary bit-vector.
inline void fp_ieee_bv_sort_identity(const camada::SMTSolverRef &solver,
                                     camada::FPEncoding Encoding) {
  auto fp = solver->mkSymbol("ibv_f", solver->mkFP32Sort(Encoding));
  auto bits = solver->mkIEEEFPToBV(fp);

  // Exactly the sort mkBVSort(32) hands out — this is what callers compare
  // against, and BVFP would fail requireSameSort below.
  REQUIRE(bits->Sort == solver->mkBVSort(32));

  // ESBMC's bitcast pattern: equate the bit pattern with a plain BV
  // symbol, then pin the round-trip semantics.
  auto ibv = solver->mkSymbol("ibv_i", solver->mkBVSort(32));
  solver->addConstraint(solver->mkEqual(bits, ibv));
  solver->addConstraint(solver->mkEqual(fp, solver->mkFP32(1.5f, Encoding)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  auto v = solver->getBVInBin(ibv);
  REQUIRE(v);
  REQUIRE(v.value() == "00111111110000000000000000000000"); // 1.5f
}

inline void fp_to_signed_bv_multiple_widths(const camada::SMTSolverRef &solver,
                                            camada::FPEncoding Encoding) {
  auto fp = solver->mkFP32(42.0f, Encoding);
  auto sbv32 = solver->mkFPToSBV(fp, 32);

  REQUIRE(fp->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(sbv32->getKind() == camada::SMTExprKind::FPtoSBV);

  solver->addConstraint(solver->mkEqual(sbv32, solver->mkBVFromDec(42, 32)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  solver->reset();
  fp = solver->mkFP32(42.0f, Encoding);
  auto sbv64 = solver->mkFPToSBV(fp, 64);
  REQUIRE(fp->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(sbv64->getKind() == camada::SMTExprKind::FPtoSBV);
  solver->addConstraint(solver->mkEqual(sbv64, solver->mkBVFromDec(42, 64)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  solver->reset();
  fp = solver->mkFP32(42.0f, Encoding);
  sbv32 = solver->mkFPToSBV(fp, 32);
  sbv64 = solver->mkFPToSBV(fp, 64);
  REQUIRE(fp->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(sbv32->getKind() == camada::SMTExprKind::FPtoSBV);
  REQUIRE(sbv64->getKind() == camada::SMTExprKind::FPtoSBV);
  solver->addConstraint(solver->mkEqual(sbv32, solver->mkBVFromDec(42, 32)));
  solver->addConstraint(solver->mkEqual(sbv64, solver->mkBVFromDec(42, 64)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);

  // Width 1 is the degenerate signed target: its range is [-1, 0], so 0
  // converts and -1 converts, while 42 is out of range. The BV encoding
  // used to build the range bounds by concatenating a (width-1)-wide
  // value, which is a zero-width sort here and aborted.
  solver->reset();
  auto zero = solver->mkFP32(0.0f, Encoding);
  auto neg_one = solver->mkFP32(-1.0f, Encoding);
  solver->addConstraint(
      solver->mkEqual(solver->mkFPToSBV(zero, 1), solver->mkBVFromDec(0, 1)));
  solver->addConstraint(solver->mkEqual(solver->mkFPToSBV(neg_one, 1),
                                        solver->mkBVFromDec(1, 1)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void fp_denormal_round_to_integral(const camada::SMTSolverRef &solver,
                                          camada::FPEncoding Encoding) {
  auto pos_denorm =
      solver->mkFP32(std::numeric_limits<float>::denorm_min(), Encoding);
  auto neg_denorm =
      solver->mkFP32(-std::numeric_limits<float>::denorm_min(), Encoding);
  auto rtp = solver->mkRM(camada::RM::ROUND_TO_PLUS_INF, Encoding);
  auto rtn = solver->mkRM(camada::RM::ROUND_TO_MINUS_INF, Encoding);

  auto pos_rounded = solver->mkFPToIntegral(pos_denorm, rtp);
  auto neg_rounded = solver->mkFPToIntegral(neg_denorm, rtn);

  REQUIRE(pos_denorm->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(neg_denorm->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(rtp->getKind() == camada::SMTExprKind::RMConst);
  REQUIRE(rtn->getKind() == camada::SMTExprKind::RMConst);
  REQUIRE(pos_rounded->getKind() == camada::SMTExprKind::FPtoIntegral);
  REQUIRE(neg_rounded->getKind() == camada::SMTExprKind::FPtoIntegral);

  solver->addConstraint(
      solver->mkEqual(pos_rounded, solver->mkFP32(1.0f, Encoding)));
  solver->addConstraint(
      solver->mkEqual(neg_rounded, solver->mkFP32(-1.0f, Encoding)));

  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void fp_div_overflow_to_inf(const camada::SMTSolverRef &solver,
                                   camada::FPEncoding Encoding) {
  auto max_finite = solver->mkFP32(std::numeric_limits<float>::max(), Encoding);
  auto tiny =
      solver->mkFP32(std::numeric_limits<float>::denorm_min(), Encoding);
  auto rne = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);

  auto div = solver->mkFPDiv(max_finite, tiny, rne);

  REQUIRE(max_finite->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(tiny->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(rne->getKind() == camada::SMTExprKind::RMConst);
  REQUIRE(div->getKind() == camada::SMTExprKind::FPDiv);

  solver->addConstraint(solver->mkEqual(
      div, solver->mkFP32(std::numeric_limits<float>::infinity(), Encoding)));

  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void fp_remainder_semantics(const camada::SMTSolverRef &solver,
                                   camada::FPEncoding Encoding) {
  auto x = solver->mkFP32(7.0f, Encoding);
  auto y = solver->mkFP32(2.0f, Encoding);
  auto expected = solver->mkFP32(-1.0f, Encoding);

  auto rem = solver->mkFPRem(x, y);

  REQUIRE(x->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(y->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(expected->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(rem->getKind() == camada::SMTExprKind::FPRem);

  solver->addConstraint(solver->mkEqual(rem, expected));

  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// Checks one concrete fp.rem result against the host CPU, which computes
// IEEE-754 remainder exactly (std::remainder is correctly rounded). mkEqual
// is object equality on FP, so signed zeros are distinguished; NaN results
// are checked via fp.isNaN since payloads are unspecified.
inline void check_rem_pair_f32(const camada::SMTSolverRef &solver,
                               camada::FPEncoding Encoding, float X, float Y) {
  const bool IsBVEncoding = Encoding == camada::FPEncoding::BV;
  CAPTURE(X, Y, IsBVEncoding);
  solver->reset();
  auto rem =
      solver->mkFPRem(solver->mkFP32(X, Encoding), solver->mkFP32(Y, Encoding));
  float Expected = std::remainder(X, Y);
  if (std::isnan(Expected))
    solver->addConstraint(solver->mkFPIsNaN(rem));
  else
    solver->addConstraint(
        solver->mkEqual(rem, solver->mkFP32(Expected, Encoding)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void check_rem_pair_f64(const camada::SMTSolverRef &solver,
                               camada::FPEncoding Encoding, double X,
                               double Y) {
  const bool IsBVEncoding = Encoding == camada::FPEncoding::BV;
  CAPTURE(X, Y, IsBVEncoding);
  solver->reset();
  auto rem =
      solver->mkFPRem(solver->mkFP64(X, Encoding), solver->mkFP64(Y, Encoding));
  double Expected = std::remainder(X, Y);
  if (std::isnan(Expected))
    solver->addConstraint(solver->mkFPIsNaN(rem));
  else
    solver->addConstraint(
        solver->mkEqual(rem, solver->mkFP64(Expected, Encoding)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// Multiply and divide against the host CPU, on subnormal operands.
//
// These are the inputs that caught a regression where multiply and divide
// stopped normalizing their operands. round() renormalizes the
// significand, so the change looked safe, but an unnormalized subnormal
// reports an exponent understated by its leading-zero count and round()
// cannot recover that: multiply returned a wrong subnormal product and
// divide returned an infinity where the result is finite.
inline void fp_muldiv_subnormal_host_oracle(const camada::SMTSolverRef &solver,
                                            camada::FPEncoding Encoding) {
  const float Sub = std::numeric_limits<float>::denorm_min();
  const std::pair<float, float> Pairs[] = {
      // Ordinary values, as a control.
      {3.0f, 2.0f},
      {-7.5f, 0.5f},
      // Subnormal operands. A subnormal times a large value lands back in
      // the normal range; a normal over a subnormal overflows the naive
      // exponent difference.
      {-128.5f, Sub},
      {Sub, 1e38f},
      {Sub * 3.0f, -1.6482427e38f},
      {4.82425e-07f, -2.93883e-39f},
      {1.0f, Sub},
      {Sub, Sub},
  };

  for (auto [X, Y] : Pairs) {
    for (bool IsDiv : {false, true}) {
      solver->reset();
      // Drive the operands through symbols pinned by equality rather than
      // passing constants: a constant multiply is folded by the backend's
      // rewriter and never reaches the bit-blast under test.
      auto s = solver->mkFP32Sort(Encoding);
      auto x = solver->mkSymbol("mdx", s);
      auto y = solver->mkSymbol("mdy", s);
      solver->addConstraint(solver->mkFPEqual(x, solver->mkFP32(X, Encoding)));
      solver->addConstraint(solver->mkFPEqual(y, solver->mkFP32(Y, Encoding)));
      auto rm = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);
      auto got = IsDiv ? solver->mkFPDiv(x, y, rm) : solver->mkFPMul(x, y, rm);
      // volatile keeps the reference at float precision.
      volatile float VX = X, VY = Y;
      const float Want = IsDiv ? VX / VY : VX * VY;
      auto want = solver->mkFP32(Want, Encoding);
      // Compare IEEE bits: a wrong subnormal and an infinity where the
      // result is finite both show up, and fp.eq would hide -0 vs +0.
      INFO((IsDiv ? "div(" : "mul(") << X << ", " << Y << ") want " << Want);
      solver->addConstraint(solver->mkNot(solver->mkEqual(
          solver->mkIEEEFPToBV(got), solver->mkIEEEFPToBV(want))));
      REQUIRE(solver->check() == camada::CheckResult::UNSAT);
    }
  }
}

// toIntegral on values that are already integers, across formats.
//
// The "exponent >= sbits-1, so x is already an integer" branch was gated
// by a floating-point log2 test that reads 4.17 > 4 for binary16 and
// disabled the branch outright, so toIntegral(14184.0) returned 0.5.
// binary32 passed the same gate, which is why nothing here caught it —
// hence the explicit narrow-format case.
// The binary16 half runs under the BV encoding only, matching
// fp_non_standard_widths: narrow formats are camada's own encoding, and
// backends reject them natively (cvc5 requires --fp-exp, bitwuzla
// --fpexp).
inline void fp_tointegral_large_values_bv(const camada::SMTSolverRef &solver) {
  const camada::FPEncoding Encoding = camada::FPEncoding::BV;
  // Large binary16 values: every one of these is exactly an integer, so
  // toIntegral must return it unchanged.
  const std::string Halfs[] = {
      "0110100000010000", // 2^11 * 1.0625
      "0110110000010000", "0111000000010000",
      "0111010000010000", "0111100000010000", // 14184-scale magnitudes
  };
  for (const std::string &Bits : Halfs) {
    solver->reset();
    auto x = solver->mkFPFromBin(Bits, 5, Encoding);
    auto rm = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);
    INFO("binary16 toIntegral(" << Bits << ")");
    solver->addConstraint(
        solver->mkNot(solver->mkFPEqual(solver->mkFPToIntegral(x, rm), x)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
}

inline void fp_tointegral_large_values(const camada::SMTSolverRef &solver,
                                       camada::FPEncoding Encoding) {
  // binary32, which took the other side of the gate and stayed correct.
  for (float V : {16777216.0f, 14184.0f, 1e30f, -1e30f, -14184.0f}) {
    solver->reset();
    auto x = solver->mkFP32(V, Encoding);
    auto rm = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);
    INFO("binary32 toIntegral(" << V << ")");
    solver->addConstraint(
        solver->mkNot(solver->mkFPEqual(solver->mkFPToIntegral(x, rm), x)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
}

// FMA against the host CPU's fused multiply-add, which is exact per
// IEEE-754: one rounding of x*y+z, never two. The subnormal cases are the
// point — camada's bit-blast inherited a one-ulp error from Z3's
// fpa2bv_converter that only shows when an operand is subnormal, and the
// symbolic fixtures above do not reach it.
inline void fp_fma_host_oracle(const camada::SMTSolverRef &solver,
                               camada::FPEncoding Encoding) {
  const float Sub = std::numeric_limits<float>::denorm_min();
  const std::tuple<float, float, float> Triples[] = {
      // Ordinary values, as a control.
      {2.0f, 3.0f, 1.0f},
      {0.5f, 0.5f, 0.25f},
      {-2.5f, 4.0f, 0.5f},
      // Subnormal operands: a subnormal times a large value lands back in
      // the normal range, so the product's leading zeros must be accounted
      // for before it is aligned against the addend.
      {Sub, 1e38f, 0.6467139f},
      {Sub * 3.0f, -1.6482427e38f, 0.6467139f},
      {-1.1180757e-38f, -1.6482427e38f, 0.64671391f},
      {Sub, Sub, 1.0f},
      {Sub * 7.0f, 2.0f, -Sub},
  };

  for (auto [X, Y, Z] : Triples) {
    solver->reset();
    auto x = solver->mkFP32(X, Encoding);
    auto y = solver->mkFP32(Y, Encoding);
    auto z = solver->mkFP32(Z, Encoding);
    auto rm = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);
    auto got = solver->mkFPFMA(x, y, z, rm);
    auto want = solver->mkFP32(std::fma(X, Y, Z), Encoding);
    INFO("fma(" << X << ", " << Y << ", " << Z << ")");
    solver->addConstraint(solver->mkNot(solver->mkFPEqual(got, want)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
}

inline void fp_remainder_host_oracle(const camada::SMTSolverRef &solver,
                                     camada::FPEncoding Encoding) {
  const std::pair<float, float> Pairs[] = {
      // Quotient rounding and ties-to-even.
      {5.0f, 2.0f},  // q = 2.5 -> 2 (even), rem = 1
      {7.0f, 2.0f},  // q = 3.5 -> 4 (even), rem = -1
      {6.0f, 4.0f},  // q = 1.5 -> 2 (even), rem = -2
      {10.0f, 4.0f}, // q = 2.5 -> 2 (even), rem = 2
      {7.5f, 2.5f},  // exact q = 3, rem = 0
      // Sign combinations; rem keeps the sign of x.
      {-5.0f, 2.0f},
      {5.0f, -2.0f},
      {-5.0f, -2.0f},
      {-7.0f, 2.0f},
      // Signed zero results.
      {4.0f, 2.0f},  // +0
      {-4.0f, 2.0f}, // -0
      {0.0f, 3.0f},
      {-0.0f, 3.0f},
      // Large exponent difference (the expensive encoding path).
      {1.0e38f, 3.0f},
      {1.0e30f, 1.1754944e-38f}, // y = min normal
      // Exponent difference beyond 2^ebits - 3: y subnormal pushes the
      // normalized difference up to (2^ebits - 3) + (sbits - 1). The
      // classic Z3-style encoding under-allocates shift headroom here and
      // returns wrong values; pins the modular encoding's fix.
      {3.0e38f, 7.0e-39f},
      {3.4028235e38f, 1.4012985e-45f}, // max finite over min subnormal
      // Subnormal operands.
      {1.0e-45f, 1.0e-44f},         // x, y both subnormal
      {1.0e-39f, 1.1754944e-38f},   // x subnormal, y min normal
      {1.0f, 1.4012985e-45f},       // y = min subnormal, huge diff
      {1.9999998f, 1.4012985e-45f}, // full mantissa over min subnormal
      {1.4012985e-45f, 1.0e-38f},   // x min subnormal, y near min normal
      {2.3509886e-38f, 2.3509887e-38f},
      // y subnormal with x slightly above: exercises the negative
      // exponent-difference path while the raw-exponent guard is disabled
      // (raw exp(y) == 0).
      {1.4012985e-45f, 1.1754942e-38f}, // |x| << |y|, y max subnormal
      {5.8774718e-39f, 1.1754942e-38f}, // q = 0.5, tie with q even
      {8.8162076e-39f, 1.1754942e-38f}, // q = 0.75 -> 1
      // x < y/2 just below the raw-exponent guard boundary.
      {0.49999997f, 2.0f},
      {0.5f, 2.0f}, // tie: q = 0.25 -> 0, rem = x
      // Specials.
      {3.0f, std::numeric_limits<float>::infinity()},  // -> x
      {-3.0f, std::numeric_limits<float>::infinity()}, // -> x
      {std::numeric_limits<float>::infinity(), 3.0f},  // -> NaN
      {3.0f, 0.0f},                                    // -> NaN
      {0.0f, 0.0f},                                    // -> NaN
  };
  for (const auto &P : Pairs)
    check_rem_pair_f32(solver, Encoding, P.first, P.second);
}

inline void fp_non_standard_widths(const camada::SMTSolverRef &solver,
                                   camada::FPEncoding Encoding) {
  // 5-bit exponent, 11-bit significand (float16-style format)
  auto one = solver->mkFPFromBin("0011110000000000", 5, Encoding);
  auto two = solver->mkFPFromBin("0100000000000000", 5, Encoding);
  auto rne = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);

  REQUIRE(one->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(two->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(one->getWidth() == 16);
  REQUIRE(two->getWidth() == 16);

  auto add = solver->mkFPAdd(one, one, rne);
  REQUIRE(add->getKind() == camada::SMTExprKind::FPAdd);

  solver->addConstraint(solver->mkEqual(add, two));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

inline void
fp_cancellation_and_normalization(const camada::SMTSolverRef &solver,
                                  camada::FPEncoding Encoding) {
  // Subtraction causing cancellation
  auto x = solver->mkFP32(1.0000001f, Encoding);
  auto y = solver->mkFP32(1.0f, Encoding);
  auto rne = solver->mkRM(camada::RM::ROUND_TO_EVEN, Encoding);
  auto sub = solver->mkFPSub(x, y, rne);

  auto eq = solver->mkEqual(sub, solver->mkFP32(1.0000001f - 1.0f, Encoding));
  solver->addConstraint(eq);
  solver->addConstraint(solver->mkFPIsNormal(sub));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
}

// Wide formats previously hit undefined behavior in the BV encoding's
// host-side constant construction (1ULL << N at N >= 64): binary128
// constants (2^112-1 significand masks) and x87-extended sqrt
// (2^(sbits+3) with sbits = 64). The constants are now built as bit
// strings at any width; these pin the previously-broken formats
// end-to-end. Constant operands let the backend fold the circuits, so
// the checks stay fast despite the widths.
inline void fp_wide_format_semantics(const camada::SMTSolverRef &solver) {
  // Bit pattern of the power-of-two value 2^K at a given format:
  // sign 0, exponent bias + K, significand zero.
  auto pow2At = [&](unsigned EW, unsigned SW, uint64_t K) {
    uint64_t exp = ((uint64_t(1) << (EW - 1)) - 1) + K;
    std::string bits = "0";
    for (unsigned i = 0; i < EW; ++i)
      bits += (exp >> (EW - 1 - i)) & 1 ? '1' : '0';
    bits += std::string(SW, '0');
    return solver->mkFPFromBin(bits, EW, camada::FPEncoding::BV);
  };

  // binary128: 1.0 + 1.0 == 2.0.
  {
    auto one = pow2At(15, 112, 0);
    auto two = pow2At(15, 112, 1);
    auto rm = solver->mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
    solver->addConstraint(
        solver->mkNot(solver->mkEqual(solver->mkFPAdd(one, one, rm), two)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
    solver->reset();
  }

  // x87-extended-like (15, 63): sqrt(4.0) == 2.0.
  {
    auto four = pow2At(15, 63, 2);
    auto two = pow2At(15, 63, 1);
    auto rm = solver->mkRM(camada::RM::ROUND_TO_EVEN, camada::FPEncoding::BV);
    solver->addConstraint(
        solver->mkNot(solver->mkEqual(solver->mkFPSqrt(four, rm), two)));
    REQUIRE(solver->check() == camada::CheckResult::UNSAT);
  }
}

inline void fp_typed_getter_format(const camada::SMTSolverRef &solver,
                                   camada::FPEncoding Encoding) {
  // getFP32 and getFP64 name a specific IEEE format. Handed a term of a
  // different one they used to parse whatever bitstring came back, so a
  // binary64 1.5 read through getFP32 answered 0 instead of reporting.
  auto f32 = solver->mkFPSort(8, 23, Encoding);
  auto f64 = solver->mkFPSort(11, 52, Encoding);

  auto d = solver->mkSymbol("tg_d", f64);
  solver->addConstraint(solver->mkEqual(d, solver->mkFP64(1.5, Encoding)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  auto asDouble = solver->getFP64(d);
  REQUIRE(asDouble);
  REQUIRE(asDouble.value() == 1.5);
  auto asFloat = solver->getFP32(d);
  REQUIRE_FALSE(asFloat);
  REQUIRE(asFloat.error().Code == camada::SMTErrorCode::InvalidUsage);

  solver->reset();
  f32 = solver->mkFPSort(8, 23, Encoding);
  auto f = solver->mkSymbol("tg_f", f32);
  solver->addConstraint(solver->mkEqual(f, solver->mkFP32(1.5f, Encoding)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  auto backAsFloat = solver->getFP32(f);
  REQUIRE(backAsFloat);
  REQUIRE(backAsFloat.value() == 1.5f);
  REQUIRE_FALSE(solver->getFP64(f));

  // A format that is neither binary32 nor binary64 matches neither
  // getter. Uses the BV encoding explicitly: cvc5 rejects non-standard
  // native FP formats without --fp-exp, and the getters' format check is
  // encoding-independent anyway.
  solver->reset();
  auto f16 = solver->mkFPSort(5, 10, camada::FPEncoding::BV);
  auto h = solver->mkSymbol("tg_h", f16);
  solver->addConstraint(solver->mkEqual(
      h, solver->mkFPFromBin("0011110000000000", 5, camada::FPEncoding::BV)));
  REQUIRE(solver->check() == camada::CheckResult::SAT);
  REQUIRE_FALSE(solver->getFP32(h));
  REQUIRE_FALSE(solver->getFP64(h));
  auto bits = solver->getFPInBin(h);
  REQUIRE(bits);
  REQUIRE(bits.value() == "0011110000000000");
}
