
#include "camada.h"

#include <catch2/catch_test_macros.hpp>
#include <cmath>
#include <limits>

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
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
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
    return solver->mkFPIsDenormal(fp);
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
    REQUIRE(solver->check() == camada::checkResult::UNSAT);

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
    REQUIRE(solver->check() == camada::checkResult::UNSAT);
  };

  check_neg("fp_neg_flip_sign", camada::FPNegBehavior::FlipSignBit);
  check_neg("fp_neg_standard", camada::FPNegBehavior::PreserveNaNPayload);
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
  REQUIRE(solver->check() == camada::checkResult::SAT);
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
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

inline void fp_bv_conversions(const camada::SMTSolverRef &solver,
                              camada::FPEncoding Encoding) {
  auto rtz = solver->mkRM(camada::RM::ROUND_TO_ZERO, Encoding);
  auto fp32 = solver->mkFP32Sort(Encoding);
  auto all_ones = solver->mkBVFromBin("11111111", 8);

  REQUIRE(rtz->getKind() == camada::SMTExprKind::RMConst);
  REQUIRE(all_ones->getKind() == camada::SMTExprKind::BVConst);

  auto signed_fp = solver->mkSBVtoFP(all_ones, fp32, rtz);
  auto unsigned_fp = solver->mkUBVtoFP(all_ones, fp32, rtz);
  REQUIRE(signed_fp->getKind() == camada::SMTExprKind::SBVtoFP);
  REQUIRE(unsigned_fp->getKind() == camada::SMTExprKind::UBVtoFP);

  auto minus_one = solver->mkFP32(-1.0f, Encoding);
  auto two_fifty_five = solver->mkFP32(255.0f, Encoding);
  solver->addConstraint(solver->mkEqual(signed_fp, minus_one));
  solver->addConstraint(solver->mkEqual(unsigned_fp, two_fifty_five));

  auto signed_bv = solver->mkFPtoSBV(signed_fp, 8);
  auto unsigned_bv = solver->mkFPtoUBV(unsigned_fp, 8);
  REQUIRE(signed_bv->getKind() == camada::SMTExprKind::FPtoSBV);
  REQUIRE(unsigned_bv->getKind() == camada::SMTExprKind::FPtoUBV);

  solver->addConstraint(solver->mkEqual(signed_bv, all_ones));
  solver->addConstraint(solver->mkEqual(unsigned_bv, all_ones));

  REQUIRE(solver->check() == camada::checkResult::SAT);
}

inline void fp_to_signed_bv_multiple_widths(const camada::SMTSolverRef &solver,
                                            camada::FPEncoding Encoding) {
  auto fp = solver->mkFP32(42.0f, Encoding);
  auto sbv32 = solver->mkFPtoSBV(fp, 32);

  REQUIRE(fp->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(sbv32->getKind() == camada::SMTExprKind::FPtoSBV);

  solver->addConstraint(solver->mkEqual(sbv32, solver->mkBVFromDec(42, 32)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  solver->reset();
  fp = solver->mkFP32(42.0f, Encoding);
  auto sbv64 = solver->mkFPtoSBV(fp, 64);
  REQUIRE(fp->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(sbv64->getKind() == camada::SMTExprKind::FPtoSBV);
  solver->addConstraint(solver->mkEqual(sbv64, solver->mkBVFromDec(42, 64)));
  REQUIRE(solver->check() == camada::checkResult::SAT);

  solver->reset();
  fp = solver->mkFP32(42.0f, Encoding);
  sbv32 = solver->mkFPtoSBV(fp, 32);
  sbv64 = solver->mkFPtoSBV(fp, 64);
  REQUIRE(fp->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(sbv32->getKind() == camada::SMTExprKind::FPtoSBV);
  REQUIRE(sbv64->getKind() == camada::SMTExprKind::FPtoSBV);
  solver->addConstraint(solver->mkEqual(sbv32, solver->mkBVFromDec(42, 32)));
  solver->addConstraint(solver->mkEqual(sbv64, solver->mkBVFromDec(42, 64)));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

inline void fp_denormal_round_to_integral(const camada::SMTSolverRef &solver,
                                          camada::FPEncoding Encoding) {
  auto pos_denorm =
      solver->mkFP32(std::numeric_limits<float>::denorm_min(), Encoding);
  auto neg_denorm =
      solver->mkFP32(-std::numeric_limits<float>::denorm_min(), Encoding);
  auto rtp = solver->mkRM(camada::RM::ROUND_TO_PLUS_INF, Encoding);
  auto rtn = solver->mkRM(camada::RM::ROUND_TO_MINUS_INF, Encoding);

  auto pos_rounded = solver->mkFPtoIntegral(pos_denorm, rtp);
  auto neg_rounded = solver->mkFPtoIntegral(neg_denorm, rtn);

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

  REQUIRE(solver->check() == camada::checkResult::SAT);
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

  REQUIRE(solver->check() == camada::checkResult::SAT);
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

  REQUIRE(solver->check() == camada::checkResult::SAT);
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
  REQUIRE(solver->check() == camada::checkResult::SAT);
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
  REQUIRE(solver->check() == camada::checkResult::SAT);
}
