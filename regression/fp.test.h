
#include "camada.h"

#include <catch2/catch_test_macros.hpp>
#include <cmath>

inline void fp_arithmetics(const camada::SMTSolverRef &solver) {
  auto x = solver->mkFP32(0.750000059604644775390625f);
  auto y = solver->mkFP32(0.750000059604644775390625f);
  REQUIRE(x->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(y->getKind() == camada::SMTExprKind::FPConst);

  auto zero = solver->mkFP32(0.f);
  auto one = solver->mkFP32(1.f);
  auto two = solver->mkFP32(2.f);
  REQUIRE(zero->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(one->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(two->getKind() == camada::SMTExprKind::FPConst);

  auto r = solver->mkRM(camada::RM::ROUND_TO_EVEN);
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
  auto mul = solver->mkFP32(0.562500119209f);
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

inline void fp_round_to_away(const camada::SMTSolverRef &solver) {
  const std::string solverName = solver->getSolverNameAndVersion();
  if (solverName.find("MathSAT") != std::string::npos ||
      solverName.find("STP") != std::string::npos)
    return;

  auto one = solver->mkFP32(1.0f);
  auto half_ulp = solver->mkFP32(std::ldexp(1.0f, -24));
  auto rne = solver->mkRM(camada::RM::ROUND_TO_EVEN);
  auto rna = solver->mkRM(camada::RM::ROUND_TO_AWAY);

  REQUIRE(one->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(half_ulp->getKind() == camada::SMTExprKind::FPConst);
  REQUIRE(rne->getKind() == camada::SMTExprKind::RMConst);
  REQUIRE(rna->getKind() == camada::SMTExprKind::RMConst);

  auto even_sum = solver->mkFPAdd(one, half_ulp, rne);
  auto away_sum = solver->mkFPAdd(one, half_ulp, rna);
  REQUIRE(even_sum->getKind() == camada::SMTExprKind::FPAdd);
  REQUIRE(away_sum->getKind() == camada::SMTExprKind::FPAdd);

  auto even_expected = solver->mkFP32(1.0f);
  auto away_expected = solver->mkFP32(std::nextafterf(1.0f, 2.0f));

  solver->addConstraint(solver->mkEqual(even_sum, even_expected));
  solver->addConstraint(solver->mkEqual(away_sum, away_expected));
  REQUIRE(solver->check() == camada::checkResult::SAT);
}

inline void fp_bv_conversions(const camada::SMTSolverRef &solver) {
  auto rtz = solver->mkRM(camada::RM::ROUND_TO_ZERO);
  auto fp32 = solver->mkFP32Sort();
  auto all_ones = solver->mkBVFromBin("11111111", 8);

  REQUIRE(rtz->getKind() == camada::SMTExprKind::RMConst);
  REQUIRE(all_ones->getKind() == camada::SMTExprKind::BVConst);

  auto signed_fp = solver->mkSBVtoFP(all_ones, fp32, rtz);
  auto unsigned_fp = solver->mkUBVtoFP(all_ones, fp32, rtz);
  REQUIRE(signed_fp->getKind() == camada::SMTExprKind::SBVtoFP);
  REQUIRE(unsigned_fp->getKind() == camada::SMTExprKind::UBVtoFP);

  auto minus_one = solver->mkFP32(-1.0f);
  auto two_fifty_five = solver->mkFP32(255.0f);
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
