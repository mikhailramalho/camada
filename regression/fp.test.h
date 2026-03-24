
#include "camada.h"

#include <catch2/catch_test_macros.hpp>

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
