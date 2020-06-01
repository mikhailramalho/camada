
#include "z3solver.h"

#include <fmt/printf.h>

#ifdef SOLVER_Z3_ENABLED

/// Default constructor, mainly used by make_shared
camada::Z3Sort::Z3Sort(camada::Z3ContextRef C, z3::sort ZS)
    : Context(C), Sort(ZS) {}

bool camada::Z3Sort::isBitvectorSortImpl() const { return Sort.is_bv(); }

bool camada::Z3Sort::isBooleanSortImpl() const { return Sort.is_bool(); }

bool camada::Z3Sort::isFloatSortImpl() const { return Sort.is_fpa(); }

bool camada::Z3Sort::isRoundingModeSortImpl() const {
  return (Z3_get_sort_kind(*Context, Sort) == Z3_ROUNDING_MODE_SORT);
}

unsigned camada::Z3Sort::getBitvectorSortSizeImpl() const {
  return Sort.bv_size();
}

unsigned camada::Z3Sort::getFloatSortSizeImpl() const {
  return Sort.fpa_ebits() + Sort.fpa_sbits();
}

bool camada::Z3Sort::equal_to(camada::SMTSort const &Other) const {
  return Z3_is_eq_sort(*Context, Sort, static_cast<const Z3Sort &>(Other).Sort);
}

void camada::Z3Sort::dump() const {
  fmt::print(stderr, "{}\n", Z3_sort_to_string(*Context, Sort));
}

camada::Z3Expr::Z3Expr(camada::Z3ContextRef C, z3::expr ZA)
    : camada::SMTExpr(), Context(C), AST(ZA) {}

/// Comparison of AST equality, not model equivalence.
bool camada::Z3Expr::equal_to(camada::SMTExpr const &Other) const {
  assert(Z3_is_eq_sort(*Context, AST.get_sort(),
                       static_cast<const Z3Expr &>(Other).AST.get_sort()) &&
         "AST's must have the same sort");
  return z3::eq(AST, static_cast<const Z3Expr &>(Other).AST);
}

void camada::Z3Expr::dump() const {
  fmt::print(stderr, "{}\n", Z3_ast_to_string(*Context, AST));
}

// Function used to report errors
void Z3ErrorHandler(Z3_context Context, Z3_error_code Error) {
  fmt::print(stderr, "Z3 error: {}\n",
             std::string(Z3_get_error_msg(Context, Error)));
}

camada::Z3Solver::Z3Solver(Z3ContextRef C) : Context(C), Solver(*Context) {
  Z3_set_error_handler(*Context, Z3ErrorHandler);
}

camada::Z3Solver::Z3Solver(Z3ContextRef C, z3::solver S)
    : Context(C), Solver(S) {
  Z3_set_error_handler(*Context, Z3ErrorHandler);
}

void camada::Z3Solver::addConstraint(const camada::SMTExprRef &Exp) {
  Solver.add(toZ3Expr(*Exp).AST);
}

camada::SMTSortRef
camada::Z3Solver::newSortRef(const camada::SMTSort &Sort) const {
  return std::make_shared<Z3Sort>(toZ3Sort(Sort));
}

camada::SMTExprRef
camada::Z3Solver::newExprRef(const camada::SMTExpr &Exp) const {
  return std::make_shared<Z3Expr>(toZ3Expr(Exp));
}

camada::SMTSortRef camada::Z3Solver::getBoolSort() {
  return newSortRef(Z3Sort(Context, Context->bool_sort()));
}

camada::SMTSortRef camada::Z3Solver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef(Z3Sort(Context, Context->bv_sort(BitWidth)));
}

camada::SMTSortRef camada::Z3Solver::getRoundingModeSort() {
  return newSortRef(Z3Sort(
      Context, z3::to_sort(*Context, Z3_mk_fpa_rounding_mode_sort(*Context))));
}

camada::SMTSortRef camada::Z3Solver::getFloatSort(const unsigned ExpWidth,
                                                  const unsigned SigWidth) {
  return newSortRef(Z3Sort(Context, Context->fpa_sort(ExpWidth, SigWidth)));
}

camada::SMTSortRef camada::Z3Solver::getSort(const camada::SMTExprRef &Exp) {
  return newSortRef(Z3Sort(Context, toZ3Expr(*Exp).AST.get_sort()));
}

camada::SMTExprRef camada::Z3Solver::mkBVNeg(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, -toZ3Expr(*Exp).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVNot(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, ~toZ3Expr(*Exp).AST));
}

camada::SMTExprRef camada::Z3Solver::mkNot(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, !toZ3Expr(*Exp).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVAdd(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST + toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVSub(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST - toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVMul(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST * toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVSRem(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::srem(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVURem(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::urem(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSDiv(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST / toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVUDiv(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::udiv(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVShl(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::shl(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVAshr(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ashr(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVLshr(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::lshr(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVXor(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST ^ toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVOr(const camada::SMTExprRef &LHS,
                                            const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST | toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVAnd(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST & toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVUlt(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ult(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSlt(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::slt(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVUgt(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ugt(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSgt(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST > toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkBVUle(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ule(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSle(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::sle(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVUge(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::uge(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSge(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST >= toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkAnd(const camada::SMTExprRef &LHS,
                                           const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST && toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkOr(const camada::SMTExprRef &LHS,
                                          const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST || toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkEqual(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST == toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkIte(const camada::SMTExprRef &Cond,
                                           const camada::SMTExprRef &T,
                                           const camada::SMTExprRef &F) {
  return newExprRef(
      Z3Expr(Context,
             z3::ite(toZ3Expr(*Cond).AST, toZ3Expr(*T).AST, toZ3Expr(*F).AST)));
}

camada::SMTExprRef
camada::Z3Solver::mkBVSignExt(unsigned i, const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, z3::sext(toZ3Expr(*Exp).AST, i)));
}

camada::SMTExprRef
camada::Z3Solver::mkBVZeroExt(unsigned i, const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, z3::zext(toZ3Expr(*Exp).AST, i)));
}

camada::SMTExprRef
camada::Z3Solver::mkBVExtract(unsigned High, unsigned Low,
                              const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*Exp).AST.extract(High, Low)));
}

camada::SMTExprRef camada::Z3Solver::mkBVConcat(const camada::SMTExprRef &LHS,
                                                const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::concat(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkFPNeg(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, -toZ3Expr(*Exp).AST));
}

camada::SMTExprRef
camada::Z3Solver::mkFPIsInfinite(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_is_infinite(
                                         *Context, toZ3Expr(*Exp).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPIsNaN(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_is_nan(*Context, toZ3Expr(*Exp).AST))));
}

camada::SMTExprRef
camada::Z3Solver::mkFPIsNormal(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context,
                           Z3_mk_fpa_is_normal(*Context, toZ3Expr(*Exp).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPIsZero(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_is_zero(*Context, toZ3Expr(*Exp).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPMul(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS,
                                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_mul(*Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPDiv(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS,
                                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_div(*Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPRem(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::rem(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkFPAdd(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS,
                                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_add(*Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPSub(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS,
                                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_sub(*Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPSqrt(const camada::SMTExprRef &Exp,
                                              const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context,
                           Z3_mk_fpa_sqrt(*Context, toZ3Expr(*roundingMode).AST,
                                          toZ3Expr(*Exp).AST))));
};

camada::SMTExprRef camada::Z3Solver::mkFPFMA(const camada::SMTExprRef &X,
                                             const camada::SMTExprRef &Y,
                                             const camada::SMTExprRef &Z,
                                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_fma(*Context, toZ3Expr(*roundingMode).AST,
                                          toZ3Expr(*Z).AST, toZ3Expr(*Y).AST,
                                          toZ3Expr(*Z).AST))));
};

camada::SMTExprRef camada::Z3Solver::mkFPLt(const camada::SMTExprRef &LHS,
                                            const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST < toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkFPGt(const camada::SMTExprRef &LHS,
                                            const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST > toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkFPLe(const camada::SMTExprRef &LHS,
                                            const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST <= toZ3Expr(*RHS).AST));
}

camada::SMTExprRef camada::Z3Solver::mkFPGe(const camada::SMTExprRef &LHS,
                                            const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_geq(*Context, toZ3Expr(*LHS).AST,
                                                   toZ3Expr(*RHS).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPEqual(const camada::SMTExprRef &LHS,
                                               const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_eq(*Context, toZ3Expr(*LHS).AST,
                                                  toZ3Expr(*RHS).AST))));
}

camada::SMTExprRef camada::Z3Solver::mkFPtoFP(const camada::SMTExprRef &From,
                                              const SMTSortRef &To,
                                              const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_to_fp_float(
                                *Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*From).AST, toZ3Sort(*To).Sort))));
}

camada::SMTExprRef camada::Z3Solver::mkSBVtoFP(const camada::SMTExprRef &From,
                                               const SMTSortRef &To,
                                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_to_fp_signed(
                                *Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*From).AST, toZ3Sort(*To).Sort))));
}

camada::SMTExprRef camada::Z3Solver::mkUBVtoFP(const camada::SMTExprRef &From,
                                               const SMTSortRef &To,
                                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_to_fp_unsigned(
                                *Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*From).AST, toZ3Sort(*To).Sort))));
}

camada::SMTExprRef camada::Z3Solver::mkFPtoSBV(const camada::SMTExprRef &From,
                                               unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_sbv(
                                         *Context, toZ3Expr(*roundingMode).AST,
                                         toZ3Expr(*From).AST, ToWidth))));
}

camada::SMTExprRef camada::Z3Solver::mkFPtoUBV(const camada::SMTExprRef &From,
                                               unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_ubv(
                                         *Context, toZ3Expr(*roundingMode).AST,
                                         toZ3Expr(*From).AST, ToWidth))));
}

camada::SMTExprRef
camada::Z3Solver::mkFPtoIntegral(const camada::SMTExprRef &From,
                                 RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_round_to_integral(
                                         *Context, toZ3Expr(*roundingMode).AST,
                                         toZ3Expr(*From).AST))));
};

bool camada::Z3Solver::getBoolean(const camada::SMTExprRef &Exp) {
  return toZ3Expr(*Exp).AST.bool_value();
}

const std::string
camada::Z3Solver::getBitvector(const camada::SMTExprRef &Exp) {
  std::string bv;
  bool is_num = toZ3Expr(*Exp).AST.is_numeral(bv);
  assert(is_num && "Failed to get bitvector from Z3");
  return bv;
}

template <typename FPType, typename IntType,
          bool (*Z3Func)(Z3_context c, Z3_ast v, IntType *i)>
static inline FPType getFP(const camada::Z3ContextRef C, const z3::model Model,
                           const camada::SMTExprRef &Exp) {
  // TODO: what about negative NaN?
  if (Z3_fpa_is_numeral_nan(*C, toZ3Expr(*Exp).AST))
    return NAN;

  if (Z3_fpa_is_numeral_inf(*C, toZ3Expr(*Exp).AST))
    return Z3_fpa_is_numeral_positive(*C, toZ3Expr(*Exp).AST) ? INFINITY
                                                              : -INFINITY;

  // Convert the float to bv
  Z3_ast fp_value;
  bool eval = Z3_model_eval(
      *C, Model, Z3_mk_fpa_to_ieee_bv(*C, toZ3Expr(*Exp).AST), 1, &fp_value);
  assert(eval && "Failed to convert FP to BV in Z3");

  IntType FP_as_int;
  (*Z3Func)(*C, fp_value, &FP_as_int);

  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  assert(sizeof(float) == sizeof(int32_t));

  FPType result;
  memcpy(&result, &FP_as_int, sizeof(FPType));
  return result;
}

const float camada::Z3Solver::getFloat(const camada::SMTExprRef &Exp) {
  return getFP<float, int32_t, Z3_get_numeral_int>(Context, Solver.get_model(),
                                                   Exp);
}

const double camada::Z3Solver::getDouble(const camada::SMTExprRef &Exp) {
  return getFP<double, int64_t, Z3_get_numeral_int64>(Context,
                                                      Solver.get_model(), Exp);
}

bool camada::Z3Solver::getInterpretation(const camada::SMTExprRef &Exp,
                                         std::string &Inter) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).AST.decl()))
    return false;

  Inter = getBitvector(newExprRef(
      Z3Expr(Context,
             Solver.get_model().get_const_interp(toZ3Expr(*Exp).AST.decl()))));
  return true;
}

bool camada::Z3Solver::getInterpretation(const camada::SMTExprRef &Exp,
                                         float &Float) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).AST.decl()))
    return false;

  Float =
      getFloat(newExprRef(Z3Expr(Context, Solver.get_model().get_const_interp(
                                              toZ3Expr(*Exp).AST.decl()))));
  return true;
}

bool camada::Z3Solver::getInterpretation(const camada::SMTExprRef &Exp,
                                         double &Double) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).AST.decl()))
    return false;

  Double =
      getDouble(newExprRef(Z3Expr(Context, Solver.get_model().get_const_interp(
                                               toZ3Expr(*Exp).AST.decl()))));
  return true;
}

camada::SMTExprRef camada::Z3Solver::mkBoolean(const bool b) {
  return newExprRef(Z3Expr(Context, Context->bool_val(b)));
}

camada::SMTExprRef camada::Z3Solver::mkBitvector(const std::string &Int,
                                                 unsigned BitWidth) {
  return newExprRef(Z3Expr(Context, Context->bv_val(Int.c_str(), BitWidth)));
}

camada::SMTExprRef camada::Z3Solver::mkSymbol(const char *Name,
                                              camada::SMTSortRef Sort) {
  return newExprRef(
      Z3Expr(Context, Context->constant(Name, toZ3Sort(*Sort).Sort)));
}

camada::SMTExprRef camada::Z3Solver::mkFP(const float Float) {
  return newExprRef(Z3Expr(Context, Context->fpa_val(Float)));
}

camada::SMTExprRef camada::Z3Solver::mkFP(const double Double) {
  return newExprRef(Z3Expr(Context, Context->fpa_val(Double)));
}

camada::SMTExprRef camada::Z3Solver::mkRoundingMode(const RoundingMode R) {
  switch (R) {
  default:
    assert(0 && "Unsupported floating-point semantics!");
    break;
  case RoundingMode::ROUND_TO_EVEN:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rne(*Context))));
  case RoundingMode::ROUND_TO_AWAY:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rna(*Context))));
  case RoundingMode::ROUND_TO_PLUS_INF:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rtp(*Context))));
  case RoundingMode::ROUND_TO_MINUS_INF:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rtn(*Context))));
  case RoundingMode::ROUND_TO_ZERO:
    return newExprRef(
        Z3Expr(Context, z3::to_expr(*Context, Z3_mk_fpa_rtz(*Context))));
  }
}

camada::SMTExprRef camada::Z3Solver::mkNaN(const bool Sgn,
                                           const unsigned ExpWidth,
                                           const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  SMTExprRef theNaN = newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_nan(*Context, toZ3Sort(*sort).Sort))));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

camada::SMTExprRef camada::Z3Solver::mkInf(const bool Sgn,
                                           const unsigned ExpWidth,
                                           const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  return newExprRef(
      Z3Expr(Context,
             z3::to_expr(*Context,
                         Z3_mk_fpa_inf(*Context, toZ3Sort(*sort).Sort, Sgn))));
}

camada::checkResult camada::Z3Solver::check() {
  z3::check_result res = Solver.check();
  if (res == z3::check_result::sat)
    return camada::checkResult::SAT;

  if (res == z3::check_result::unsat)
    return camada::checkResult::UNSAT;

  return camada::checkResult::UNKNOWN;
}

void camada::Z3Solver::push() { return Solver.push(); }

void camada::Z3Solver::pop(unsigned NumStates) { return Solver.pop(NumStates); }

/// Reset the solver and remove all constraints.
void camada::Z3Solver::reset() { Solver.reset(); }

void camada::Z3Solver::dump() const {
  fmt::print(stderr, "{}\n", Z3_solver_to_string(*Context, Solver));
}

void camada::Z3Solver::dumpModel() const {
  fmt::print(stderr, "{}\n", Z3_model_to_string(*Context, Solver.get_model()));
}

#endif

camada::SMTSolverRef camada::createZ3Solver() {
#if SOLVER_Z3_ENABLED
  return std::make_shared<Z3Solver>(std::make_shared<z3::context>());
#else
  fmt::print(stderr, "Camada was not compiled with Z3 support, rebuild with "
                     "-DCAMADA_ENABLE_SOLVER_Z3=ON\n");
  abort();
#endif
}
