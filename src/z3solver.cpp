#include "z3solver.h"

#include <fmt/printf.h>

using namespace camada;

#ifdef SOLVER_Z3_ENABLED

/// Default constructor, mainly used by make_shared
Z3Sort::Z3Sort(Z3ContextRef C, const z3::sort &ZS)
    : Context(std::move(C)), Sort(ZS) {}

bool Z3Sort::isBitvectorSortImpl() const { return Sort.is_bv(); }

bool Z3Sort::isBooleanSortImpl() const { return Sort.is_bool(); }

bool Z3Sort::isFloatSortImpl() const { return Sort.is_fpa(); }

bool Z3Sort::isRoundingModeSortImpl() const {
  return (Z3_get_sort_kind(*Context, Sort) == Z3_ROUNDING_MODE_SORT);
}

unsigned Z3Sort::getBitvectorSortSizeImpl() const { return Sort.bv_size(); }

unsigned Z3Sort::getFloatSortSizeImpl() const {
  return Sort.fpa_ebits() + Sort.fpa_sbits();
}

bool Z3Sort::equal_to(SMTSort const &Other) const {
  return Z3_is_eq_sort(*Context, Sort,
                       dynamic_cast<const Z3Sort &>(Other).Sort);
}

void Z3Sort::dump() const {
  fmt::print(stderr, "{}\n", Z3_sort_to_string(*Context, Sort));
}

Z3Expr::Z3Expr(Z3ContextRef C, const z3::expr &ZA)
    : Context(std::move(C)), AST(ZA) {}

/// Comparison of AST equality, not model equivalence.
bool Z3Expr::equal_to(SMTExpr const &Other) const {
  camada::abortCondWithMessage(
      "AST's must have the same sort",
      Z3_is_eq_sort(*Context, AST.get_sort(),
                    dynamic_cast<const Z3Expr &>(Other).AST.get_sort()));
  return z3::eq(AST, dynamic_cast<const Z3Expr &>(Other).AST);
}

void Z3Expr::dump() const {
  fmt::print(stderr, "{}\n", Z3_ast_to_string(*Context, AST));
}

// Function used to report errors
void Z3ErrorHandler(Z3_context Context, Z3_error_code Error) {
  fmt::print(stderr, "Z3 error: {}\n",
             std::string(Z3_get_error_msg(Context, Error)));
}

Z3Solver::Z3Solver(Z3ContextRef C) : Context(std::move(C)), Solver(*Context) {
  Z3_set_error_handler(*Context, Z3ErrorHandler);
}

Z3Solver::Z3Solver(Z3ContextRef C, const z3::solver &S)
    : Context(std::move(C)), Solver(S) {
  Z3_set_error_handler(*Context, Z3ErrorHandler);
}

void Z3Solver::addConstraint(const SMTExprRef &Exp) {
  Solver.add(toZ3Expr(*Exp).AST);
}

SMTSortRef Z3Solver::newSortRef(const SMTSort &Sort) const {
  return std::make_shared<Z3Sort>(toZ3Sort(Sort));
}

SMTExprRef Z3Solver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<Z3Expr>(toZ3Expr(Exp));
}

SMTSortRef Z3Solver::getBoolSort() {
  return newSortRef(Z3Sort(Context, Context->bool_sort()));
}

SMTSortRef Z3Solver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef(Z3Sort(Context, Context->bv_sort(BitWidth)));
}

SMTSortRef Z3Solver::getRoundingModeSort() {
  return newSortRef(Z3Sort(
      Context, z3::to_sort(*Context, Z3_mk_fpa_rounding_mode_sort(*Context))));
}

SMTSortRef Z3Solver::getFloatSort(const unsigned ExpWidth,
                                  const unsigned SigWidth) {
  return newSortRef(Z3Sort(Context, Context->fpa_sort(ExpWidth, SigWidth)));
}

SMTSortRef Z3Solver::getSort(const SMTExprRef &Exp) {
  return newSortRef(Z3Sort(Context, toZ3Expr(*Exp).AST.get_sort()));
}

SMTExprRef Z3Solver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, -toZ3Expr(*Exp).AST));
}

SMTExprRef Z3Solver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, ~toZ3Expr(*Exp).AST));
}

SMTExprRef Z3Solver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, !toZ3Expr(*Exp).AST));
}

SMTExprRef Z3Solver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST + toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST - toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST * toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::srem(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::urem(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST / toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::udiv(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::shl(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ashr(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::lshr(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST ^ toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST | toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST & toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ult(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::slt(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ugt(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST > toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::ule(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::sle(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::uge(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST >= toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST && toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST || toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST == toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                           const SMTExprRef &F) {
  return newExprRef(
      Z3Expr(Context,
             z3::ite(toZ3Expr(*Cond).AST, toZ3Expr(*T).AST, toZ3Expr(*F).AST)));
}

SMTExprRef Z3Solver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, z3::sext(toZ3Expr(*Exp).AST, i)));
}

SMTExprRef Z3Solver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, z3::zext(toZ3Expr(*Exp).AST, i)));
}

SMTExprRef Z3Solver::mkBVExtract(unsigned High, unsigned Low,
                                 const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*Exp).AST.extract(High, Low)));
}

SMTExprRef Z3Solver::mkBVConcat(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::concat(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkFPNeg(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, -toZ3Expr(*Exp).AST));
}

SMTExprRef Z3Solver::mkFPIsInfinite(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_is_infinite(
                                         *Context, toZ3Expr(*Exp).AST))));
}

SMTExprRef Z3Solver::mkFPIsNaN(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_is_nan(*Context, toZ3Expr(*Exp).AST))));
}

SMTExprRef Z3Solver::mkFPIsNormal(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context,
                           Z3_mk_fpa_is_normal(*Context, toZ3Expr(*Exp).AST))));
}

SMTExprRef Z3Solver::mkFPIsZero(const SMTExprRef &Exp) {
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_is_zero(*Context, toZ3Expr(*Exp).AST))));
}

SMTExprRef Z3Solver::mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_mul(*Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST))));
}

SMTExprRef Z3Solver::mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_div(*Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST))));
}

SMTExprRef Z3Solver::mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      Z3Expr(Context, z3::rem(toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

SMTExprRef Z3Solver::mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_add(*Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST))));
}

SMTExprRef Z3Solver::mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context,
                  Z3_mk_fpa_sub(*Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST))));
}

SMTExprRef Z3Solver::mkFPSqrt(const SMTExprRef &Exp, const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context,
                           Z3_mk_fpa_sqrt(*Context, toZ3Expr(*roundingMode).AST,
                                          toZ3Expr(*Exp).AST))));
};

SMTExprRef Z3Solver::mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z, const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_fma(*Context, toZ3Expr(*roundingMode).AST,
                                          toZ3Expr(*X).AST, toZ3Expr(*Y).AST,
                                          toZ3Expr(*Z).AST))));
};

SMTExprRef Z3Solver::mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST < toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST > toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(Context, toZ3Expr(*LHS).AST <= toZ3Expr(*RHS).AST));
}

SMTExprRef Z3Solver::mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_geq(*Context, toZ3Expr(*LHS).AST,
                                                   toZ3Expr(*RHS).AST))));
}

SMTExprRef Z3Solver::mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_eq(*Context, toZ3Expr(*LHS).AST,
                                                  toZ3Expr(*RHS).AST))));
}

SMTExprRef Z3Solver::mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_to_fp_float(
                                *Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*From).AST, toZ3Sort(*To).Sort))));
}

SMTExprRef Z3Solver::mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_to_fp_signed(
                                *Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*From).AST, toZ3Sort(*To).Sort))));
}

SMTExprRef Z3Solver::mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_to_fp_unsigned(
                                *Context, toZ3Expr(*roundingMode).AST,
                                toZ3Expr(*From).AST, toZ3Sort(*To).Sort))));
}

SMTExprRef Z3Solver::mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_sbv(
                                         *Context, toZ3Expr(*roundingMode).AST,
                                         toZ3Expr(*From).AST, ToWidth))));
}

SMTExprRef Z3Solver::mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_to_ubv(
                                         *Context, toZ3Expr(*roundingMode).AST,
                                         toZ3Expr(*From).AST, ToWidth))));
}

SMTExprRef Z3Solver::mkFPtoIntegral(const SMTExprRef &From, RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(Z3Expr(
      Context, z3::to_expr(*Context, Z3_mk_fpa_round_to_integral(
                                         *Context, toZ3Expr(*roundingMode).AST,
                                         toZ3Expr(*From).AST))));
};

bool Z3Solver::getBoolean(const SMTExprRef &Exp) {
  return toZ3Expr(*Exp).AST.bool_value();
}

std::string Z3Solver::getBitvector(const SMTExprRef &Exp) {
  std::string bv;
  bool is_num = toZ3Expr(*Exp).AST.is_numeral(bv);
  camada::abortCondWithMessage("Failed to get bitvector from Z3", is_num);
  return bv;
}

template <typename FPType, typename IntType,
          bool (*Z3Func)(Z3_context c, Z3_ast v, IntType *i)>
static inline FPType getFP(const Z3ContextRef &C, const z3::model &Model,
                           const SMTExprRef &Exp) {
  // TODO: what about negative NaN?
  if (Z3_fpa_is_numeral_nan(*C, toZ3Expr(*Exp).AST))
    return NAN;

  if (Z3_fpa_is_numeral_inf(*C, toZ3Expr(*Exp).AST))
    return Z3_fpa_is_numeral_positive(*C, toZ3Expr(*Exp).AST) ? INFINITY
                                                              : -INFINITY;

  // Convert the float to bv
  Z3_ast fp_value;
  bool eval = Z3_model_eval(
      *C, Model, Z3_mk_fpa_to_ieee_bv(*C, toZ3Expr(*Exp).AST), true, &fp_value);
  camada::abortCondWithMessage("Failed to convert FP to BV in Z3", eval);

  IntType FP_as_int;
  (*Z3Func)(*C, fp_value, &FP_as_int);

  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  camada::abortCondWithMessage("Cannot convert int to floating-point",
                               sizeof(FPType) == sizeof(IntType));

  FPType result;
  memcpy(&result, &FP_as_int, sizeof(FPType));
  return result;
}

float Z3Solver::getFloat(const SMTExprRef &Exp) {
  return getFP<float, int32_t, Z3_get_numeral_int>(Context, Solver.get_model(),
                                                   Exp);
}

double Z3Solver::getDouble(const SMTExprRef &Exp) {
  return getFP<double, int64_t, Z3_get_numeral_int64>(Context,
                                                      Solver.get_model(), Exp);
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, std::string &Inter) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).AST.decl()))
    return false;

  Inter = getBitvector(newExprRef(
      Z3Expr(Context,
             Solver.get_model().get_const_interp(toZ3Expr(*Exp).AST.decl()))));
  return true;
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, float &Float) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).AST.decl()))
    return false;

  Float =
      getFloat(newExprRef(Z3Expr(Context, Solver.get_model().get_const_interp(
                                              toZ3Expr(*Exp).AST.decl()))));
  return true;
}

bool Z3Solver::getInterpretation(const SMTExprRef &Exp, double &Double) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).AST.decl()))
    return false;

  Double =
      getDouble(newExprRef(Z3Expr(Context, Solver.get_model().get_const_interp(
                                               toZ3Expr(*Exp).AST.decl()))));
  return true;
}

SMTExprRef Z3Solver::mkBoolean(const bool b) {
  return newExprRef(Z3Expr(Context, Context->bool_val(b)));
}

SMTExprRef Z3Solver::mkBitvector(const std::string &Int, unsigned BitWidth) {
  return newExprRef(Z3Expr(Context, Context->bv_val(Int.c_str(), BitWidth)));
}

SMTExprRef Z3Solver::mkSymbol(const char *Name, SMTSortRef Sort) {
  return newExprRef(
      Z3Expr(Context, Context->constant(Name, toZ3Sort(*Sort).Sort)));
}

SMTExprRef Z3Solver::mkFP(const float Float) {
  return newExprRef(Z3Expr(Context, Context->fpa_val(Float)));
}

SMTExprRef Z3Solver::mkFP(const double Double) {
  return newExprRef(Z3Expr(Context, Context->fpa_val(Double)));
}

SMTExprRef Z3Solver::mkRoundingMode(const RoundingMode R) {
  switch (R) {
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
  default:;
  }
  camada::abortCondWithMessage("Unsupported floating-point semantics.");
}

SMTExprRef Z3Solver::mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  SMTExprRef theNaN = newExprRef(Z3Expr(
      Context,
      z3::to_expr(*Context, Z3_mk_fpa_nan(*Context, toZ3Sort(*sort).Sort))));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef Z3Solver::mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  return newExprRef(
      Z3Expr(Context,
             z3::to_expr(*Context,
                         Z3_mk_fpa_inf(*Context, toZ3Sort(*sort).Sort, Sgn))));
}

checkResult Z3Solver::check() {
  z3::check_result res = Solver.check();
  if (res == z3::check_result::sat)
    return checkResult::SAT;

  if (res == z3::check_result::unsat)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void Z3Solver::push() { return Solver.push(); }

void Z3Solver::pop(unsigned NumStates) { return Solver.pop(NumStates); }

/// Reset the solver and remove all constraints.
void Z3Solver::reset() { Solver.reset(); }

void Z3Solver::dump() const {
  fmt::print(stderr, "{}\n", Z3_solver_to_string(*Context, Solver));
}

void Z3Solver::dumpModel() const {
  fmt::print(stderr, "{}\n", Z3_model_to_string(*Context, Solver.get_model()));
}

#endif

SMTSolverRef camada::createZ3Solver() {
#if SOLVER_Z3_ENABLED
  return std::make_shared<Z3Solver>(std::make_shared<z3::context>());
#else
  fmt::print(stderr, "Camada was not compiled with Z3 support, rebuild with "
                     "-DCAMADA_ENABLE_SOLVER_Z3=ON\n");
  abort();
#endif
}
