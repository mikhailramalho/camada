#include "mathsatsolver.h"
#include "ac_config.h"

#include <fmt/printf.h>
#include <gmp.h>

using namespace camada;

#ifdef SOLVER_MATHSAT_ENABLED

/// Default constructor, mainly used by make_shared
MathSATSort::MathSATSort(MathSATContextRef C, const msat_type &MS)
    : Context(std::move(C)), Sort(MS) {}

bool MathSATSort::isBitvectorSortImpl() const {
  std::size_t w;
  return msat_is_bv_type(*Context, Sort, &w);
}

bool MathSATSort::isBooleanSortImpl() const {
  return msat_is_bool_type(*Context, Sort);
}

bool MathSATSort::isFloatSortImpl() const {
  std::size_t exp, sig;
  return msat_is_fp_type(*Context, Sort, &exp, &sig);
}

bool MathSATSort::isRoundingModeSortImpl() const {
  return msat_is_fp_roundingmode_type(*Context, Sort);
}

unsigned MathSATSort::getBitvectorSortSizeImpl() const {
  std::size_t w;
  msat_is_bv_type(*Context, Sort, &w);
  return w;
}

unsigned MathSATSort::getFloatSortSizeImpl() const {
  std::size_t exp, sig;
  msat_is_fp_type(*Context, Sort, &exp, &sig);
  return exp + sig + 1;
}

bool MathSATSort::equal_to(SMTSort const &Other) const {
  return msat_type_equals(Sort, dynamic_cast<const MathSATSort &>(Other).Sort);
}

void MathSATSort::dump() const {
  char *s = msat_type_repr(Sort);
  fmt::print(stderr, "{}\n", s);
  msat_free(s);
}

MathSATExpr::MathSATExpr(MathSATContextRef C, const msat_term &MA)
    : Context(std::move(C)), AST(MA) {}

/// Comparison of AST equality, not model equivalence.
bool MathSATExpr::equal_to(SMTExpr const &Other) const {
  camada::abortCondWithMessage(
      msat_type_equals(
          msat_term_get_type(AST),
          msat_term_get_type(dynamic_cast<const MathSATExpr &>(Other).AST)),
      "AST's must have the same sort");
  return (msat_term_id(AST) ==
          msat_term_id(dynamic_cast<const MathSATExpr &>(Other).AST));
}

void MathSATExpr::dump() const {
  char *ast = msat_to_smtlib2(*Context, AST);
  fmt::print(stderr, "{}\n", ast);
  msat_free(ast);
}

MathSATSolver::MathSATSolver() {
  msat_config cfg = msat_create_config();
  msat_set_option(cfg, "model_generation", "true");
  Context = std::make_shared<msat_env>(msat_create_env(cfg));
  msat_destroy_config(cfg);
}

MathSATSolver::MathSATSolver(const msat_config &Config)
    : Context(std::make_shared<msat_env>(msat_create_env(Config))) {}

MathSATSolver::~MathSATSolver() {
  msat_destroy_env(*Context);
  Context = nullptr;
}

void MathSATSolver::addConstraint(const SMTExprRef &Exp) {
  msat_assert_formula(*Context, toMathSATExpr(*Exp).AST);
}

SMTSortRef MathSATSolver::newSortRef(const SMTSort &Sort) const {
  abortCondWithMessage(!MSAT_ERROR_TYPE(toMathSATSort(Sort).Sort),
                       "Error when creating MathSAT sort.");
  return std::make_shared<MathSATSort>(toMathSATSort(Sort));
}

SMTExprRef MathSATSolver::newExprRef(const SMTExpr &Exp) const {
  abortCondWithMessage(!MSAT_ERROR_TERM(toMathSATExpr(Exp).AST),
                       "Error when creating MathSAT expr.");
  return std::make_shared<MathSATExpr>(toMathSATExpr(Exp));
}

SMTSortRef MathSATSolver::getBoolSort() {
  return newSortRef(MathSATSort(Context, msat_get_bool_type(*Context)));
}

SMTSortRef MathSATSolver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef(MathSATSort(Context, msat_get_bv_type(*Context, BitWidth)));
}

SMTSortRef MathSATSolver::getRoundingModeSort() {
  return newSortRef(
      MathSATSort(Context, msat_get_fp_roundingmode_type(*Context)));
}

SMTSortRef MathSATSolver::getFloatSort(const unsigned ExpWidth,
                                       const unsigned SigWidth) {
  return newSortRef(
      MathSATSort(Context, msat_get_fp_type(*Context, ExpWidth, SigWidth)));
}

SMTSortRef MathSATSolver::getSort(const SMTExprRef &Exp) {
  return newSortRef(
      MathSATSort(Context, msat_term_get_type(toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_bv_neg(*Context, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_bv_not(*Context, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, msat_make_not(*Context, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkBVAdd(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_plus(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVSub(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_minus(*Context, toMathSATExpr(*LHS).AST,
                                              toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVMul(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_times(*Context, toMathSATExpr(*LHS).AST,
                                           toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVSRem(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_srem(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVURem(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_urem(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVSDiv(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_sdiv(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVUDiv(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_udiv(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVShl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_lshl(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVAshr(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_ashr(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVLshr(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_lshr(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVXor(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_xor(*Context, toMathSATExpr(*LHS).AST,
                                            toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_or(*Context, toMathSATExpr(*LHS).AST,
                                           toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVAnd(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_and(*Context, toMathSATExpr(*LHS).AST,
                                            toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVUlt(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_ult(*Context, toMathSATExpr(*LHS).AST,
                                            toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVSlt(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_slt(*Context, toMathSATExpr(*LHS).AST,
                                            toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVUle(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_uleq(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkBVSle(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_sleq(*Context, toMathSATExpr(*LHS).AST,
                                             toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_and(*Context, toMathSATExpr(*LHS).AST,
                                         toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_or(*Context, toMathSATExpr(*LHS).AST,
                                        toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkEqual(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_eq(*Context, toMathSATExpr(*LHS).AST,
                                        toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                                const SMTExprRef &F) {
  if (getSort(T)->isBooleanSort())
    return mkOr(mkAnd(Cond, T), mkAnd(mkNot(Cond), F));

  return newExprRef(MathSATExpr(
      Context,
      msat_make_term_ite(*Context, toMathSATExpr(*Cond).AST,
                         toMathSATExpr(*T).AST, toMathSATExpr(*F).AST)));
}

SMTExprRef MathSATSolver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_bv_sext(*Context, i, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_bv_zext(*Context, i, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkBVExtract(unsigned High, unsigned Low,
                                      const SMTExprRef &Exp) {
  return newExprRef(
      MathSATExpr(Context, msat_make_bv_extract(*Context, High, Low,
                                                toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkBVConcat(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return newExprRef(MathSATExpr(
      Context, msat_make_bv_concat(*Context, toMathSATExpr(*LHS).AST,
                                   toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkFPNeg(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_neg(*Context, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkFPIsInfinite(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_isinf(*Context, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkFPIsNaN(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_isnan(*Context, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkFPIsNormal(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_isnormal(*Context, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkFPIsZero(const SMTExprRef &Exp) {
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_iszero(*Context, toMathSATExpr(*Exp).AST)));
}

SMTExprRef MathSATSolver::mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context,
      msat_make_fp_times(*Context, toMathSATExpr(*roundingMode).AST,
                         toMathSATExpr(*LHS).AST, toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context,
      msat_make_fp_div(*Context, toMathSATExpr(*roundingMode).AST,
                       toMathSATExpr(*LHS).AST, toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkFPRem(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  abortWithMessage("MathSAT does not implement fp.rem");
}

SMTExprRef MathSATSolver::mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context,
      msat_make_fp_plus(*Context, toMathSATExpr(*roundingMode).AST,
                        toMathSATExpr(*LHS).AST, toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                  const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context,
      msat_make_fp_minus(*Context, toMathSATExpr(*roundingMode).AST,
                         toMathSATExpr(*LHS).AST, toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkFPSqrt(const SMTExprRef &Exp,
                                   const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_sqrt(*Context, toMathSATExpr(*roundingMode).AST,
                                 toMathSATExpr(*Exp).AST)));
};

SMTExprRef MathSATSolver::mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                                  const SMTExprRef &Z, const RoundingMode R) {
  abortWithMessage("MathSAT does not implement fp.fma");
};

SMTExprRef MathSATSolver::mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_fp_lt(*Context, toMathSATExpr(*LHS).AST,
                                           toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_fp_leq(*Context, toMathSATExpr(*LHS).AST,
                                            toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkFPEqual(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return newExprRef(
      MathSATExpr(Context, msat_make_fp_equal(*Context, toMathSATExpr(*LHS).AST,
                                              toMathSATExpr(*RHS).AST)));
}

SMTExprRef MathSATSolver::mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                                   const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  std::size_t ExpWidth, MantWidth;
  msat_is_fp_type(*Context, toMathSATSort(*To).Sort, &ExpWidth, &MantWidth);
  return newExprRef(
      MathSATExpr(Context, msat_make_fp_cast(*Context, ExpWidth, MantWidth,
                                             toMathSATExpr(*roundingMode).AST,
                                             toMathSATExpr(*From).AST)));
}

SMTExprRef MathSATSolver::mkSBVtoFP(const SMTExprRef &From,
                                    const SMTSortRef &To,
                                    const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  std::size_t ExpWidth, MantWidth;
  msat_is_fp_type(*Context, toMathSATSort(*To).Sort, &ExpWidth, &MantWidth);
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_from_sbv(*Context, ExpWidth, MantWidth,
                                     toMathSATExpr(*roundingMode).AST,
                                     toMathSATExpr(*From).AST)));
}

SMTExprRef MathSATSolver::mkUBVtoFP(const SMTExprRef &From,
                                    const SMTSortRef &To,
                                    const RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  std::size_t ExpWidth, MantWidth;
  msat_is_fp_type(*Context, toMathSATSort(*To).Sort, &ExpWidth, &MantWidth);
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_from_ubv(*Context, ExpWidth, MantWidth,
                                     toMathSATExpr(*roundingMode).AST,
                                     toMathSATExpr(*From).AST)));
}

SMTExprRef MathSATSolver::mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(
      MathSATExpr(Context, msat_make_fp_to_bv(*Context, ToWidth,
                                              toMathSATExpr(*roundingMode).AST,
                                              toMathSATExpr(*From).AST)));
}

SMTExprRef MathSATSolver::mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) {
  // Conversion from float to integers always truncate, so we assume
  // the round mode to be toward zero
  SMTExprRef roundingMode = mkRoundingMode(RoundingMode::ROUND_TO_ZERO);
  return newExprRef(
      MathSATExpr(Context, msat_make_fp_to_bv(*Context, ToWidth,
                                              toMathSATExpr(*roundingMode).AST,
                                              toMathSATExpr(*From).AST)));
}

SMTExprRef MathSATSolver::mkFPtoIntegral(const SMTExprRef &From,
                                         RoundingMode R) {
  SMTExprRef roundingMode = mkRoundingMode(R);
  return newExprRef(MathSATExpr(
      Context,
      msat_make_fp_round_to_int(*Context, toMathSATExpr(*roundingMode).AST,
                                toMathSATExpr(*From).AST)));
}

bool MathSATSolver::getBoolean(const SMTExprRef &Exp) {
  if (msat_term_is_true(*Context, toMathSATExpr(*Exp).AST))
    return true;

  if (msat_term_is_false(*Context, toMathSATExpr(*Exp).AST))
    return false;

  abortWithMessage("Boolean is neither true nor false");
}

// TODO: Can we unify getBitvector with the float template? The only
// difference if the number of arguments in strtol
int64_t MathSATSolver::getBitvector(const SMTExprRef &Exp) {
  SMTExprRef t = newExprRef(MathSATExpr(
      Context, msat_get_model_value(*Context, toMathSATExpr(*Exp).AST)));

  // GMP rational value object.
  mpq_t val;
  mpq_init(val);
  msat_term_to_number(*toMathSATExpr(*t).Context, toMathSATExpr(*t).AST, val);

  mpz_t num;
  mpz_init(num);
  mpz_set(num, mpq_numref(val));
  mpq_clear(val);

  char buffer[mpz_sizeinbase(num, 10) + 2];
  mpz_get_str(buffer, 10, num);
  mpz_clear(num);

  camada::abortCondWithMessage(sizeof(int64_t) == sizeof(long int),
                               "Cannot convert GMP val to int");

  char *foo = buffer;
  int64_t finval = strtol(buffer, &foo, 10);

  if (buffer[0] != '\0' && (foo == buffer || *foo != '\0'))
    camada::abortWithMessage(
        "Couldn't parse string representation of Bitvector");

  return finval;
}

template <typename ResType, typename StrToFuncType,
          StrToFuncType (*StrToFunc)(const char *, char **)>
static inline ResType GMPtoType(SMTExprRef t) {
  // GMP rational value object.
  mpq_t val;
  mpq_init(val);
  msat_term_to_number(*toMathSATExpr(*t).Context, toMathSATExpr(*t).AST, val);

  mpz_t num;
  mpz_init(num);
  mpz_set(num, mpq_numref(val));
  mpq_clear(val);

  char buffer[mpz_sizeinbase(num, 10) + 2];
  mpz_get_str(buffer, 10, num);
  mpz_clear(num);

  camada::abortCondWithMessage(sizeof(ResType) == sizeof(StrToFuncType),
                               "Cannot convert GMP val to int");

  char *foo = buffer;
  ResType finval = StrToFunc(buffer, &foo);

  if (buffer[0] != '\0' && (foo == buffer || *foo != '\0'))
    camada::abortWithMessage(
        "Couldn't parse string representation of Bitvector");

  return finval;
}

float MathSATSolver::getFloat(const SMTExprRef &Exp) {
  SMTExprRef t = newExprRef(MathSATExpr(
      Context, msat_get_model_value(*Context, toMathSATExpr(*Exp).AST)));
  return GMPtoType<float, float, std::strtof>(t);
}

double MathSATSolver::getDouble(const SMTExprRef &Exp) {
  SMTExprRef t = newExprRef(MathSATExpr(
      Context, msat_get_model_value(*Context, toMathSATExpr(*Exp).AST)));
  return GMPtoType<double, double, std::strtod>(t);
}

bool MathSATSolver::getInterpretation(const SMTExprRef &Exp, int64_t &Inter) {
  // TODO: MathSAT never fails?
  Inter = getBitvector(Exp);
  return true;
}

bool MathSATSolver::getInterpretation(const SMTExprRef &Exp, float &Float) {
  // TODO: MathSAT never fails?
  Float = getFloat(Exp);
  return true;
}

bool MathSATSolver::getInterpretation(const SMTExprRef &Exp, double &Double) {
  // TODO: MathSAT never fails?
  Double = getDouble(Exp);
  return true;
}

SMTExprRef MathSATSolver::mkBoolean(const bool Bool) {
  return newExprRef(MathSATExpr(Context, Bool ? msat_make_true(*Context)
                                              : msat_make_false(*Context)));
}

SMTExprRef MathSATSolver::mkBitvector(const int64_t Int, unsigned BitWidth) {
  return newExprRef(MathSATExpr(
      Context, msat_make_bv_number(*Context, std::to_string(Int).c_str(),
                                   BitWidth, 10)));
}

SMTExprRef MathSATSolver::mkSymbol(const char *Name, SMTSortRef Sort) {
  msat_decl d =
      msat_declare_function(*Context, Name, toMathSATSort(*Sort).Sort);
  abortCondWithMessage(!MSAT_ERROR_DECL(d),
                       "Invalid function symbol declaration sort");

  return newExprRef(MathSATExpr(Context, msat_make_constant(*Context, d)));
}

template <typename FPType, typename IntType>
static inline std::string FPasInt(const FPType FP) {
  // Convert the integer to float/double
  // We assume that floats are 32 bits long and doubles are 64 bits long
  camada::abortCondWithMessage(sizeof(FPType) == sizeof(IntType),
                               "Cannot convert int to floating-point");

  IntType FPAsInt;
  memcpy(&FPAsInt, &FP, sizeof(FPType));
  return std::to_string(FPAsInt);
}

SMTExprRef MathSATSolver::mkFloat(const float Float) {
  return newExprRef(MathSATExpr(
      Context, msat_make_fp_bits_number(
                   *Context, FPasInt<float, int32_t>(Float).c_str(), 8, 24)));
}

SMTExprRef MathSATSolver::mkDouble(const double Double) {
  return newExprRef(MathSATExpr(
      Context,
      msat_make_fp_bits_number(
          *Context, FPasInt<double, int64_t>(Double).c_str(), 11, 53)));
}

SMTExprRef MathSATSolver::mkRoundingMode(const RoundingMode R) {
  switch (R) {
  case RoundingMode::ROUND_TO_EVEN:
    return newExprRef(
        MathSATExpr(Context, msat_make_fp_roundingmode_nearest_even(*Context)));
  case RoundingMode::ROUND_TO_PLUS_INF:
    return newExprRef(
        MathSATExpr(Context, msat_make_fp_roundingmode_plus_inf(*Context)));
  case RoundingMode::ROUND_TO_MINUS_INF:
    return newExprRef(
        MathSATExpr(Context, msat_make_fp_roundingmode_minus_inf(*Context)));
  case RoundingMode::ROUND_TO_ZERO:
    return newExprRef(
        MathSATExpr(Context, msat_make_fp_roundingmode_zero(*Context)));
  default:;
  }
  camada::abortWithMessage("Unsupported floating-point semantics.");
}

SMTExprRef MathSATSolver::mkNaN(const bool Sgn, const unsigned ExpWidth,
                                const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth);
  SMTExprRef theNaN = newExprRef(
      MathSATExpr(Context, msat_make_fp_nan(*Context, ExpWidth, SigWidth - 1)));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef MathSATSolver::mkInf(const bool Sgn, const unsigned ExpWidth,
                                const unsigned SigWidth) {
  SMTSortRef sort = getFloatSort(ExpWidth, SigWidth - 1);
  return newExprRef(MathSATExpr(
      Context, Sgn ? msat_make_fp_minus_inf(*Context, ExpWidth, SigWidth - 1)
                   : msat_make_fp_plus_inf(*Context, ExpWidth, SigWidth - 1)));
}

checkResult MathSATSolver::check() {
  msat_result res = msat_solve(*Context);
  if (res == MSAT_SAT)
    return checkResult::SAT;

  if (res == MSAT_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void MathSATSolver::push() { msat_push_backtrack_point(*Context); }

void MathSATSolver::pop(unsigned NumStates) {
  while (NumStates--)
    msat_pop_backtrack_point(*Context);
}

void MathSATSolver::reset() { msat_reset_env(*Context); }

void MathSATSolver::dump() {
  size_t num_of_asserted;
  msat_term *asserted_formulas =
      msat_get_asserted_formulas(*Context, &num_of_asserted);

  for (unsigned i = 0; i < num_of_asserted; i++)
    fmt::print(stderr, "{}\n", msat_to_smtlib2(*Context, asserted_formulas[i]));
  msat_free(asserted_formulas);
}

void MathSATSolver::dumpModel() {
  // we use a model iterator to retrieve the model values for all the
  // variables, and the necessary function instantiations
  msat_model_iterator iter = msat_create_model_iterator(*Context);
  assert(!MSAT_ERROR_MODEL_ITERATOR(iter));

  fmt::print(stderr, "Model:\n");
  while (msat_model_iterator_has_next(iter)) {
    msat_term t, v;
    char *s;
    msat_model_iterator_next(iter, &t, &v);
    s = msat_term_repr(t);
    assert(s);
    fmt::print(stderr, "{} = ", s);
    msat_free(s);
    s = msat_term_repr(v);
    assert(s);
    fmt::print(stderr, "{}\n", s);
    msat_free(s);
  }
  msat_destroy_model_iterator(iter);
}

#endif

SMTSolverRef camada::createMathSATSolver() {
#if SOLVER_MATHSAT_ENABLED
  return std::make_shared<MathSATSolver>();
#else
  fmt::print(stderr,
             "Camada was not compiled with MathSAT support, rebuild with "
             "-DCAMADA_ENABLE_SOLVER_MATHSAT=ON\n");
  abort();
#endif
}
