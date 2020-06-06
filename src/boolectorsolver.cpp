
#include "boolectorsolver.h"
#include "ac_config.h"

#include <fmt/printf.h>

using namespace camada;

#ifdef SOLVER_BOOLECTOR_ENABLED

// Function used to report errors
void BtorErrorHandler(const char *msg) {
  fmt::print(stderr, "Btor error: {}\n", msg);
}

BtorContext::BtorContext() : Context(nullptr) {
  boolector_set_abort(BtorErrorHandler);
  createAndConfig();
}

void BtorContext::createAndConfig() {
  Context = boolector_new();
  boolector_set_opt(Context, BTOR_OPT_MODEL_GEN, 1);
  boolector_set_opt(Context, BTOR_OPT_AUTO_CLEANUP, 1);
}

BtorContext::~BtorContext() {
  boolector_release_all(Context);
  boolector_delete(Context);
  Context = nullptr;
}

void BtorContext::reset() {
  boolector_release_all(Context);
  boolector_delete(Context);
  Context = nullptr;
  createAndConfig();
}

BtorSort::BtorSort(BtorContextRef C, const BoolectorSort &BS)
    : Context(std::move(C)), Sort(BS) {}

bool BtorSort::isBitvectorSortImpl() const {
  return boolector_is_bitvec_sort(Context->Context, Sort);
}

bool BtorSort::isBooleanSortImpl() const {
  // There is not is_boolean_sort, so we need to check if the sort is not
  // everything else
  return !(boolector_is_bitvec_sort(Context->Context, Sort) &&
           boolector_is_fun_sort(Context->Context, Sort) &&
           boolector_is_array_sort(Context->Context, Sort));
}

bool BtorSort::isFloatSortImpl() const {
  // Always false: btor does not support fp
  return false;
}

bool BtorSort::isRoundingModeSortImpl() const {
  // Always false: btor does not support fp
  return false;
}

unsigned BtorSort::getBitvectorSortSizeImpl() const {
  return boolector_bitvec_sort_get_width(Context->Context, Sort);
}

unsigned BtorSort::getFloatSortSizeImpl() const {
  // Returning 0 should trigger a failure in camada::getFloatSortSize()
  return 0;
}

bool BtorSort::equal_to(SMTSort const &Other) const {
  // boolector  API does not provide equality function for sort
  const BtorSort &bs = dynamic_cast<const BtorSort &>(Other);
  if (isBooleanSortImpl() && bs.isBooleanSortImpl())
    return true;

  if (isBitvectorSortImpl() && bs.isBitvectorSortImpl() &&
      (getBitvectorSortSizeImpl() == bs.getBitvectorSortSizeImpl()))
    return true;

  // TODO: add here checks for arrays and uninterpreted functions if necessary
  return false;
}

BtorExpr::BtorExpr(BtorContextRef C, BoolectorNode *BA)
    : Context(std::move(C)), AST(BA) {}

bool BtorExpr::equal_to(SMTExpr const &Other) const {
  camada::abortCondWithMessage(
      boolector_is_equal_sort(Context->Context, AST,
                              dynamic_cast<const BtorExpr &>(Other).AST),
      "AST's must have the same sort");
  return (boolector_get_node_id(Context->Context, AST) ==
          boolector_get_node_id(Context->Context,
                                dynamic_cast<const BtorExpr &>(Other).AST));
}

void BtorExpr::dump() const {
  boolector_dump_smt2_node(Context->Context, stderr, AST);
}

BtorSolver::BtorSolver() : Context(std::make_shared<BtorContext>()) {}

BtorSolver::BtorSolver(BtorContextRef C) : Context(std::move(C)) {}

void BtorSolver::addConstraint(const SMTExprRef &Exp) {
  boolector_assert(Context->Context, toBtorExpr(*Exp).AST);
}

SMTSortRef BtorSolver::newSortRef(const SMTSort &Sort) const {
  return std::make_shared<BtorSort>(toBtorSort(Sort));
}

SMTExprRef BtorSolver::newExprRef(const SMTExpr &Exp) const {
  return std::make_shared<BtorExpr>(toBtorExpr(Exp));
}

SMTSortRef BtorSolver::getBoolSort() {
  return newSortRef(BtorSort(Context, boolector_bool_sort(Context->Context)));
}

SMTSortRef BtorSolver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef(
      BtorSort(Context, boolector_bitvec_sort(Context->Context, BitWidth)));
}

SMTSortRef BtorSolver::getRoundingModeSort() {
  abortWithMessage("Boolector does not support fp");
}

SMTSortRef BtorSolver::getFloatSort(const unsigned, const unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTSortRef BtorSolver::getSort(const SMTExprRef &Exp) {
  return newSortRef(BtorSort(
      Context, boolector_get_sort(Context->Context, toBtorExpr(*Exp).AST)));
}

SMTExprRef BtorSolver::mkBVNeg(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, boolector_neg(Context->Context, toBtorExpr(*Exp).AST)));
}

SMTExprRef BtorSolver::mkBVNot(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, boolector_not(Context->Context, toBtorExpr(*Exp).AST)));
}

SMTExprRef BtorSolver::mkNot(const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, boolector_not(Context->Context, toBtorExpr(*Exp).AST)));
}

SMTExprRef BtorSolver::mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_add(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_sub(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_mul(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_srem(Context->Context, toBtorExpr(*LHS).AST,
                                       toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_urem(Context->Context, toBtorExpr(*LHS).AST,
                                       toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_sdiv(Context->Context, toBtorExpr(*LHS).AST,
                                       toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_udiv(Context->Context, toBtorExpr(*LHS).AST,
                                       toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_sll(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_sra(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_srl(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_xor(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_or(Context->Context, toBtorExpr(*LHS).AST,
                                     toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_and(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_ult(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_slt(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_ugt(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_sgt(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_ugte(Context->Context, toBtorExpr(*LHS).AST,
                                       toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_slte(Context->Context, toBtorExpr(*LHS).AST,
                                       toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_ugte(Context->Context, toBtorExpr(*LHS).AST,
                                       toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_sgte(Context->Context, toBtorExpr(*LHS).AST,
                                       toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_and(Context->Context, toBtorExpr(*LHS).AST,
                                      toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_or(Context->Context, toBtorExpr(*LHS).AST,
                                     toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_eq(Context->Context, toBtorExpr(*LHS).AST,
                                     toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                             const SMTExprRef &F) {
  return newExprRef(BtorExpr(
      Context, boolector_cond(Context->Context, toBtorExpr(*Cond).AST,
                              toBtorExpr(*T).AST, toBtorExpr(*F).AST)));
}

SMTExprRef BtorSolver::mkBVSignExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, boolector_sext(Context->Context, toBtorExpr(*Exp).AST, i)));
}

SMTExprRef BtorSolver::mkBVZeroExt(unsigned i, const SMTExprRef &Exp) {
  return newExprRef(BtorExpr(
      Context, boolector_uext(Context->Context, toBtorExpr(*Exp).AST, i)));
}

SMTExprRef BtorSolver::mkBVExtract(unsigned High, unsigned Low,
                                   const SMTExprRef &Exp) {
  return newExprRef(
      BtorExpr(Context, boolector_slice(Context->Context, toBtorExpr(*Exp).AST,
                                        High, Low)));
}

SMTExprRef BtorSolver::mkBVConcat(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return newExprRef(
      BtorExpr(Context, boolector_concat(Context->Context, toBtorExpr(*LHS).AST,
                                         toBtorExpr(*RHS).AST)));
}

SMTExprRef BtorSolver::mkFPNeg(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsInfinite(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsNaN(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsNormal(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPIsZero(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPMul(const SMTExprRef &, const SMTExprRef &,
                               const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPDiv(const SMTExprRef &, const SMTExprRef &,
                               const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPRem(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPAdd(const SMTExprRef &, const SMTExprRef &,
                               const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPSub(const SMTExprRef &, const SMTExprRef &,
                               const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPSqrt(const SMTExprRef &, const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPFMA(const SMTExprRef &, const SMTExprRef &,
                               const SMTExprRef &, const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPLt(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPGt(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPLe(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPGe(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPEqual(const SMTExprRef &, const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPtoFP(const SMTExprRef &, const SMTSortRef &,
                                const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkSBVtoFP(const SMTExprRef &, const SMTSortRef &,
                                 const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkUBVtoFP(const SMTExprRef &, const SMTSortRef &,
                                 const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPtoSBV(const SMTExprRef &, unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPtoUBV(const SMTExprRef &, unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkFPtoIntegral(const SMTExprRef &, RoundingMode) {
  abortWithMessage("Boolector does not support fp");
};

bool BtorSolver::getBoolean(const SMTExprRef &Exp) {
  const char *boolean =
      boolector_bv_assignment(Context->Context, toBtorExpr(*Exp).AST);

  abortCondWithMessage(boolean != nullptr,
                       "Boolector returned null bv assignment string");
  bool res;
  switch (*boolean) {
  case '1':
    res = true;
    break;
  case '0':
    res = false;
    break;
  default:
    abortWithMessage(
        "Boolector returned digit other than 0 or 1 for a boolean");
  }

  boolector_free_bv_assignment(Context->Context, boolean);
  return res;
}

int64_t BtorSolver::getBitvector(const SMTExprRef &Exp) {
  const char *bv =
      boolector_bv_assignment(Context->Context, toBtorExpr(*Exp).AST);
  char *foo;
  int64_t finval = strtol(bv, &foo, 10);

  if (bv[0] != '\0' && (foo == bv || *foo != '\0'))
    camada::abortWithMessage(
        "Couldn't parse string representation of Bitvector");

  return finval;
}

float BtorSolver::getFloat(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

double BtorSolver::getDouble(const SMTExprRef &) {
  abortWithMessage("Boolector does not support fp");
}

bool BtorSolver::getInterpretation(const SMTExprRef &Exp, int64_t &Inter) {
  // TODO: Boolector never fails?
  Inter = getBitvector(Exp);
  return true;
}

bool BtorSolver::getInterpretation(const SMTExprRef &, float &) {
  abortWithMessage("Boolector does not support fp");
}

bool BtorSolver::getInterpretation(const SMTExprRef &, double &) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkBoolean(const bool b) {
  return newExprRef(BtorExpr(Context, b ? boolector_true(Context->Context)
                                        : boolector_false(Context->Context)));
}

SMTExprRef BtorSolver::mkBitvector(const int64_t Int, unsigned BitWidth) {
  const SMTSortRef Sort = getBitvectorSort(BitWidth);
  return newExprRef(BtorExpr(
      Context, boolector_constd(Context->Context, toBtorSort(*Sort).Sort,
                                std::to_string(Int).c_str())));
}

SMTExprRef BtorSolver::mkSymbol(const char *Name, SMTSortRef Sort) {
  auto it = SymbolTable.find(Name);
  if (it != SymbolTable.end())
    return it->second;

  auto inserted = SymbolTable.insert(SymbolTablet::value_type(
      Name, newExprRef(BtorExpr(Context,
                                boolector_var(Context->Context,
                                              toBtorSort(*Sort).Sort, Name)))));

  abortCondWithMessage(inserted.second,
                       "Could not cache new Boolector variable");

  return inserted.first->second;
}

SMTExprRef BtorSolver::mkFloat(const float) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkDouble(const double) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkRoundingMode(const RoundingMode) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkNaN(const bool, const unsigned, const unsigned) {
  abortWithMessage("Boolector does not support fp");
}

SMTExprRef BtorSolver::mkInf(const bool, const unsigned, const unsigned) {
  abortWithMessage("Boolector does not support fp");
}

checkResult BtorSolver::check() {
  int res = boolector_sat(Context->Context);
  if (res == BOOLECTOR_SAT)
    return checkResult::SAT;

  if (res == BOOLECTOR_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void BtorSolver::push() { boolector_push(Context->Context, 1); }

void BtorSolver::pop(unsigned NumStates) {
  boolector_pop(Context->Context, NumStates);
}

void BtorSolver::reset() { Context.reset(); }

void BtorSolver::dump() { boolector_dump_smt2(Context->Context, stderr); }

void BtorSolver::dumpModel() {
  boolector_print_model(Context->Context, const_cast<char *>("smt2"), stderr);
}

#endif

SMTSolverRef camada::createBoolectorSolver() {
#if SOLVER_BOOLECTOR_ENABLED
  return std::make_shared<BtorSolver>();
#else
  fmt::print(stderr, "Camada was not compiled with Boolector support, rebuild "
                     "with -DCAMADA_ENABLE_SOLVER_BOOLECTOR=ON\n");
  abort();
#endif
}