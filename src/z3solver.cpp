
#include "z3solver.h"

#include <fmt/printf.h>

#ifdef SOLVER_Z3_ENABLED

/// Default constructor, mainly used by make_shared
camada::Z3Sort::Z3Sort(camada::Z3ContextRef C, z3::sort ZS)
    : Context(C), Sort(ZS) {}

bool camada::Z3Sort::isBitvectorSortImpl() const { return Sort.is_bv(); }

bool camada::Z3Sort::isBooleanSortImpl() const { return Sort.is_bool(); }

unsigned camada::Z3Sort::getBitvectorSortSizeImpl() const {
  return Sort.bv_size();
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
  assert(Z3_is_eq_sort(
             *Context, Z3_get_sort(*Context, AST),
             Z3_get_sort(*Context, static_cast<const Z3Expr &>(Other).AST)) &&
         "AST's must have the same sort");
  return Z3_is_eq_ast(*Context, AST, static_cast<const Z3Expr &>(Other).AST);
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

void camada::Z3Solver::addConstraint(const camada::SMTExprRef &Exp) const {
  Z3_solver_assert(*Context, Solver, toZ3Expr(*Exp).AST);
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

const std::string
camada::Z3Solver::getBitvector(const camada::SMTExprRef &Exp) {
  return std::string(Z3_get_numeral_string(*Context, toZ3Expr(*Exp).AST));
}

bool camada::Z3Solver::getBoolean(const camada::SMTExprRef &Exp) {
  return Z3_get_bool_value(*Context, toZ3Expr(*Exp).AST) == Z3_L_TRUE;
}

/// Given an expression, extract the value of this operand in the model.
bool camada::Z3Solver::getInterpretation(const camada::SMTExprRef &Exp,
                                         std::string &Inter) {
  if (!Solver.get_model().has_interp(toZ3Expr(*Exp).AST.decl()))
    return false;

  Inter = getBitvector(newExprRef(
      Z3Expr(Context,
             Solver.get_model().get_const_interp(toZ3Expr(*Exp).AST.decl()))));
  return true;
}

camada::checkResult camada::Z3Solver::check() const {
  Z3_lbool res = Z3_solver_check(*Context, Solver);
  if (res == Z3_L_TRUE)
    return camada::checkResult::SAT;

  if (res == Z3_L_FALSE)
    return camada::checkResult::UNSAT;

  return camada::checkResult::UNKNOWN;
}

void camada::Z3Solver::push() { return Z3_solver_push(*Context, Solver); }

void camada::Z3Solver::pop(unsigned NumStates) {
  assert(Z3_solver_get_num_scopes(*Context, Solver) >= NumStates);
  return Z3_solver_pop(*Context, Solver, NumStates);
}

/// Reset the solver and remove all constraints.
void camada::Z3Solver::reset() { Z3_solver_reset(*Context, Solver); }

void camada::Z3Solver::dump() const {
  fmt::print(stderr, "{}\n", Z3_solver_to_string(*Context, Solver));
}

void camada::Z3Solver::dumpModel() const {
  fmt::print(
      stderr, "{}\n",
      Z3_model_to_string(*Context, Z3_solver_get_model(*Context, Solver)));
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
