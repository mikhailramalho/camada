
#include "z3solver.h"

#include <fmt/printf.h>

#ifdef SOLVER_Z3_ENABLED

/// Default constructor, mainly used by make_shared
camada::Z3Sort::Z3Sort(camada::Z3ContextRef C, Z3_sort ZS)
    : Context(C), Sort(ZS) {
  Z3_inc_ref(*Context, reinterpret_cast<Z3_ast>(Sort));
}

/// implicit copy constructor for correct reference counting.
camada::Z3Sort::Z3Sort(const camada::Z3Sort &Other)
    : Context(Other.Context), Sort(Other.Sort) {
  Z3_inc_ref(*Context, reinterpret_cast<Z3_ast>(Sort));
}

/// implicit copy assignment constructor for correct reference
/// counting.
camada::Z3Sort &camada::Z3Sort::operator=(const camada::Z3Sort &Other) {
  Z3_inc_ref(*Context, reinterpret_cast<Z3_ast>(Other.Sort));
  Z3_dec_ref(*Context, reinterpret_cast<Z3_ast>(Sort));
  Sort = Other.Sort;
  return *this;
}

camada::Z3Sort::~Z3Sort() {
  if (Sort)
    Z3_dec_ref(*Context, reinterpret_cast<Z3_ast>(Sort));
}

bool camada::Z3Sort::isBitvectorSortImpl() const {
  return (Z3_get_sort_kind(*Context, Sort) == Z3_BV_SORT);
}

bool camada::Z3Sort::isBooleanSortImpl() const {
  return (Z3_get_sort_kind(*Context, Sort) == Z3_BOOL_SORT);
}

unsigned camada::Z3Sort::getBitvectorSortSizeImpl() const {
  return Z3_get_bv_sort_size(*Context, Sort);
}

bool camada::Z3Sort::equal_to(camada::SMTSort const &Other) const {
  return Z3_is_eq_sort(*Context, Sort, static_cast<const Z3Sort &>(Other).Sort);
}

void camada::Z3Sort::dump() const {
  fmt::print(stderr, "{}\n", Z3_sort_to_string(*Context, Sort));
}

camada::Z3Expr::Z3Expr(camada::Z3ContextRef C, Z3_ast ZA)
    : camada::SMTExpr(), Context(C), AST(ZA) {
  Z3_inc_ref(*Context, AST);
}

/// implicit copy constructor for correct reference counting.
camada::Z3Expr::Z3Expr(const camada::Z3Expr &Copy)
    : camada::SMTExpr(), Context(Copy.Context), AST(Copy.AST) {
  Z3_inc_ref(*Context, AST);
}

/// implicit copy assignment constructor for correct reference
/// counting.
camada::Z3Expr &camada::Z3Expr::operator=(const camada::Z3Expr &Other) {
  Z3_inc_ref(*Context, Other.AST);
  Z3_dec_ref(*Context, AST);
  AST = Other.AST;
  return *this;
}

camada::Z3Expr::~Z3Expr() {
  if (AST)
    Z3_dec_ref(*Context, AST);
}

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

camada::Z3Model::Z3Model(camada::Z3ContextRef C, Z3_model ZM)
    : Context(C), Model(ZM) {
  Z3_model_inc_ref(*Context, Model);
}

camada::Z3Model::~Z3Model() {
  if (Model)
    Z3_model_dec_ref(*Context, Model);
}

void camada::Z3Model::dump() const {
  fmt::print(stderr, "{}\n", Z3_model_to_string(*Context, Model));
}

camada::Z3Tactic::Z3Tactic(Z3ContextRef C, Z3_tactic T)
    : Context(C), Tactic(T) {
  Z3_tactic_inc_ref(*Context, Tactic);
}

camada::Z3Tactic::~Z3Tactic() {
  if (Tactic)
    Z3_tactic_dec_ref(*Context, Tactic);
}

// Function used to report errors
void Z3ErrorHandler(Z3_context Context, Z3_error_code Error) {
  fmt::print(stderr, "Z3 error: {}\n",
             std::string(Z3_get_error_msg(Context, Error)));
}

camada::Z3Solver::Z3Solver(Z3ContextRef C)
    : Context(C), Solver(Z3_mk_simple_solver(*Context)) {

  Z3_set_error_handler(*Context, Z3ErrorHandler);

  Z3_solver_inc_ref(*Context, Solver);
}

camada::Z3Solver::~Z3Solver() {
  if (Solver)
    Z3_solver_dec_ref(*Context, Solver);
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
  return newSortRef(Z3Sort(Context, Z3_mk_bool_sort(*Context)));
}

camada::SMTSortRef camada::Z3Solver::getBitvectorSort(unsigned BitWidth) {
  return newSortRef(Z3Sort(Context, Z3_mk_bv_sort(*Context, BitWidth)));
}

camada::SMTSortRef camada::Z3Solver::getSort(const camada::SMTExprRef &Exp) {
  return newSortRef(Z3Sort(Context, Z3_get_sort(*Context, toZ3Expr(*Exp).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVNeg(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, Z3_mk_bvneg(*Context, toZ3Expr(*Exp).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVNot(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, Z3_mk_bvnot(*Context, toZ3Expr(*Exp).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkNot(const camada::SMTExprRef &Exp) {
  return newExprRef(Z3Expr(Context, Z3_mk_not(*Context, toZ3Expr(*Exp).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVAdd(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvadd(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSub(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvsub(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVMul(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvmul(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSRem(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvsrem(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVURem(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvurem(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSDiv(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvsdiv(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVUDiv(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvudiv(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVShl(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvshl(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVAshr(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvashr(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVLshr(const camada::SMTExprRef &LHS,
                                              const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvlshr(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVXor(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvxor(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVOr(const camada::SMTExprRef &LHS,
                                            const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvor(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVAnd(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvand(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVUlt(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvult(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSlt(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvslt(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVUgt(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvugt(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSgt(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvsgt(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVUle(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvule(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSle(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvsle(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVUge(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvuge(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVSge(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_bvsge(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkAnd(const camada::SMTExprRef &LHS,
                                           const camada::SMTExprRef &RHS) {
  Z3_ast Args[2] = {toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST};
  return newExprRef(Z3Expr(Context, Z3_mk_and(*Context, 2, Args)));
}

camada::SMTExprRef camada::Z3Solver::mkOr(const camada::SMTExprRef &LHS,
                                          const camada::SMTExprRef &RHS) {
  Z3_ast Args[2] = {toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST};
  return newExprRef(Z3Expr(Context, Z3_mk_or(*Context, 2, Args)));
}

camada::SMTExprRef camada::Z3Solver::mkEqual(const camada::SMTExprRef &LHS,
                                             const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_eq(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkIte(const camada::SMTExprRef &Cond,
                                           const camada::SMTExprRef &T,
                                           const camada::SMTExprRef &F) {
  return newExprRef(
      Z3Expr(Context, Z3_mk_ite(*Context, toZ3Expr(*Cond).AST, toZ3Expr(*T).AST,
                                toZ3Expr(*F).AST)));
}

camada::SMTExprRef
camada::Z3Solver::mkBVSignExt(unsigned i, const camada::SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Z3_mk_sign_ext(*Context, i, toZ3Expr(*Exp).AST)));
}

camada::SMTExprRef
camada::Z3Solver::mkBVZeroExt(unsigned i, const camada::SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Z3_mk_zero_ext(*Context, i, toZ3Expr(*Exp).AST)));
}

camada::SMTExprRef
camada::Z3Solver::mkBVExtract(unsigned High, unsigned Low,
                              const camada::SMTExprRef &Exp) {
  return newExprRef(
      Z3Expr(Context, Z3_mk_extract(*Context, High, Low, toZ3Expr(*Exp).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBVConcat(const camada::SMTExprRef &LHS,
                                                const camada::SMTExprRef &RHS) {
  return newExprRef(Z3Expr(
      Context, Z3_mk_concat(*Context, toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST)));
}

camada::SMTExprRef camada::Z3Solver::mkBoolean(const bool b) {
  return newExprRef(
      Z3Expr(Context, b ? Z3_mk_true(*Context) : Z3_mk_false(*Context)));
}

camada::SMTExprRef camada::Z3Solver::mkBitvector(const std::string Int,
                                                 unsigned BitWidth) {
  const camada::SMTSortRef Sort = getBitvectorSort(BitWidth);
  return newExprRef(Z3Expr(
      Context, Z3_mk_numeral(*Context, Int.c_str(), toZ3Sort(*Sort).Sort)));
}

camada::SMTExprRef camada::Z3Solver::mkSymbol(const char *Name,
                                              camada::SMTSortRef Sort) {
  return newExprRef(
      Z3Expr(Context, Z3_mk_const(*Context, Z3_mk_string_symbol(*Context, Name),
                                  toZ3Sort(*Sort).Sort)));
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
  Z3Model Model(Context, Z3_solver_get_model(*Context, Solver));
  Z3_func_decl Func =
      Z3_get_app_decl(*Context, Z3_to_app(*Context, toZ3Expr(*Exp).AST));
  if (Z3_model_has_interp(*Context, Model.Model, Func) != Z3_L_TRUE)
    return false;

  Inter = getBitvector(newExprRef(
      Z3Expr(Context, Z3_model_get_const_interp(*Context, Model.Model, Func))));
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
