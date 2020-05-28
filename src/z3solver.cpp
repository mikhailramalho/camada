#include "ac_config.h"
#include "camada.h"

#if SOLVER_Z3_ENABLED

#include <fmt/printf.h>
#include <z3.h>

namespace {

/// Configuration class for Z3
class Z3Config {
  friend class Z3Context;

  Z3_config Config;

public:
  Z3Config() : Config(Z3_mk_config()) {
    // Enable model finding
    Z3_set_param_value(Config, "model", "true");
    // Disable proof generation
    Z3_set_param_value(Config, "proof", "false");
    // Set timeout to 15000ms = 15s
    Z3_set_param_value(Config, "timeout", "15000");
  }

  ~Z3Config() { Z3_del_config(Config); }
}; // end class Z3Config

// Function used to report errors
void Z3ErrorHandler(Z3_context Context, Z3_error_code Error) {
  fmt::print(stderr,
             "Z3 error: " + std::string(Z3_get_error_msg(Context, Error)));
}

/// Wrapper for Z3 context
class Z3Context {
public:
  Z3_context Context;

  Z3Context() {
    Context = Z3_mk_context_rc(Z3Config().Config);
    // The error function is set here because the context is the first object
    // created by the backend
    Z3_set_error_handler(Context, Z3ErrorHandler);
  }

  virtual ~Z3Context() {
    Z3_del_context(Context);
    Context = nullptr;
  }
}; // end class Z3Context

/// Wrapper for Z3 Sort
class Z3Sort : public camada::SMTSort {
  friend class Z3Solver;

  Z3Context &Context;

  Z3_sort Sort;

public:
  /// Default constructor, mainly used by make_shared
  Z3Sort(Z3Context &C, Z3_sort ZS) : Context(C), Sort(ZS) {
    Z3_inc_ref(Context.Context, reinterpret_cast<Z3_ast>(Sort));
  }

  /// Override implicit copy constructor for correct reference counting.
  Z3Sort(const Z3Sort &Other) : Context(Other.Context), Sort(Other.Sort) {
    Z3_inc_ref(Context.Context, reinterpret_cast<Z3_ast>(Sort));
  }

  /// Override implicit copy assignment constructor for correct reference
  /// counting.
  Z3Sort &operator=(const Z3Sort &Other) {
    Z3_inc_ref(Context.Context, reinterpret_cast<Z3_ast>(Other.Sort));
    Z3_dec_ref(Context.Context, reinterpret_cast<Z3_ast>(Sort));
    Sort = Other.Sort;
    return *this;
  }

  Z3Sort(Z3Sort &&Other) = delete;
  Z3Sort &operator=(Z3Sort &&Other) = delete;

  ~Z3Sort() {
    if (Sort)
      Z3_dec_ref(Context.Context, reinterpret_cast<Z3_ast>(Sort));
  }

  bool isBitvectorSortImpl() const override {
    return (Z3_get_sort_kind(Context.Context, Sort) == Z3_BV_SORT);
  }

  bool isBooleanSortImpl() const override {
    return (Z3_get_sort_kind(Context.Context, Sort) == Z3_BOOL_SORT);
  }

  unsigned getBitvectorSortSizeImpl() const override {
    return Z3_get_bv_sort_size(Context.Context, Sort);
  }

  bool equal_to(camada::SMTSort const &Other) const override {
    return Z3_is_eq_sort(Context.Context, Sort,
                         static_cast<const Z3Sort &>(Other).Sort);
  }

  void dump() const override {
    fmt::print(stderr, Z3_sort_to_string(Context.Context, Sort));
  }
}; // end class Z3Sort

static const Z3Sort &toZ3Sort(const camada::SMTSort &S) {
  return static_cast<const Z3Sort &>(S);
}

class Z3Expr : public camada::SMTExpr {
  friend class Z3Solver;

  Z3Context &Context;

  Z3_ast AST;

public:
  Z3Expr(Z3Context &C, Z3_ast ZA) : camada::SMTExpr(), Context(C), AST(ZA) {
    Z3_inc_ref(Context.Context, AST);
  }

  /// Override implicit copy constructor for correct reference counting.
  Z3Expr(const Z3Expr &Copy)
      : camada::SMTExpr(), Context(Copy.Context), AST(Copy.AST) {
    Z3_inc_ref(Context.Context, AST);
  }

  /// Override implicit copy assignment constructor for correct reference
  /// counting.
  Z3Expr &operator=(const Z3Expr &Other) {
    Z3_inc_ref(Context.Context, Other.AST);
    Z3_dec_ref(Context.Context, AST);
    AST = Other.AST;
    return *this;
  }

  Z3Expr(Z3Expr &&Other) = delete;
  Z3Expr &operator=(Z3Expr &&Other) = delete;

  ~Z3Expr() {
    if (AST)
      Z3_dec_ref(Context.Context, AST);
  }

  /// Comparison of AST equality, not model equivalence.
  bool equal_to(camada::SMTExpr const &Other) const override {
    assert(Z3_is_eq_sort(Context.Context, Z3_get_sort(Context.Context, AST),
                         Z3_get_sort(Context.Context,
                                     static_cast<const Z3Expr &>(Other).AST)) &&
           "AST's must have the same sort");
    return Z3_is_eq_ast(Context.Context, AST,
                        static_cast<const Z3Expr &>(Other).AST);
  }

  void dump() const override {
    fmt::print(stderr, Z3_ast_to_string(Context.Context, AST));
  }
}; // end class Z3Expr

static const Z3Expr &toZ3Expr(const camada::SMTExpr &E) {
  return static_cast<const Z3Expr &>(E);
}

class Z3Model {
  friend class Z3Solver;

  Z3Context &Context;

  Z3_model Model;

public:
  Z3Model(Z3Context &C, Z3_model ZM) : Context(C), Model(ZM) {
    Z3_model_inc_ref(Context.Context, Model);
  }

  Z3Model(const Z3Model &Other) = delete;
  Z3Model(Z3Model &&Other) = delete;
  Z3Model &operator=(Z3Model &Other) = delete;
  Z3Model &operator=(Z3Model &&Other) = delete;

  ~Z3Model() {
    if (Model)
      Z3_model_dec_ref(Context.Context, Model);
  }

  void dump() const {
    fmt::print(stderr, Z3_model_to_string(Context.Context, Model));
  }
}; // end class Z3Model

class Z3Solver : public camada::SMTSolver {
  friend class Z3ConstraintManager;

  Z3Context Context;

  Z3_solver Solver;

public:
  Z3Solver() : Solver(Z3_mk_simple_solver(Context.Context)) {
    Z3_solver_inc_ref(Context.Context, Solver);
  }

  Z3Solver(const Z3Solver &Other) = delete;
  Z3Solver(Z3Solver &&Other) = delete;
  Z3Solver &operator=(Z3Solver &Other) = delete;
  Z3Solver &operator=(Z3Solver &&Other) = delete;

  ~Z3Solver() {
    if (Solver)
      Z3_solver_dec_ref(Context.Context, Solver);
  }

  void addConstraint(const camada::SMTExprRef &Exp) const override {
    Z3_solver_assert(Context.Context, Solver, toZ3Expr(*Exp).AST);
  }

  camada::SMTSortRef newSortRef(const camada::SMTSort &Sort) const override {
    return std::make_shared<Z3Sort>(toZ3Sort(Sort));
  }

  // Given an camada::SMTExpr, adds/retrives it from the cache and returns
  // an camada::SMTExprRef to the camada::SMTExpr in the cache
  camada::SMTExprRef newExprRef(const camada::SMTExpr &Exp) const override {
    return std::make_shared<Z3Expr>(toZ3Expr(Exp));
  }

  camada::SMTSortRef getBoolSort() override {
    return newSortRef(Z3Sort(Context, Z3_mk_bool_sort(Context.Context)));
  }

  camada::SMTSortRef getBitvectorSort(unsigned BitWidth) override {
    return newSortRef(
        Z3Sort(Context, Z3_mk_bv_sort(Context.Context, BitWidth)));
  }

  camada::SMTSortRef getSort(const camada::SMTExprRef &Exp) override {
    return newSortRef(
        Z3Sort(Context, Z3_get_sort(Context.Context, toZ3Expr(*Exp).AST)));
  }

  camada::SMTExprRef mkBVNeg(const camada::SMTExprRef &Exp) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvneg(Context.Context, toZ3Expr(*Exp).AST)));
  }

  camada::SMTExprRef mkBVNot(const camada::SMTExprRef &Exp) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvnot(Context.Context, toZ3Expr(*Exp).AST)));
  }

  camada::SMTExprRef mkNot(const camada::SMTExprRef &Exp) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_not(Context.Context, toZ3Expr(*Exp).AST)));
  }

  camada::SMTExprRef mkBVAdd(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvadd(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVSub(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvsub(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVMul(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvmul(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVSRem(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvsrem(Context.Context, toZ3Expr(*LHS).AST,
                                     toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVURem(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvurem(Context.Context, toZ3Expr(*LHS).AST,
                                     toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVSDiv(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvsdiv(Context.Context, toZ3Expr(*LHS).AST,
                                     toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVUDiv(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvudiv(Context.Context, toZ3Expr(*LHS).AST,
                                     toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVShl(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvshl(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVAshr(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvashr(Context.Context, toZ3Expr(*LHS).AST,
                                     toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVLshr(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvlshr(Context.Context, toZ3Expr(*LHS).AST,
                                     toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVXor(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvxor(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVOr(const camada::SMTExprRef &LHS,
                            const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvor(Context.Context, toZ3Expr(*LHS).AST,
                                   toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVAnd(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvand(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVUlt(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvult(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVSlt(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvslt(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVUgt(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvugt(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVSgt(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvsgt(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVUle(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvule(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVSle(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvsle(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVUge(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvuge(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVSge(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_bvsge(Context.Context, toZ3Expr(*LHS).AST,
                                    toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkAnd(const camada::SMTExprRef &LHS,
                           const camada::SMTExprRef &RHS) override {
    Z3_ast Args[2] = {toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST};
    return newExprRef(Z3Expr(Context, Z3_mk_and(Context.Context, 2, Args)));
  }

  camada::SMTExprRef mkOr(const camada::SMTExprRef &LHS,
                          const camada::SMTExprRef &RHS) override {
    Z3_ast Args[2] = {toZ3Expr(*LHS).AST, toZ3Expr(*RHS).AST};
    return newExprRef(Z3Expr(Context, Z3_mk_or(Context.Context, 2, Args)));
  }

  camada::SMTExprRef mkEqual(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_eq(Context.Context, toZ3Expr(*LHS).AST,
                                 toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkIte(const camada::SMTExprRef &Cond,
                           const camada::SMTExprRef &T,
                           const camada::SMTExprRef &F) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_ite(Context.Context, toZ3Expr(*Cond).AST,
                                  toZ3Expr(*T).AST, toZ3Expr(*F).AST)));
  }

  camada::SMTExprRef mkBVSignExt(unsigned i,
                                 const camada::SMTExprRef &Exp) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_sign_ext(Context.Context, i, toZ3Expr(*Exp).AST)));
  }

  camada::SMTExprRef mkBVZeroExt(unsigned i,
                                 const camada::SMTExprRef &Exp) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_zero_ext(Context.Context, i, toZ3Expr(*Exp).AST)));
  }

  camada::SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                                 const camada::SMTExprRef &Exp) override {
    return newExprRef(Z3Expr(Context, Z3_mk_extract(Context.Context, High, Low,
                                                    toZ3Expr(*Exp).AST)));
  }

  /// Creates a predicate that checks for overflow in a bitvector addition
  /// operation
  camada::SMTExprRef mkBVAddNoOverflow(const camada::SMTExprRef &LHS,
                                       const camada::SMTExprRef &RHS,
                                       bool isSigned) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_bvadd_no_overflow(Context.Context, toZ3Expr(*LHS).AST,
                                         toZ3Expr(*RHS).AST, isSigned)));
  }

  /// Creates a predicate that checks for underflow in a signed bitvector
  /// addition operation
  camada::SMTExprRef
  mkBVAddNoUnderflow(const camada::SMTExprRef &LHS,
                     const camada::SMTExprRef &RHS) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_bvadd_no_underflow(Context.Context, toZ3Expr(*LHS).AST,
                                          toZ3Expr(*RHS).AST)));
  }

  /// Creates a predicate that checks for overflow in a signed bitvector
  /// subtraction operation
  camada::SMTExprRef mkBVSubNoOverflow(const camada::SMTExprRef &LHS,
                                       const camada::SMTExprRef &RHS) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_bvsub_no_overflow(Context.Context, toZ3Expr(*LHS).AST,
                                         toZ3Expr(*RHS).AST)));
  }

  /// Creates a predicate that checks for underflow in a bitvector subtraction
  /// operation
  camada::SMTExprRef mkBVSubNoUnderflow(const camada::SMTExprRef &LHS,
                                        const camada::SMTExprRef &RHS,
                                        bool isSigned) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_bvsub_no_underflow(Context.Context, toZ3Expr(*LHS).AST,
                                          toZ3Expr(*RHS).AST, isSigned)));
  }

  /// Creates a predicate that checks for overflow in a signed bitvector
  /// division/modulus operation
  camada::SMTExprRef
  mkBVSDivNoOverflow(const camada::SMTExprRef &LHS,
                     const camada::SMTExprRef &RHS) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_bvsdiv_no_overflow(Context.Context, toZ3Expr(*LHS).AST,
                                          toZ3Expr(*RHS).AST)));
  }

  /// Creates a predicate that checks for overflow in a bitvector negation
  /// operation
  camada::SMTExprRef mkBVNegNoOverflow(const camada::SMTExprRef &Exp) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_bvneg_no_overflow(Context.Context, toZ3Expr(*Exp).AST)));
  }

  /// Creates a predicate that checks for overflow in a bitvector multiplication
  /// operation
  camada::SMTExprRef mkBVMulNoOverflow(const camada::SMTExprRef &LHS,
                                       const camada::SMTExprRef &RHS,
                                       bool isSigned) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_bvmul_no_overflow(Context.Context, toZ3Expr(*LHS).AST,
                                         toZ3Expr(*RHS).AST, isSigned)));
  }

  /// Creates a predicate that checks for underflow in a signed bitvector
  /// multiplication operation
  camada::SMTExprRef
  mkBVMulNoUnderflow(const camada::SMTExprRef &LHS,
                     const camada::SMTExprRef &RHS) override {
    return newExprRef(Z3Expr(
        Context, Z3_mk_bvmul_no_underflow(Context.Context, toZ3Expr(*LHS).AST,
                                          toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBVConcat(const camada::SMTExprRef &LHS,
                                const camada::SMTExprRef &RHS) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_concat(Context.Context, toZ3Expr(*LHS).AST,
                                     toZ3Expr(*RHS).AST)));
  }

  camada::SMTExprRef mkBoolean(const bool b) override {
    return newExprRef(Z3Expr(Context, b ? Z3_mk_true(Context.Context)
                                        : Z3_mk_false(Context.Context)));
  }

  camada::SMTExprRef mkBitvector(const boost::multiprecision::cpp_int Int,
                                 unsigned BitWidth) override {
    const camada::SMTSortRef Sort = getBitvectorSort(BitWidth);
    return newExprRef(Z3Expr(
        Context, Z3_mk_numeral(Context.Context,
                               boost::lexical_cast<std::string>(Int).c_str(),
                               toZ3Sort(*Sort).Sort)));
  }

  camada::SMTExprRef mkSymbol(const char *Name,
                              camada::SMTSortRef Sort) override {
    return newExprRef(
        Z3Expr(Context, Z3_mk_const(Context.Context,
                                    Z3_mk_string_symbol(Context.Context, Name),
                                    toZ3Sort(*Sort).Sort)));
  }

  const boost::multiprecision::cpp_int
  getBitvector(const camada::SMTExprRef &Exp, bool isUnsigned) override {
    return boost::multiprecision::cpp_int(
        Z3_get_numeral_string(Context.Context, toZ3Expr(*Exp).AST));
  }

  bool getBoolean(const camada::SMTExprRef &Exp) override {
    return Z3_get_bool_value(Context.Context, toZ3Expr(*Exp).AST) == Z3_L_TRUE;
  }

  camada::checkResult check() const override {
    Z3_lbool res = Z3_solver_check(Context.Context, Solver);
    if (res == Z3_L_TRUE)
      return camada::checkResult::SAT;

    if (res == Z3_L_FALSE)
      return camada::checkResult::UNSAT;

    return camada::checkResult::UNKNOWN;
  }

  void push() override { return Z3_solver_push(Context.Context, Solver); }

  void pop(unsigned NumStates = 1) override {
    assert(Z3_solver_get_num_scopes(Context.Context, Solver) >= NumStates);
    return Z3_solver_pop(Context.Context, Solver, NumStates);
  }

  /// Reset the solver and remove all constraints.
  void reset() override { Z3_solver_reset(Context.Context, Solver); }

  void dump() const override {
    fmt::print(stderr, Z3_solver_to_string(Context.Context, Solver));
  }

  void dumpModel() const override {
    fmt::print(stderr, Z3_model_to_string(
                           Context.Context,
                           Z3_solver_get_model(Context.Context, Solver)));
  }
}; // end class Z3Solver

} // end anonymous namespace

#endif

camada::SMTSolverRef camada::createZ3Solver() {
#if SOLVER_Z3_ENABLED
  return std::make_shared<Z3Solver>();
#else
  fmt::print(stderr, "Camada was not compiled with Z3 support, rebuild with "
                     "-DCAMADA_ENABLE_SOLVER_Z3=ON");
  return nullptr;
#endif
}
