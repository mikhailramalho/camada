#ifndef Z3SOLVER_H_
#define Z3SOLVER_H_

#include "camada.h"

#ifdef SOLVER_Z3_ENABLED

#include <z3++.h>

namespace camada {

using Z3ContextRef = std::shared_ptr<z3::context>;

/// Wrapper for Z3 Sort
class Z3Sort : public SMTSort {
public:
  Z3ContextRef Context;

  Z3_sort Sort;

  /// Default constructor, mainly used by make_shared
  Z3Sort(Z3ContextRef C, Z3_sort ZS);

  /// Override implicit copy constructor for correct reference counting.
  Z3Sort(const Z3Sort &Other);

  /// Override implicit copy assignment constructor for correct reference
  /// counting.
  Z3Sort &operator=(const Z3Sort &Other);

  Z3Sort(Z3Sort &&Other) = delete;
  Z3Sort &operator=(Z3Sort &&Other) = delete;

  virtual ~Z3Sort();

  bool isBitvectorSortImpl() const override;

  bool isBooleanSortImpl() const override;

  unsigned getBitvectorSortSizeImpl() const override;

  bool equal_to(SMTSort const &Other) const override;

  void dump() const override;
}; // end class Z3Sort

static const Z3Sort &toZ3Sort(const SMTSort &S) {
  return static_cast<const Z3Sort &>(S);
}

class Z3Expr : public SMTExpr {
public:
  Z3ContextRef Context;

  Z3_ast AST;

  Z3Expr(Z3ContextRef C, Z3_ast ZA);

  /// Override implicit copy constructor for correct reference counting.
  Z3Expr(const Z3Expr &Copy);

  /// Override implicit copy assignment constructor for correct reference
  /// counting.
  Z3Expr &operator=(const Z3Expr &Other);

  Z3Expr(Z3Expr &&Other) = delete;
  Z3Expr &operator=(Z3Expr &&Other) = delete;

  virtual ~Z3Expr();

  /// Comparison of AST equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class Z3Expr

static const Z3Expr &toZ3Expr(const SMTExpr &E) {
  return static_cast<const Z3Expr &>(E);
}

class Z3Model {
public:
  Z3ContextRef Context;

  Z3_model Model;

  Z3Model(Z3ContextRef C, Z3_model ZM);

  Z3Model(const Z3Model &Other) = delete;
  Z3Model(Z3Model &&Other) = delete;
  Z3Model &operator=(Z3Model &Other) = delete;
  Z3Model &operator=(Z3Model &&Other) = delete;

  virtual ~Z3Model();

  void dump() const;
}; // end class Z3Model

class Z3Tactic {
public:
  Z3ContextRef Context;

  Z3_tactic Tactic;

  Z3Tactic(Z3ContextRef C, Z3_tactic T);

  Z3Tactic(const Z3Tactic &Other) = delete;
  Z3Tactic(Z3Tactic &&Other) = delete;
  Z3Tactic &operator=(Z3Tactic &Other) = delete;
  Z3Tactic &operator=(Z3Tactic &&Other) = delete;

  virtual ~Z3Tactic();

}; // end class Z3Tactic

class Z3Params {
public:
  Z3ContextRef Context;

  Z3_params Params;

  Z3Params(Z3ContextRef C, Z3_params P);

  Z3Params(const Z3Params &Other) = delete;
  Z3Params(Z3Params &&Other) = delete;
  Z3Params &operator=(Z3Params &Other) = delete;
  Z3Params &operator=(Z3Params &&Other) = delete;

  virtual ~Z3Params();

}; // end class Z3Params

class Z3Solver : public camada::SMTSolver {
public:
  Z3ContextRef Context;

  Z3_solver Solver;

  Z3Solver() = default;
  explicit Z3Solver(Z3ContextRef C);

  Z3Solver(const Z3Solver &Other) = delete;
  Z3Solver(Z3Solver &&Other) = delete;
  Z3Solver &operator=(Z3Solver &Other) = delete;
  Z3Solver &operator=(Z3Solver &&Other) = delete;

  ~Z3Solver();

  void addConstraint(const camada::SMTExprRef &Exp) const override;

  camada::SMTSortRef newSortRef(const camada::SMTSort &Sort) const override;

  camada::SMTExprRef newExprRef(const camada::SMTExpr &Exp) const override;

  camada::SMTSortRef getBoolSort() override;

  camada::SMTSortRef getBitvectorSort(unsigned BitWidth) override;

  camada::SMTSortRef getSort(const camada::SMTExprRef &Exp) override;

  camada::SMTExprRef mkBVNeg(const camada::SMTExprRef &Exp) override;

  camada::SMTExprRef mkBVNot(const camada::SMTExprRef &Exp) override;

  camada::SMTExprRef mkNot(const camada::SMTExprRef &Exp) override;

  camada::SMTExprRef mkBVAdd(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVSub(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVMul(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVSRem(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVURem(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVSDiv(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVUDiv(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVShl(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVAshr(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVLshr(const camada::SMTExprRef &LHS,
                              const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVXor(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVOr(const camada::SMTExprRef &LHS,
                            const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVAnd(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVUlt(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVSlt(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVUgt(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVSgt(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVUle(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVSle(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVUge(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBVSge(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkAnd(const camada::SMTExprRef &LHS,
                           const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkOr(const camada::SMTExprRef &LHS,
                          const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkEqual(const camada::SMTExprRef &LHS,
                             const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkIte(const camada::SMTExprRef &Cond,
                           const camada::SMTExprRef &T,
                           const camada::SMTExprRef &F) override;

  camada::SMTExprRef mkBVSignExt(unsigned i,
                                 const camada::SMTExprRef &Exp) override;

  camada::SMTExprRef mkBVZeroExt(unsigned i,
                                 const camada::SMTExprRef &Exp) override;

  camada::SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                                 const camada::SMTExprRef &Exp) override;

  camada::SMTExprRef mkBVConcat(const camada::SMTExprRef &LHS,
                                const camada::SMTExprRef &RHS) override;

  camada::SMTExprRef mkBoolean(const bool b) override;

  camada::SMTExprRef mkBitvector(const std::string Int,
                                 unsigned BitWidth) override;

  camada::SMTExprRef mkSymbol(const char *Name,
                              camada::SMTSortRef Sort) override;

  const std::string getBitvector(const camada::SMTExprRef &Exp) override;

  bool getBoolean(const camada::SMTExprRef &Exp) override;

  /// Given an expression, extract the value of this operand in the model.
  bool getInterpretation(const camada::SMTExprRef &Exp,
                         std::string &Inter) override;

  camada::checkResult check() const override;

  void push() override;

  void pop(unsigned NumStates = 1) override;

  /// Reset the solver and remove all constraints.
  void reset() override;

  void dump() const override;

  void dumpModel() const override;
}; // end class Z3Solver

} // namespace camada

#endif

#endif
