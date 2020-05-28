#ifndef CAMADA_H_
#define CAMADA_H_

#include <cassert>
#include <memory>
#include <string>

namespace camada {

enum class checkResult { SAT, UNSAT, UNKNOWN };

/// Generic base class for SMT sorts
class SMTSort {
public:
  SMTSort() = default;
  virtual ~SMTSort() = default;

  /// Returns true if the sort is a bitvector, calls isBitvectorSortImpl().
  virtual bool isBitvectorSort() const { return isBitvectorSortImpl(); }

  /// Returns true if the sort is a boolean, calls isBooleanSortImpl().
  virtual bool isBooleanSort() const { return isBooleanSortImpl(); }

  /// Returns the bitvector size, fails if the sort is not a bitvector
  /// Calls getBitvectorSortSizeImpl().
  virtual unsigned getBitvectorSortSize() const {
    assert(isBitvectorSort() && "Not a bitvector sort!");
    unsigned Size = getBitvectorSortSizeImpl();
    assert(Size && "Size is zero!");
    return Size;
  };

  friend bool operator==(SMTSort const &LHS, SMTSort const &RHS) {
    return LHS.equal_to(RHS);
  }

  virtual void dump() const;

protected:
  /// Query the SMT solver and returns true if two sorts are equal (same kind
  /// and bit width). This does not check if the two sorts are the same objects.
  virtual bool equal_to(SMTSort const &other) const = 0;

  /// Query the SMT solver and checks if a sort is bitvector.
  virtual bool isBitvectorSortImpl() const = 0;

  /// Query the SMT solver and checks if a sort is boolean.
  virtual bool isBooleanSortImpl() const = 0;

  /// Query the SMT solver and returns the sort bit width.
  virtual unsigned getBitvectorSortSizeImpl() const = 0;
};

/// Shared pointer for SMTSorts, used by SMTSolver API.
using SMTSortRef = std::shared_ptr<SMTSort>;

/// Generic base class for SMT exprs
class SMTExpr {
public:
  SMTExpr() = default;
  virtual ~SMTExpr() = default;

  friend bool operator==(SMTExpr const &LHS, SMTExpr const &RHS) {
    return LHS.equal_to(RHS);
  }

  virtual void dump() const;

protected:
  /// Query the SMT solver and returns true if two sorts are equal (same kind
  /// and bit width). This does not check if the two sorts are the same objects.
  virtual bool equal_to(SMTExpr const &other) const = 0;
};

/// Shared pointer for SMTExprs, used by SMTSolver API.
using SMTExprRef = std::shared_ptr<SMTExpr>;

/// Generic base class for SMT Solvers
///
/// This class is responsible for wrapping all sorts and expression generation,
/// through the mk* methods. It also provides methods to create SMT expressions
/// straight from clang's AST, through the from* methods.
class SMTSolver {
public:
  SMTSolver() = default;
  virtual ~SMTSolver() = default;

  /// Wrapper to create new SMTSort
  virtual SMTSortRef newSortRef(const SMTSort &Sort) const = 0;

  /// Wrapper to create new SMTExpr
  virtual SMTExprRef newExprRef(const SMTExpr &Exp) const = 0;

  /// Returns a boolean sort.
  virtual SMTSortRef getBoolSort() = 0;

  /// Returns an appropriate bitvector sort for the given bitwidth.
  virtual SMTSortRef getBitvectorSort(const unsigned BitWidth) = 0;

  /// Returns an appropriate sort for the given AST.
  virtual SMTSortRef getSort(const SMTExprRef &AST) = 0;

  /// Given a constraint, adds it to the solver
  virtual void addConstraint(const SMTExprRef &Exp) const = 0;

  /// Creates a bitvector addition operation
  virtual SMTExprRef mkBVAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector subtraction operation
  virtual SMTExprRef mkBVSub(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector multiplication operation
  virtual SMTExprRef mkBVMul(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed modulus operation
  virtual SMTExprRef mkBVSRem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned modulus operation
  virtual SMTExprRef mkBVURem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed division operation
  virtual SMTExprRef mkBVSDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned division operation
  virtual SMTExprRef mkBVUDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector logical shift left operation
  virtual SMTExprRef mkBVShl(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector arithmetic shift right operation
  virtual SMTExprRef mkBVAshr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector logical shift right operation
  virtual SMTExprRef mkBVLshr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector negation operation
  virtual SMTExprRef mkBVNeg(const SMTExprRef &Exp) = 0;

  /// Creates a bitvector not operation
  virtual SMTExprRef mkBVNot(const SMTExprRef &Exp) = 0;

  /// Creates a bitvector xor operation
  virtual SMTExprRef mkBVXor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector or operation
  virtual SMTExprRef mkBVOr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector and operation
  virtual SMTExprRef mkBVAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned less-than operation
  virtual SMTExprRef mkBVUlt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed less-than operation
  virtual SMTExprRef mkBVSlt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned greater-than operation
  virtual SMTExprRef mkBVUgt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed greater-than operation
  virtual SMTExprRef mkBVSgt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned less-equal-than operation
  virtual SMTExprRef mkBVUle(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed less-equal-than operation
  virtual SMTExprRef mkBVSle(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector unsigned greater-equal-than operation
  virtual SMTExprRef mkBVUge(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector signed greater-equal-than operation
  virtual SMTExprRef mkBVSge(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean not operation
  virtual SMTExprRef mkNot(const SMTExprRef &Exp) = 0;

  /// Creates a boolean equality operation
  virtual SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean and operation
  virtual SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean or operation
  virtual SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean ite operation
  virtual SMTExprRef mkIte(const SMTExprRef &Cond, const SMTExprRef &T,
                           const SMTExprRef &F) = 0;

  /// Creates a bitvector sign extension operation
  virtual SMTExprRef mkBVSignExt(unsigned i, const SMTExprRef &Exp) = 0;

  /// Creates a bitvector zero extension operation
  virtual SMTExprRef mkBVZeroExt(unsigned i, const SMTExprRef &Exp) = 0;

  /// Creates a bitvector extract operation
  virtual SMTExprRef mkBVExtract(unsigned High, unsigned Low,
                                 const SMTExprRef &Exp) = 0;

  /// Creates a bitvector concat operation
  virtual SMTExprRef mkBVConcat(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates a predicate that checks for overflow in a bitvector addition
  /// operation
  virtual SMTExprRef mkBVAddNoOverflow(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS,
                                       bool isSigned) = 0;

  /// Creates a predicate that checks for underflow in a signed bitvector
  /// addition operation
  virtual SMTExprRef mkBVAddNoUnderflow(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) = 0;

  /// Creates a predicate that checks for overflow in a signed bitvector
  /// subtraction operation
  virtual SMTExprRef mkBVSubNoOverflow(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) = 0;

  /// Creates a predicate that checks for underflow in a bitvector subtraction
  /// operation
  virtual SMTExprRef mkBVSubNoUnderflow(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS,
                                        bool isSigned) = 0;

  /// Creates a predicate that checks for overflow in a signed bitvector
  /// division/modulus operation
  virtual SMTExprRef mkBVSDivNoOverflow(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) = 0;

  /// Creates a predicate that checks for overflow in a bitvector negation
  /// operation
  virtual SMTExprRef mkBVNegNoOverflow(const SMTExprRef &Exp) = 0;

  /// Creates a predicate that checks for overflow in a bitvector
  /// multiplication operation
  virtual SMTExprRef mkBVMulNoOverflow(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS,
                                       bool isSigned) = 0;

  /// Creates a predicate that checks for underflow in a signed bitvector
  /// multiplication operation
  virtual SMTExprRef mkBVMulNoUnderflow(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) = 0;

  /// Creates a new symbol, given a name and a sort
  virtual SMTExprRef mkSymbol(const char *Name, SMTSortRef Sort) = 0;

  /// If the a model is available, returns the value of a given bitvector
  /// symbol
  virtual const std::string getBitvector(const SMTExprRef &Exp,
                                         bool isUnsigned) = 0;

  /// If the a model is available, returns the value of a given boolean symbol
  virtual bool getBoolean(const SMTExprRef &Exp) = 0;

  /// Constructs an SMTExprRef from a boolean.
  virtual SMTExprRef mkBoolean(const bool b) = 0;

  /// Constructs an SMTExprRef from an APSInt and its bit width
  virtual SMTExprRef mkBitvector(const std::string Int, unsigned BitWidth) = 0;

  /// Check if the constraints are satisfiable
  virtual checkResult check() const = 0;

  /// Push the current solver state
  virtual void push() = 0;

  /// Pop the previous solver state
  virtual void pop(unsigned NumStates = 1) = 0;

  /// Reset the solver and remove all constraints.
  virtual void reset() = 0;

  /// Dump formula
  virtual void dump() const;

  /// Dump Model
  virtual void dumpModel() const;
};

/// Shared pointer for SMTSolvers.
using SMTSolverRef = std::shared_ptr<SMTSolver>;

/// Return camada version
const std::string getCamadaVersion();

/// Convenience method to create a Z3Solver object
SMTSolverRef createZ3Solver();

} // namespace camada

#endif
