#ifndef CAMADA_H_
#define CAMADA_H_

#include <memory>
#include <string>

namespace camada {

/// Return camada version
std::string getCamadaVersion();

/// Abort program if Cond is false and prints Msg to stderr
void abortCondWithMessage(bool Cond, const std::string &Msg);

/// Abort program and prints Msg to stderr
[[noreturn]] void abortWithMessage(const std::string &Msg);

enum class checkResult { SAT, UNSAT, UNKNOWN };

enum class RoundingMode {
  ROUND_TO_EVEN,
  ROUND_TO_AWAY,
  ROUND_TO_PLUS_INF,
  ROUND_TO_MINUS_INF,
  ROUND_TO_ZERO
};

/// Generic base class for SMT sorts
class SMTSort {
public:
  SMTSort() = default;
  virtual ~SMTSort() = default;

  /// Returns true if the sort is a bitvector, calls isBitvectorSortImpl().
  virtual bool isBitvectorSort() const { return isBitvectorSortImpl(); }

  /// Returns true if the sort is a boolean, calls isBooleanSortImpl().
  virtual bool isBooleanSort() const { return isBooleanSortImpl(); }

  /// Returns true if the sort is a floating-point, calls isFloatSortImpl().
  virtual bool isFloatSort() const { return isFloatSortImpl(); }

  /// Returns true if the sort is a rounding mode, calls
  /// isRoundingModeSortImpl().
  virtual bool isRoundingModeSort() const { return isRoundingModeSortImpl(); }

  /// Returns the bitvector size, fails if the sort is not a bitvector
  /// Calls getBitvectorSortSizeImpl().
  virtual unsigned getBitvectorSortSize() const {
    abortCondWithMessage(isBitvectorSort(), "Not a bitvector sort!");
    unsigned size = getBitvectorSortSizeImpl();
    abortCondWithMessage(size, "Bitvector size is zero!");
    return size;
  };

  /// Returns the floating-point size, fails if the sort is not a floating-point
  /// Calls getFloatSortSizeImpl().
  virtual unsigned getFloatSortSize() const {
    abortCondWithMessage(isFloatSort(), "Not a floating-point sort!");
    unsigned size = getFloatSortSizeImpl();
    abortCondWithMessage(size, "Floating-point size is zero!");
    return size;
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

  /// Query the SMT solver and checks if a sort is floating-point.
  virtual bool isFloatSortImpl() const = 0;

  /// Query the SMT solver and checks if a sort is rounding mode.
  virtual bool isRoundingModeSortImpl() const = 0;

  /// Query the SMT solver and returns the sort bit width.
  virtual unsigned getBitvectorSortSizeImpl() const = 0;

  /// Query the SMT solver and returns the sort bit width.
  virtual unsigned getFloatSortSizeImpl() const = 0;
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

  /// Returns an appropriate bitvector sort for the given bitwidth.
  virtual SMTSortRef getRoundingModeSort() = 0;

  virtual SMTSortRef getFloatSort(const unsigned ExpWidth,
                                  const unsigned SigWidth) = 0;

  /// Convenience method to create a 32 bits long a floating-point sort.
  SMTSortRef getFloat32Sort() { return getFloatSort(8, 24); }

  /// Convenience method to create a 64 bits long a floating-point sort.
  SMTSortRef getFloat64Sort() { return getFloatSort(11, 53); }

  /// Returns an appropriate sort for the given AST.
  virtual SMTSortRef getSort(const SMTExprRef &AST) = 0;

  /// Given a constraint, adds it to the solver
  virtual void addConstraint(const SMTExprRef &Exp) = 0;

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

  /// Creates a floating-point negation operation
  virtual SMTExprRef mkFPNeg(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isInfinite operation
  virtual SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isNaN operation
  virtual SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isNormal operation
  virtual SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isZero operation
  virtual SMTExprRef mkFPIsZero(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point multiplication operation
  virtual SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) = 0;

  /// Creates a floating-point division operation
  virtual SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) = 0;

  /// Creates a floating-point remainder operation
  virtual SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point addition operation
  virtual SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) = 0;

  /// Creates a floating-point subtraction operation
  virtual SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const RoundingMode R) = 0;

  /// Creates a floating-point square root operation
  virtual SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const RoundingMode R) = 0;

  /// Creates a floating-point fused-multiply add operation: round((x * y) + z)
  virtual SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z, const RoundingMode R) = 0;

  /// Creates a floating-point less-than operation
  virtual SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point greater-than operation
  virtual SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point less-than-or-equal operation
  virtual SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point greater-than-or-equal operation
  virtual SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point equality operation
  virtual SMTExprRef mkFPEqual(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates a floating-point conversion from floatint-point to floating-point
  /// operation
  virtual SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const RoundingMode R) = 0;

  /// Creates a floating-point conversion from signed bitvector to
  /// floatint-point operation
  virtual SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) = 0;

  /// Creates a floating-point conversion from unsigned bitvector to
  /// floatint-point operation
  virtual SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const RoundingMode R) = 0;

  /// Creates a floating-point conversion from floatint-point to signed
  /// bitvector operation
  virtual SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floatint-point to unsigned
  /// bitvector operation
  virtual SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floatint-point to the closest
  /// integer, considering the rounding mode.
  virtual SMTExprRef mkFPtoIntegral(const SMTExprRef &From, RoundingMode R) = 0;

  /// If the a model is available, returns the value of a given boolean symbol
  virtual bool getBoolean(const SMTExprRef &Exp) = 0;

  /// If the a model is available, returns the value of a given bitvector
  /// symbol as a 64-bits int
  virtual int64_t getBitvector(const SMTExprRef &Exp) = 0;

  /// If the a model is available, returns the value of a given floating-point
  /// symbol as float
  virtual float getFloat(const SMTExprRef &Exp) = 0;

  /// If the a model is available, returns the value of a given floating-point
  /// symbol as double
  virtual double getDouble(const SMTExprRef &Exp) = 0;

  /// Given an expression, extract the value of this operand in the model.
  virtual bool getInterpretation(const SMTExprRef &Exp, int64_t &Int) = 0;

  /// Given an expression extract the value of this operand in the model.
  virtual bool getInterpretation(const SMTExprRef &Exp, float &Float) = 0;

  /// Given an expression extract the value of this operand in the model.
  virtual bool getInterpretation(const SMTExprRef &Exp, double &Double) = 0;

  /// Constructs an SMTExprRef from a boolean.
  virtual SMTExprRef mkBoolean(const bool b) = 0;

  /// Constructs an SMTExprRef from an integer and its bit width
  virtual SMTExprRef mkBitvector(const int64_t Int, unsigned BitWidth) = 0;

  /// Creates a new symbol, given a name and a sort
  virtual SMTExprRef mkSymbol(const char *Name, SMTSortRef Sort) = 0;

  /// Constructs an SMTExprRef from a float.
  virtual SMTExprRef mkFloat(const float Float) = 0;

  /// Constructs an SMTExprRef from a double.
  virtual SMTExprRef mkDouble(const double Double) = 0;

  /// Returns an appropriate floating-point rounding mode.
  virtual SMTExprRef mkRoundingMode(const RoundingMode R) = 0;

  /// Returns a NaN floating-point
  virtual SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) = 0;

  /// Convenience method to create 32 bits long NaN
  SMTExprRef mkNaN32(const bool Sgn) { return mkNaN(Sgn, 8, 24); }

  /// Convenience method to create 64 bits long NaN
  SMTExprRef mkNaN64(const bool Sgn) { return mkNaN(Sgn, 11, 53); }

  /// Returns a Inf floating-point
  virtual SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth) = 0;

  /// Convenience method to create 32 bits long Inf
  SMTExprRef mkInf32(const bool Sgn) { return mkInf(Sgn, 8, 24); }

  /// Convenience method to create 64 bits long Inf
  SMTExprRef mkInf64(const bool Sgn) { return mkInf(Sgn, 11, 53); }

  /// Check if the constraints are satisfiable
  virtual checkResult check() = 0;

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

/// Convenience method to create a Z3Solver object
SMTSolverRef createZ3Solver();

} // namespace camada

#endif
