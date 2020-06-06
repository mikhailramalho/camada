#ifndef BOOLECTORSOLVER_H_
#define BOOLECTORSOLVER_H_

#include "camada.h"

#include <unordered_map>

extern "C" {
#include <boolector/boolector.h>
}

namespace camada {

/// Wrapper for Boolector context
class BtorContext {
public:
  Btor *Context;

  BtorContext();
  virtual ~BtorContext();

  void createAndConfig();
  void reset();
}; // end class BtorContext

using BtorContextRef = std::shared_ptr<BtorContext>;

/// Wrapper for Boolector Sort
class BtorSort : public SMTSort {
public:
  BtorContextRef Context;

  BoolectorSort Sort;

  BtorSort(BtorContextRef C, const BoolectorSort &BS);
  virtual ~BtorSort() = default;

  bool isBitvectorSortImpl() const override;

  bool isBooleanSortImpl() const override;

  bool isFloatSortImpl() const override;

  bool isRoundingModeSortImpl() const override;

  unsigned getBitvectorSortSizeImpl() const override;

  unsigned getFloatSortSizeImpl() const override;

  bool equal_to(SMTSort const &Other) const override;
}; // end class BtorSort

static inline const BtorSort &toBtorSort(const SMTSort &S) {
  return dynamic_cast<const BtorSort &>(S);
}

class BtorExpr : public SMTExpr {
public:
  BtorContextRef Context;

  BoolectorNode *AST;

  BtorExpr(BtorContextRef C, BoolectorNode *BA);
  virtual ~BtorExpr() = default;

  /// Comparison of AST equality, not model equivalence.
  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
}; // end class BtorExpr

static inline const BtorExpr &toBtorExpr(const SMTExpr &E) {
  return dynamic_cast<const BtorExpr &>(E);
}

class BtorSolver : public camada::SMTSolver {
public:
  BtorContextRef Context;

  using SymbolTablet = std::unordered_map<std::string, SMTExprRef>;
  SymbolTablet SymbolTable;

  explicit BtorSolver();
  explicit BtorSolver(BtorContextRef C);
  virtual ~BtorSolver() = default;

  void addConstraint(const camada::SMTExprRef &Exp) override;

  camada::SMTSortRef newSortRef(const camada::SMTSort &Sort) const override;

  camada::SMTExprRef newExprRef(const camada::SMTExpr &Exp) const override;

  camada::SMTSortRef getBoolSort() override;

  camada::SMTSortRef getBitvectorSort(unsigned BitWidth) override;

  camada::SMTSortRef getRoundingModeSort() override;

  SMTSortRef getFloatSort(const unsigned ExpWidth,
                          const unsigned SigWidth) override;

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

  SMTExprRef mkFPNeg(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) override;

  SMTExprRef mkFPIsZero(const SMTExprRef &Exp) override;

  SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RoundingMode R) override;

  SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RoundingMode R) override;

  SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RoundingMode R) override;

  SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                     const RoundingMode R) override;

  SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const RoundingMode R) override;

  SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                     const SMTExprRef &Z, const RoundingMode R) override;

  SMTExprRef mkFPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) override;

  SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                      const RoundingMode R) override;

  SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RoundingMode R) override;

  SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                       const RoundingMode R) override;

  SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) override;

  SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) override;

  SMTExprRef mkFPtoIntegral(const SMTExprRef &From, RoundingMode R) override;

  bool getBoolean(const camada::SMTExprRef &Exp) override;

  int64_t getBitvector(const camada::SMTExprRef &Exp) override;

  float getFloat(const camada::SMTExprRef &Exp) override;

  double getDouble(const camada::SMTExprRef &Exp) override;

  bool getInterpretation(const camada::SMTExprRef &Exp, int64_t &Int) override;

  bool getInterpretation(const SMTExprRef &Exp, float &Float) override;

  bool getInterpretation(const SMTExprRef &Exp, double &Double) override;

  camada::SMTExprRef mkBoolean(const bool b) override;

  camada::SMTExprRef mkBitvector(const int64_t Int, unsigned BitWidth) override;

  camada::SMTExprRef mkSymbol(const char *Name,
                              camada::SMTSortRef Sort) override;

  SMTExprRef mkFloat(const float Float) override;

  SMTExprRef mkDouble(const double Double) override;

  SMTExprRef mkRoundingMode(const RoundingMode R) override;

  SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) override;

  SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                   const unsigned SigWidth) override;

  camada::checkResult check() override;

  void push() override;

  void pop(unsigned NumStates = 1) override;

  /// Reset the solver and remove all constraints.
  void reset() override;

  void dump() override;

  void dumpModel() override;
}; // end class BtorSolver

} // namespace camada

#endif
