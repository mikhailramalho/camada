/**************************************************************************
 *
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 *
 **************************************************************************/

#ifndef CAMADA_H_
#define CAMADA_H_

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "camadacommon.h"
#include "camadaexpr.h"
#include "camadasort.h"

namespace camada {

/// Selects how Camada represents floating-point values when constructing
/// FP/RM sorts and FP constants. The encoding is per-sort, not solver-
/// wide — a single solver instance can hold both Native and BV-encoded
/// FP values at the same time, and they interoperate through the
/// common-layer encoders.
///
/// - Native: use the backend's native floating-point sort (`Float32Sort`
///   in z3, `mkFloatingPoint` in cvc5, etc.). Requires native FP
///   support in the backend; fastest path on solvers that have it.
/// - BV: bit-blast every FP value into a fixed-width bit-vector and
///   emulate the IEEE-754 operations through Camada's common-layer
///   encoder. The only path available on backends without native FP
///   (STP, Yices-SMT2) and on SMT-LIB scripts intended for solvers that
///   reject native FP. Substantially slower than Native on backends
///   that have both.
///
/// The two encodings round-trip cleanly across all five FP arithmetic
/// ops, predicates, and conversions (the `fp_native_bv_predicate_parity`
/// regression pins this), but model values are reported in the encoded
/// representation — `getFP32` decodes BV back to `float`, `getBV`
/// returns the raw bits when the sort was Native.
enum class FPEncoding { Native, BV };

/// Selects how `mkArrayConst` lowers a constant array. Unlike `FPEncoding`
/// this is not a sort property: lazily and natively lowered constant arrays
/// share the same array sorts and interoperate freely (stores, selects, and
/// ites may mix them); the choice only affects how the "every element
/// equals InitValue" semantics are produced.
///
/// - Auto: native `((as const ...) v)` when the backend supports it, the
///   Camada lazy lowering otherwise. The right default for almost all uses.
/// - Native: force the backend operator; fails on backends without one.
/// - Lazy: force the Camada lowering — a fresh array symbol whose default
///   value is asserted on demand at each index the formula observes. Works
///   at any index width and is the entry point for initializers that have
///   no backend representation.
///
/// Lazily lowered arrays must stay observable by the lowering: storing one
/// inside another array, placing one in a native tuple, or passing one to
/// an uninterpreted function is rejected, and capturing one under a
/// quantifier binder is unsupported (defaults are instantiated as ground
/// constraints only, so a quantified body can observe uninstantiated
/// indexes).
enum class ConstArrayLowering { Auto, Native, Lazy };

/// Selects how Camada lowers `mkFPNeg` for backends whose native FP
/// implementation diverges from the IEEE-754 sign-bit-flip semantics
/// some users expect.
///
/// - FlipSignBit: always flip the IEEE-754 sign bit, including on NaN
///   inputs. Matches the behavior of CPU FP units and most language
///   runtimes. Backed by an explicit bit-blast on solvers whose native
///   `fp.neg` preserves the NaN payload — see PR #59 for the per-
///   backend status.
/// - PreserveNaNPayload: follow the SMT-LIB `fp.neg` definition, which
///   leaves NaN payloads (including the sign bit) unchanged. Cheaper to
///   emit on backends that natively implement this semantics.
enum class FPNegBehavior {
  FlipSignBit,
  PreserveNaNPayload,
};

/// Selects how `mkFXPRound` breaks ties. TR 18037 specifies that the
/// `roundfx` family rounds to nearest but leaves the halfway direction to
/// the implementation, and implementations differ, so the caller states
/// which one it is modelling rather than inheriting one library's choice.
///
/// - TowardPositive: a halfway value rounds up, so 0.5 rounds to 1 and
///   -0.5 rounds to 0. What LLVM libc does (it adds half an ulp and masks
///   off the low bits), and the only direction verified against an
///   executing implementation.
/// - AwayFromZero: a halfway value rounds away from zero, so 0.5 rounds
///   to 1 and -0.5 rounds to -1 — symmetric about zero, the convention
///   most C programmers expect from `round()`.
/// - ToEven: a halfway value rounds to whichever neighbour has a zero in
///   the last kept bit, the unbiased choice IEEE-754 uses by default.
///
/// All three saturate to the format's maximum when the rounding would
/// carry past it, which every implementation surveyed agrees on.
enum class FXPRoundTie {
  TowardPositive,
  AwayFromZero,
  ToEven,
};

/// Selects how the SMT-LIB backend lowers tuples on the wire.
///
/// - Native: emit `(declare-datatypes ...)` and rely on the downstream
///   solver to support SMT-LIB datatypes. Works against z3 and cvc5; not
///   accepted by bitwuzla, mathsat, yices-smt2.
/// - Camada: lower tuples in Camada to per-field BV/Bool symbols before
///   anything reaches the wire. The emitted script contains no
///   datatype declarations, so any standard SMT-LIB v2 solver can parse
///   it. Same encoding the non-native backends (bitwuzla/mathsat/stp/
///   yices) already use.
enum class TupleEncoding { Native, Camada };

/// Selects whether a solver context is created with unsat-assumption
/// production enabled. Producing the core is not free: backends whose SAT
/// engine must track assumption participation (bitwuzla, cvc5) pay a
/// solve-time cost on *every* check, and the setting is frozen at context
/// creation — so it is opt-in.
///
/// - Off (default): fast contexts. checkSatAssuming() works unchanged;
///   getUnsatAssumptions() reports UnsupportedOperation and
///   supports(SolverFeature::UnsatAssumptions) answers false.
/// - On: the backend tracks assumptions and getUnsatAssumptions() returns
///   real cores after an UNSAT checkSatAssuming().
///
/// Backends that answer cores without a creation-time option (Z3 enables
/// unsat_core per query, MathSAT and Yices track natively) ignore this
/// and always support core extraction.
enum class UnsatAssumptionsMode { Off, On };

/// Selects how arrays are encoded, on the backends that accept it.
///
/// - Native (default): the backend's theory of arrays, unchanged.
/// - Ackermann: arrays never reach the backend. Every select becomes a
///   fresh element variable tied to the array's other reads by congruence
///   axioms (`i = j => a[i] = a[j]`); stores and ites are lowered
///   structurally, and array equality uses a witness-index encoding. The
///   trade: array-theory work moves into the core solver as ground
///   constraints, quadratic in the number of reads per array.
///
/// Restrictions in Ackermann mode: quantifier-free formulas only (any
/// mkForall/mkExists call is rejected), no nested arrays, no array-sorted
/// UF arguments/returns, and model queries need bool/BV index sorts. The
/// mode forces the Camada tuple encoding — a native datatype cannot hold
/// an array member that has no backend representation.
enum class ArrayEncoding { Native, Ackermann };

enum class RM {
  ROUND_TO_EVEN = 0,
  ROUND_TO_AWAY = 1,
  ROUND_TO_PLUS_INF = 2,
  ROUND_TO_MINUS_INF = 3,
  ROUND_TO_ZERO = 4,
};

/// Return camada version
std::string getCamadaVersion();

enum class checkResult { SAT, UNSAT, UNKNOWN };

/// Capabilities a backend may or may not implement, queryable through
/// SMTSolver::supports() instead of discovering them through aborts or
/// UnsupportedOperation errors.
///
/// A true bit means the corresponding API surface is implemented for the
/// backend; individual calls can still fail for input-specific reasons
/// through their SMTResult. On the SMT-LIB pipeline backend the bits
/// describe what Camada emits — a particular child solver may still
/// reject a construct at runtime.
enum class SolverFeature {
  /// Int/Real sorts and arithmetic (mkIntSort, mkRealSort, mkArith*).
  IntRealArithmetic,
  /// Quantified formulas (mkForall, mkExists).
  Quantifiers,
  /// Uninterpreted functions (mkFunctionSort, mkApply).
  UninterpretedFunctions,
  /// FPEncoding::Native sorts and operations; FPEncoding::BV works on
  /// every backend regardless.
  NativeFloatingPoint,
  /// Backend-native tuple/datatype sorts; other backends route tuples
  /// through the Camada per-field lowering.
  NativeTuples,
  /// Backend-native `((as const ...) v)` constant arrays; other backends
  /// lower them lazily (see ConstArrayLowering).
  NativeConstantArrays,
  /// Unsat-assumption extraction after an UNSAT checkSatAssuming()
  /// (see issue #76). checkSatAssuming itself works on every backend
  /// through a push/assert/check/pop fallback.
  UnsatAssumptions,
  /// Per-check wall-clock limits via setTimeout() (see issue #77).
  Timeouts,
  /// Sparse array model extraction via getArrayValues() for arbitrary
  /// arrays (see issue #79). Lazily lowered constant arrays are answered
  /// by the common layer on every backend regardless.
  ArrayModels,
};

/// Coarse-grained error categories for operations that return `SMTResult<T>`.
///
/// These are intended for user-triggerable failures such as unsupported
/// features or model-query failures, not internal invariant violations.
enum class SMTErrorCode {
  None,
  BackendError,
  InvalidModelValue,
  UnsupportedOperation,
  /// The call sequence violated an API contract (e.g. querying unsat
  /// assumptions after the solver state changed), as opposed to a
  /// backend-originated failure.
  InvalidUsage,
};

/// Structured error payload carried by `SMTResult<T>` on failure.
struct SMTError {
  SMTError() = default;

  SMTError(SMTErrorCode TheCode, SMTBackendKind TheBackend,
           std::string TheMessage)
      : Code(TheCode), Backend(TheBackend), Message(std::move(TheMessage)) {}

  SMTErrorCode Code = SMTErrorCode::None;
  SMTBackendKind Backend{};
  std::string Message;
};

/// Lightweight C++17 result type used by fallible Camada APIs.
///
/// A result either contains a value of type `T` or an `SMTError`.
/// Successful results convert to `true`; failures convert to `false`.
///
/// Example:
/// ```cpp
/// auto value = solver->getBool(x);
/// if (!value) {
///   std::cerr << value.error().Message << "\n";
/// } else {
///   bool b = value.value();
/// }
/// ```
template <typename T> class SMTResult {
public:
  SMTResult(T Value) : Value_(std::move(Value)), HasValue_(true) {}
  SMTResult(SMTError Error) : Error_(std::move(Error)), HasValue_(false) {}

  explicit operator bool() const noexcept { return HasValue_; }

  const T &value() const {
    fatalErrorIf(!HasValue_, "Accessing value of failed SMTResult");
    return Value_;
  }

  T &value() {
    fatalErrorIf(!HasValue_, "Accessing value of failed SMTResult");
    return Value_;
  }

  const SMTError &error() const {
    fatalErrorIf(HasValue_, "Accessing error of successful SMTResult");
    return Error_;
  }

private:
  T Value_{};
  SMTError Error_{};
  bool HasValue_ = false;
};

/// Sparse model of an array expression, produced by
/// SMTSolver::getArrayValues after a SAT check.
///
/// The model value of the array at index `i` is the element of the first
/// entry whose index has the same model value as `i`, or the value of
/// `Base` when no entry matches. `Base` is a null ref when the solver did
/// not report a default — every constrained index is then covered by an
/// entry, and unlisted indexes are unconstrained.
///
/// Both expressions in each entry and `Base` are valid arguments to the
/// model-value getters (getBV, getBool, ...) for as long as the model that
/// produced them stays current (no new constraints or checks).
struct ArrayModel {
  SMTExprRef Base;
  std::vector<std::pair<SMTExprRef, SMTExprRef>> Entries;
};

/// Generic base class for SMT Solvers
///
/// This class is responsible for wrapping all sorts and expression generation,
/// through the mk* methods.
///
/// Threading contract:
///   * An SMTSolver instance is NOT thread-safe. All mutating and querying
///     methods (mk*, addConstraint, push/pop, check, get*, reset, dump...)
///     must be serialized by the caller; a single solver is intended for use
///     from one thread at a time. Concurrent solving should be done with one
///     solver per thread.
///   * SMTExprRef and SMTSortRef handles are nullable, copyable, and safe to
///     read concurrently from any thread as long as the owning solver
///     outlives the read. The handle's liveness check is race-free against
///     reset()/destruction on another thread: a stale handle deterministically
///     aborts via fatalError() rather than reading freed memory.
class SMTSolver {
public:
  SMTSolver() = default;
  virtual ~SMTSolver() = default;

  /// Returns a boolean sort.
  virtual SMTSortRef mkBoolSort() = 0;

  /// Returns an integer sort.
  virtual SMTSortRef mkIntSort() = 0;

  /// Returns a real sort.
  virtual SMTSortRef mkRealSort() = 0;

  /// Returns an appropriate bitvector sort for the given bitwidth.
  virtual SMTSortRef mkBVSort(const unsigned BitWidth) = 0;

  /// Returns an appropriate rounding mode sort.
  virtual SMTSortRef mkRMSort(FPEncoding Encoding) = 0;

  /// Returns an appropriate floating-point sort for the given bitwidth.
  /// Both widths must be non-zero and their total must fit a bit-vector
  /// sort. Under FPEncoding::BV the format must also satisfy
  /// 2*(SigWidth+1) + 5 <= 2^(ExpWidth+1) - 1, since a significand too
  /// wide for its exponent cannot be renormalized within the encoding's
  /// exponent arithmetic; such formats abort instead of misrounding.
  virtual SMTSortRef mkFPSort(const unsigned ExpWidth, const unsigned SigWidth,
                              FPEncoding Encoding) = 0;

  /// Convenience method to create a 32 bits long a floating-point sort.
  virtual SMTSortRef mkFP32Sort(FPEncoding Encoding) = 0;

  /// Convenience method to create a 64 bits long a floating-point sort.
  virtual SMTSortRef mkFP64Sort(FPEncoding Encoding) = 0;

  /// Returns an appropriate array sort.
  virtual SMTSortRef mkArraySort(const SMTSortRef &IndexSort,
                                 const SMTSortRef &ElemSort) = 0;

  /// Returns an appropriate function sort.
  virtual SMTSortRef mkFunctionSort(const std::vector<SMTSortRef> &DomainSorts,
                                    const SMTSortRef &CodomainSort) = 0;

  /// Returns an appropriate tuple sort.
  virtual SMTSortRef
  mkTupleSort(const std::vector<SMTSortRef> &ElementSorts) = 0;

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

  /// Creates a bitvector xnor operation
  virtual SMTExprRef mkBVXnor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector nor operation
  virtual SMTExprRef mkBVNor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a bitvector nand operation
  virtual SMTExprRef mkBVNand(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

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

  /// Creates a boolean predicate that is true iff the infinitely-precise
  /// signed sum of LHS and RHS is not representable at the operands'
  /// bit-width. Equivalent to SMT-LIB's bvsaddo.
  virtual SMTExprRef mkBVSAddOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// Creates a boolean predicate that is true iff the infinitely-precise
  /// unsigned sum of LHS and RHS is not representable at the operands'
  /// bit-width. Equivalent to SMT-LIB's bvuaddo.
  virtual SMTExprRef mkBVUAddOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// Creates a boolean predicate that is true iff the infinitely-precise
  /// signed difference LHS - RHS is not representable at the operands'
  /// bit-width. Equivalent to SMT-LIB's bvssubo.
  virtual SMTExprRef mkBVSSubOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// Creates a boolean predicate that is true iff the infinitely-precise
  /// unsigned difference LHS - RHS is not representable at the operands'
  /// bit-width. Equivalent to SMT-LIB's bvusubo.
  virtual SMTExprRef mkBVUSubOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// Creates a boolean predicate that is true iff the infinitely-precise
  /// signed product of LHS and RHS is not representable at the operands'
  /// bit-width. Equivalent to SMT-LIB's bvsmulo.
  virtual SMTExprRef mkBVSMulOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// Creates a boolean predicate that is true iff the infinitely-precise
  /// unsigned product of LHS and RHS is not representable at the operands'
  /// bit-width. Equivalent to SMT-LIB's bvumulo.
  virtual SMTExprRef mkBVUMulOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// Creates a boolean predicate that is true iff signed division LHS / RHS
  /// overflows, i.e. LHS is the minimal signed value and RHS is -1.
  /// Equivalent to SMT-LIB's bvsdivo. Division by zero is not an overflow.
  virtual SMTExprRef mkBVSDivOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// Creates a boolean predicate that is true iff signed negation of Exp
  /// overflows, i.e. Exp is the minimal signed value. Equivalent to
  /// SMT-LIB's bvnego.
  virtual SMTExprRef mkBVNegOverflow(const SMTExprRef &Exp) = 0;

  /// Creates a boolean not operation
  virtual SMTExprRef mkNot(const SMTExprRef &Exp) = 0;

  /// Creates a boolean equality operation
  virtual SMTExprRef mkEqual(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean implication operation
  virtual SMTExprRef mkImplies(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates a boolean and operation
  virtual SMTExprRef mkAnd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean or operation
  virtual SMTExprRef mkOr(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a boolean xor operation
  virtual SMTExprRef mkXor(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic unary minus operation.
  virtual SMTExprRef mkArithNeg(const SMTExprRef &Exp) = 0;

  /// Creates an arithmetic addition operation.
  virtual SMTExprRef mkArithAdd(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic subtraction operation.
  virtual SMTExprRef mkArithSub(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic multiplication operation.
  virtual SMTExprRef mkArithMul(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic division operation.
  virtual SMTExprRef mkArithDiv(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an integer modulus operation.
  virtual SMTExprRef mkArithMod(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an integer left-shift-by-constant operation.
  virtual SMTExprRef mkArithShl(const SMTExprRef &Exp, unsigned Amount) = 0;

  /// Creates an integer shift-left operation, equivalent to lhs * 2^rhs.
  virtual SMTExprRef mkArithShl(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic less-than operation.
  virtual SMTExprRef mkArithLt(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic greater-than operation.
  virtual SMTExprRef mkArithGt(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic less-than-or-equal operation.
  virtual SMTExprRef mkArithLe(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Creates an arithmetic greater-than-or-equal operation.
  virtual SMTExprRef mkArithGe(const SMTExprRef &LHS,
                               const SMTExprRef &RHS) = 0;

  /// Converts an integer expression to a real.
  virtual SMTExprRef mkInt2Real(const SMTExprRef &Exp) = 0;

  /// Converts an arithmetic expression to an integer via floor semantics.
  virtual SMTExprRef mkReal2Int(const SMTExprRef &Exp) = 0;

  /// Returns true iff an arithmetic expression denotes an integer.
  virtual SMTExprRef mkIsInt(const SMTExprRef &Exp) = 0;

  /// Converts an integer to a Width-bit bit-vector; the value is taken
  /// modulo 2^Width, so negative integers wrap to their two's-complement
  /// representation. Native on Z3, cvc5, and MathSAT; on backends without
  /// a native conversion (Yices, the SMT-LIB pipe) the result is a fresh
  /// bit-vector symbol constrained through the inverse direction, and
  /// that constraint lives at the current (push)/(pop) level — unlike
  /// mkIEEEFPToBV's tie, which is journalled and re-asserted after a pop
  /// because it states a definitional fact rather than an assumption.
  virtual SMTExprRef mkInt2BV(unsigned Width, const SMTExprRef &Exp) = 0;

  /// Converts a bit-vector to the integer it denotes: two's complement
  /// when IsSigned, the unsigned value in [0, 2^N) otherwise. Together
  /// with mkInt2BV this is the bridge for bitwise operations on integers
  /// (convert, apply the mkBV* operation, convert back).
  virtual SMTExprRef mkBV2Int(const SMTExprRef &Exp, bool IsSigned) = 0;

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

  /// Creates a bitvector reduction-or operation
  virtual SMTExprRef mkBVRedOr(const SMTExprRef &Exp) = 0;

  /// Creates a bitvector reduction-and operation
  virtual SMTExprRef mkBVRedAnd(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point absolute operation
  virtual SMTExprRef mkFPAbs(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point negation operation.
  /// `FlipSignBit` preserves the full IEEE encoding and only toggles the sign
  /// bit. `PreserveNaNPayload` follows the SMT floating-point standard and
  /// leaves NaNs unchanged.
  ///
  /// `FlipSignBit` is fully honored under BV encoding and via the SMTLIB
  /// pipeline. On native FP backends (Bitwuzla, CVC5, Z3) it is best-effort:
  /// these solvers treat all NaNs as a single equivalence class, so when the
  /// operand is a NaN the resulting NaN's bit pattern is not guaranteed to
  /// match a literal sign-bit flip of the input bits.
  virtual SMTExprRef
  mkFPNeg(const SMTExprRef &Exp,
          FPNegBehavior Behavior = FPNegBehavior::FlipSignBit) = 0;

  /// Creates a floating-point isInfinite operation
  virtual SMTExprRef mkFPIsInfinite(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isNaN operation
  virtual SMTExprRef mkFPIsNaN(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isSubnormal operation
  virtual SMTExprRef mkFPIsDenormal(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isNormal operation
  virtual SMTExprRef mkFPIsNormal(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point isZero operation
  virtual SMTExprRef mkFPIsZero(const SMTExprRef &Exp) = 0;

  /// Creates a floating-point multiplication operation
  virtual SMTExprRef mkFPMul(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const SMTExprRef &R) = 0;

  /// Creates a floating-point division operation
  virtual SMTExprRef mkFPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const SMTExprRef &R) = 0;

  /// Creates a floating-point remainder operation
  virtual SMTExprRef mkFPRem(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a floating-point addition operation
  virtual SMTExprRef mkFPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const SMTExprRef &R) = 0;

  /// Creates a floating-point subtraction operation
  virtual SMTExprRef mkFPSub(const SMTExprRef &LHS, const SMTExprRef &RHS,
                             const SMTExprRef &R) = 0;

  /// Creates a floating-point square root operation
  virtual SMTExprRef mkFPSqrt(const SMTExprRef &Exp, const SMTExprRef &R) = 0;

  /// Creates a floating-point fused-multiply add operation: round((x * y) + z)
  virtual SMTExprRef mkFPFMA(const SMTExprRef &X, const SMTExprRef &Y,
                             const SMTExprRef &Z, const SMTExprRef &R) = 0;

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

  /// Creates a floating-point conversion from floating-point to floating-point
  /// operation
  virtual SMTExprRef mkFPtoFP(const SMTExprRef &From, const SMTSortRef &To,
                              const SMTExprRef &R) = 0;

  /// Creates a floating-point conversion from signed bitvector to
  /// floating-point operation
  virtual SMTExprRef mkSBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const SMTExprRef &R) = 0;

  /// Creates a floating-point conversion from unsigned bitvector to
  /// floating-point operation
  virtual SMTExprRef mkUBVtoFP(const SMTExprRef &From, const SMTSortRef &To,
                               const SMTExprRef &R) = 0;

  /// Creates a floating-point conversion from floating-point to signed
  /// bitvector operation
  virtual SMTExprRef mkFPtoSBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floating-point to unsigned
  /// bitvector operation
  virtual SMTExprRef mkFPtoUBV(const SMTExprRef &From, unsigned ToWidth) = 0;

  /// Creates a floating-point conversion from floating-point to the closest
  /// integer, considering the rounding mode.
  virtual SMTExprRef mkFPtoIntegral(const SMTExprRef &From,
                                    const SMTExprRef &R) = 0;

  // --- Fixed-point arithmetic (TR 18037-shaped, Camada-encoded over BV) ---
  //
  // No solver has a native fixed-point theory, so every operation below is
  // encoded over bit-vectors in the common layer and works on all backends.
  // A fixed-point value of width W with N fractional bits represents
  // raw / 2^N, two's complement when signed.
  //
  // Operands of the binary operations may have different fixed-point
  // formats: following TR 18037's usual arithmetic conversions, the
  // operation is computed in the common full-precision format (max integer
  // bits, max fractional bits, signed if either operand is signed) and the
  // arithmetic result carries that format. Comparisons scale-align the same
  // way and return Bool.
  //
  // Non-saturating overflow is undefined behavior in C; the mkFXP*Overflow
  // and mkFXPDivByZero predicates report exactly the UB conditions, and the
  // value produced by an operation is meaningful only under the negation of
  // its predicate.

  /// Creates a fixed-point sort. Width must be non-zero; FracBits <= Width
  /// for unsigned formats and FracBits < Width for signed formats (the sign
  /// bit is not a fraction bit).
  ///
  /// TR 18037 also permits formats with padding bits, which this triple
  /// cannot express. No mainstream Clang target uses them, so they are
  /// deliberately out of scope; supporting them would add a fourth sort
  /// parameter rather than require a redesign.
  virtual SMTSortRef mkFXPSort(unsigned Width, unsigned FracBits,
                               bool IsSigned) = 0;

  /// Creates a fixed-point constant from a two's-complement binary string
  /// (exact at any width; the string length must equal the sort width).
  virtual SMTExprRef mkFXPFromBin(const std::string &RawBits,
                                  const SMTSortRef &To) = 0;

  /// Reinterprets a bit-vector of matching width as a fixed-point value.
  virtual SMTExprRef mkFXPFromRawBV(const SMTExprRef &Exp,
                                    const SMTSortRef &To) = 0;

  /// Reinterprets a fixed-point value as its underlying raw bit-vector.
  virtual SMTExprRef mkFXPToRawBV(const SMTExprRef &Exp) = 0;

  /// Creates a fixed-point addition.
  virtual SMTExprRef mkFXPAdd(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a fixed-point subtraction.
  virtual SMTExprRef mkFXPSub(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a fixed-point negation.
  virtual SMTExprRef mkFXPNeg(const SMTExprRef &Exp) = 0;

  /// Creates a fixed-point multiplication (truncating: the exact product's
  /// low fractional bits are dropped).
  virtual SMTExprRef mkFXPMul(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a fixed-point division. The quotient rounds toward negative
  /// infinity (floor), matching Clang's -ffixed-point behavior as pinned
  /// by the execution oracle.
  virtual SMTExprRef mkFXPDiv(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a fixed-point left shift by a concrete amount.
  virtual SMTExprRef mkFXPShl(const SMTExprRef &Exp, unsigned Amount) = 0;

  /// Creates a fixed-point right shift by a concrete amount (arithmetic for
  /// signed formats, logical for unsigned).
  virtual SMTExprRef mkFXPShr(const SMTExprRef &Exp, unsigned Amount) = 0;

  /// Creates a fixed-point less-than comparison (scale-aligned).
  virtual SMTExprRef mkFXPLt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a fixed-point less-than-or-equal comparison (scale-aligned).
  virtual SMTExprRef mkFXPLe(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a fixed-point greater-than comparison (scale-aligned).
  virtual SMTExprRef mkFXPGt(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a fixed-point greater-than-or-equal comparison (scale-aligned).
  virtual SMTExprRef mkFXPGe(const SMTExprRef &LHS, const SMTExprRef &RHS) = 0;

  /// Creates a fixed-point equality (scale-aligned; use this instead of
  /// mkEqual whenever the operand formats may differ).
  virtual SMTExprRef mkFXPEqual(const SMTExprRef &LHS,
                                const SMTExprRef &RHS) = 0;

  /// True iff the exact sum overflows the common format of the operands.
  virtual SMTExprRef mkFXPAddOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// True iff the exact difference overflows the common format.
  virtual SMTExprRef mkFXPSubOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// True iff the exact product overflows the common format. Tested on the
  /// pre-rounding product, so exact results just outside the representable
  /// range are reported even when truncation would land on a boundary.
  virtual SMTExprRef mkFXPMulOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// True iff the exact quotient overflows the common format (pre-rounding,
  /// as with mkFXPMulOverflow). Division by zero is reported separately by
  /// mkFXPDivByZero, not here.
  virtual SMTExprRef mkFXPDivOverflow(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) = 0;

  /// True iff the divisor is zero (undefined behavior in C).
  virtual SMTExprRef mkFXPDivByZero(const SMTExprRef &RHS) = 0;

  /// True iff negation overflows: the minimum value for signed formats, any
  /// non-zero value for unsigned formats.
  virtual SMTExprRef mkFXPNegOverflow(const SMTExprRef &Exp) = 0;

  /// True iff the left shift discards significant bits (or changes the sign
  /// for signed formats).
  virtual SMTExprRef mkFXPShlOverflow(const SMTExprRef &Exp,
                                      unsigned Amount) = 0;

  // Saturating variants (TR 18037 `_Sat` types / the FX pragmas in SAT
  // state). Saturation is an operation property, not a sort property: a
  // `_Sat` type shares its representation with the plain type, so the
  // frontend picks the sat variant by expression type, mirroring LLVM's
  // fixed-point intrinsics. Saturating overflow is defined behavior —
  // results clamp to the format's min/max and there is no paired
  // predicate — but division by zero remains UB even for `_Sat` types, so
  // mkFXPDivSat still pairs with mkFXPDivByZero.

  /// Saturating fixed-point addition.
  virtual SMTExprRef mkFXPAddSat(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  /// Saturating fixed-point subtraction.
  virtual SMTExprRef mkFXPSubSat(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  /// Saturating fixed-point negation (unsigned formats clamp to zero for
  /// any non-zero operand; signed formats clamp the minimum to the max).
  virtual SMTExprRef mkFXPNegSat(const SMTExprRef &Exp) = 0;

  /// Saturating fixed-point multiplication.
  virtual SMTExprRef mkFXPMulSat(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  /// Saturating fixed-point division. The value is meaningful only under
  /// the negation of mkFXPDivByZero.
  virtual SMTExprRef mkFXPDivSat(const SMTExprRef &LHS,
                                 const SMTExprRef &RHS) = 0;

  /// Saturating fixed-point left shift.
  virtual SMTExprRef mkFXPShlSat(const SMTExprRef &Exp, unsigned Amount) = 0;

  // Runtime-amount shift variants: C allows `x << n` with a runtime n, so
  // each shift takes an Amount expression (a bit-vector of the operand's
  // width). The value is meaningful under Amount < Width — C's own shift
  // constraint, which the consumer's UB check guards; at or beyond the
  // width the SMT shift semantics (zero) apply.

  /// Left shift by a runtime amount.
  virtual SMTExprRef mkFXPShlExpr(const SMTExprRef &Exp,
                                  const SMTExprRef &Amount) = 0;

  /// Right shift by a runtime amount (arithmetic for signed formats).
  virtual SMTExprRef mkFXPShrExpr(const SMTExprRef &Exp,
                                  const SMTExprRef &Amount) = 0;

  /// True iff the runtime-amount left shift discards significant bits
  /// (or changes the sign for signed formats).
  virtual SMTExprRef mkFXPShlOverflowExpr(const SMTExprRef &Exp,
                                          const SMTExprRef &Amount) = 0;

  /// Saturating left shift by a runtime amount.
  virtual SMTExprRef mkFXPShlSatExpr(const SMTExprRef &Exp,
                                     const SMTExprRef &Amount) = 0;

  /// Converts between fixed-point formats (truncating on narrowing).
  virtual SMTExprRef mkFXPToFXP(const SMTExprRef &Exp,
                                const SMTSortRef &To) = 0;

  /// True iff the value does not fit the target format of a mkFXPToFXP
  /// conversion.
  virtual SMTExprRef mkFXPToFXPOverflow(const SMTExprRef &Exp,
                                        const SMTSortRef &To) = 0;

  /// Saturating fixed-point format conversion: out-of-range values clamp
  /// to the target format's min/max instead of being undefined.
  virtual SMTExprRef mkFXPToFXPSat(const SMTExprRef &Exp,
                                   const SMTSortRef &To) = 0;

  /// Converts an integer bit-vector into a fixed-point value. SrcSigned is
  /// the signedness of the SOURCE integer type: it governs the value (C's
  /// int-to-fixed conversion converts the source value, so int8 0xFF is -1
  /// while uint8 0xFF is 255), independent of the target format's
  /// signedness, which only governs the representation.
  virtual SMTExprRef mkFXPFromBV(const SMTExprRef &Exp, bool SrcSigned,
                                 const SMTSortRef &To) = 0;

  /// Converts a fixed-point value to an integer bit-vector of the given
  /// width, rounding toward zero (the direction TR 18037 specifies for
  /// fixed-point to integer conversion).
  virtual SMTExprRef mkFXPToBV(const SMTExprRef &Exp, unsigned ToWidth) = 0;

  /// True iff the toward-zero integer part does not fit the target
  /// integer type's range: [0, 2^w-1] for an unsigned target,
  /// two's-complement bounds for a signed one. The plain mkFXPToBV needs
  /// no signedness parameter — its value bits are the integral part mod
  /// 2^w either way; only this range report and mkFXPToBVSat's clamp
  /// depend on the target's signedness.
  virtual SMTExprRef mkFXPToBVOverflow(const SMTExprRef &Exp, unsigned ToWidth,
                                       bool ToSigned) = 0;

  /// Saturating fixed-point to integer conversion (round toward zero,
  /// then clamp to the TARGET integer type's range — a negative source
  /// clamps to zero for an unsigned target.
  virtual SMTExprRef mkFXPToBVSat(const SMTExprRef &Exp, unsigned ToWidth,
                                  bool ToSigned) = 0;

  /// Rounds a fixed-point value to Digits fractional bits, keeping the
  /// same format (the low fraction bits become zero) — TR 18037's
  /// `roundfx`. Rounds to nearest, breaking ties per Tie, and saturates
  /// to the format's maximum when the rounding would carry past it.
  /// Digits >= the format's fraction width returns the value unchanged.
  virtual SMTExprRef mkFXPRound(const SMTExprRef &Exp, unsigned Digits,
                                FXPRoundTie Tie) = 0;

  /// Absolute value — TR 18037's `absfx`. Saturates: the most negative
  /// value of a signed format has no positive counterpart, so it maps to
  /// the format's maximum rather than overflowing (LLVM libc's choice;
  /// the composition mkIte(mkFXPLt(x,0), mkFXPNeg(x), x) wraps there
  /// instead). Unsigned formats return the value unchanged.
  virtual SMTExprRef mkFXPAbs(const SMTExprRef &Exp) = 0;

  /// Count leading sign bits — TR 18037's `countlsfx`: the number of
  /// redundant copies of the sign bit, i.e. how far the value can be
  /// shifted left before it changes sign. Returns a bit-vector of
  /// ToWidth bits. The largest possible count is the number of counted
  /// bits — the format width for an unsigned format, one less for a
  /// signed one, since the sign bit itself is not redundant — and a
  /// ToWidth too narrow to hold that aborts rather than silently
  /// wrapping. For unsigned formats it counts leading zeros.
  virtual SMTExprRef mkFXPCountls(const SMTExprRef &Exp, unsigned ToWidth) = 0;

  /// Square root, correctly rounded to nearest with ties to even: the
  /// representable value closest to the true square root at the format's
  /// scale. Always representable — square root contracts on [0, max] for
  /// every format, so no saturation is possible.
  ///
  /// Nearest rather than toward zero because camada is meant to serve as
  /// an oracle: an implementation being checked against it should be
  /// compared with the exact answer, not with a floor that is up to one
  /// ulp below it. Nothing in TR 18037 pins the direction — the standard
  /// has no sqrtfx — so unlike the truncating conversions elsewhere in
  /// this API, which reproduce C's semantics deliberately, this one is
  /// free to be exact.
  ///
  /// This is the exact mathematical operation, NOT a reproduction of any
  /// library's `sqrtfx`. LLVM libc computes a Sollya-generated linear
  /// approximation refined by Newton steps and documents an error bound
  /// rather than correct rounding, and avr-libc has its own approximation
  /// with different error; the two do not agree bit-for-bit with each
  /// other or with this. A consumer verifying a program that calls a
  /// specific library's `sqrtfx` is reproducing that library's
  /// approximation error, which is not something a shared layer can bake
  /// in.
  ///
  /// Negative operands have no real square root; the result is zero for
  /// them. There is no paired predicate because the condition is just
  /// `x < 0` — a consumer that needs to assert it writes
  /// mkFXPLt(x, zero), which produces the same term.
  virtual SMTExprRef mkFXPSqrt(const SMTExprRef &Exp) = 0;

  /// Base-e exponential, correctly rounded to nearest with ties to even,
  /// saturating to the format's maximum where the true value does not fit
  /// and giving zero where it rounds below half an ulp — TR 18037's
  /// `expfx`. Like mkFXPSqrt this is the exact mathematical operation,
  /// not a reproduction of any library's approximation; LLVM libc's
  /// `exphk`/`expk` document a relative error bound rather than correct
  /// rounding, so this is what such a claim can be checked against.
  ///
  /// Supported only on the fixed-point formats C actually has an _Accum
  /// type for, and only those whose hardest-to-round input has been
  /// measured (see scripts/fxp_exp_bounds.txt): (16,7), (16,8), (32,15),
  /// (32,16), (64,31) and (64,32). Any other format aborts.
  ///
  /// The restriction is a property of the operation, not an omission.
  /// Correct rounding needs an intermediate wide enough to decide every
  /// rounding, which needs to know how close exp() ever lands to a
  /// halfway point, and that distance is established by an exhaustive
  /// sweep whose cost grows as 2^FracBits. Sweeping every 64-bit format
  /// would take on the order of 10^4 years, and no bound generalises
  /// between formats: both the sample spacing and the saturation cutoff
  /// move with the format. Every other fixed-point operation is exact
  /// algebra and works at any width.
  virtual SMTExprRef mkFXPExp(const SMTExprRef &Exp) = 0;

  /// Converts a fixed-point value to a floating-point value of the given
  /// sort, rounding once per R. C's fixed-to-float conversion rounds to
  /// nearest even: pass RM::ROUND_TO_EVEN (Clang's direction, pinned by
  /// the execution oracle). Always defined — every fixed-point range is
  /// tiny next to any floating-point range. R is the enum, not a
  /// rounding-mode expression: the encoding routes through an exact wide
  /// intermediate whose encoding it chooses internally (falling back to
  /// the BV encoder when the backend's native formats cannot hold the
  /// intermediate), so it mints the rounding-mode term itself.
  virtual SMTExprRef mkFXPToFP(const SMTExprRef &Exp, const SMTSortRef &To,
                               RM R) = 0;

  /// Converts a floating-point value to a fixed-point value, rounding
  /// toward zero — C's float-to-fixed direction, which differs from
  /// fixed-to-fixed narrowing (floor); both pinned by the execution
  /// oracle. The value is meaningful only under the negation of
  /// mkFPToFXPOverflow (out-of-range, infinity, and NaN stay UB in C).
  virtual SMTExprRef mkFPToFXP(const SMTExprRef &Exp, const SMTSortRef &To) = 0;

  /// True iff the float-to-fixed conversion is undefined: NaN, +-infinity,
  /// or the toward-zero result lies outside the target format's range.
  virtual SMTExprRef mkFPToFXPOverflow(const SMTExprRef &Exp,
                                       const SMTSortRef &To) = 0;

  /// Saturating float-to-fixed conversion, defined for every input:
  /// out-of-range values and +-infinity clamp to the format's rails, NaN
  /// converts to 0 (Clang's choice for _Sat targets; the TR leaves it
  /// undefined).
  virtual SMTExprRef mkFPToFXPSat(const SMTExprRef &Exp,
                                  const SMTSortRef &To) = 0;

  /// Creates an array select operation. It returns the element in position
  /// Index of Array.
  virtual SMTExprRef mkArraySelect(const SMTExprRef &Array,
                                   const SMTExprRef &Index) = 0;

  /// Creates an array store operation. It stores Element in position Index of
  /// Array.
  virtual SMTExprRef mkArrayStore(const SMTExprRef &Array,
                                  const SMTExprRef &Index,
                                  const SMTExprRef &Element) = 0;

  /// Creates a tuple value from the given elements.
  virtual SMTExprRef mkTuple(const std::vector<SMTExprRef> &Elements) = 0;

  /// Selects the element at Index from Tuple.
  virtual SMTExprRef mkTupleSelect(const SMTExprRef &Tuple, unsigned Index) = 0;

  /// Returns a tuple equal to Tuple except that the element at Index is
  /// replaced by Value; all other elements are unchanged. Index is a
  /// concrete index — symbolic field selection is deliberately not part
  /// of the API.
  virtual SMTExprRef mkTupleUpdate(const SMTExprRef &Tuple, unsigned Index,
                                   const SMTExprRef &Value) = 0;

  /// Applies a function symbol to arguments.
  virtual SMTExprRef mkApply(const SMTExprRef &Function,
                             const std::vector<SMTExprRef> &Args) = 0;

  /// Creates a universally quantified formula over Vars with Body.
  virtual SMTExprRef mkForall(const std::vector<SMTExprRef> &Vars,
                              const SMTExprRef &Body) = 0;

  /// Creates an existentially quantified formula over Vars with Body.
  virtual SMTExprRef mkExists(const std::vector<SMTExprRef> &Vars,
                              const SMTExprRef &Body) = 0;

  /// If a model is available, returns the value of a given boolean symbol.
  ///
  /// On failure, returns an `SMTError` instead of aborting.
  virtual SMTResult<bool> getBool(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given bitvector
  /// symbol as a 64-bits int.
  virtual SMTResult<int64_t> getBV(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given bitvector
  /// symbol as a 2-complement form binary string.
  virtual SMTResult<std::string> getBVInBin(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given integer expression
  /// as a decimal string.
  virtual SMTResult<std::string> getInt(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given real expression
  /// as a rational numerator/denominator in decimal string form.
  virtual SMTResult<std::pair<std::string, std::string>>
  getRational(const SMTExprRef &Exp) = 0;

  /// Convenience method to get the numerator of a real expression value.
  virtual SMTResult<std::string> getRealNumerator(const SMTExprRef &Exp) = 0;

  /// Convenience method to get the denominator of a real expression value.
  virtual SMTResult<std::string> getRealDenominator(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given floating-point
  /// symbol as a binary string in the IEEE-754 format: 1 bit for the sign + N
  /// bits for the exponent + M bits for the significand.
  virtual SMTResult<std::string> getFPInBin(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given floating-point
  /// symbol as float. We assume the floating-point is using the IEEE-754
  /// format: 1 bit for the sign + 8 bits for the exponent + 23 bits for the
  /// significand and 1 hidden bit in the significand
  virtual SMTResult<float> getFP32(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the value of a given floating-point
  /// symbol as double. We assume the floating-point is using the IEEE-754
  /// format: 1 bit for the sign + 11 bits for the exponent + 52 bits for the
  /// significand and 1 hidden bit in the significand
  virtual SMTResult<double> getFP64(const SMTExprRef &Exp) = 0;

  /// Exact fixed-point model value: the raw two's-complement bits plus the
  /// format needed to interpret them (value = raw / 2^FracBits). Kept as a
  /// binary string so any width round-trips exactly.
  struct FXPValue {
    std::string RawBits;
    unsigned FracBits = 0;
    bool IsSigned = false;
  };

  /// If a model is available, returns the exact value of a given fixed-point
  /// expression.
  virtual SMTResult<FXPValue> getFXP(const SMTExprRef &Exp) = 0;

  /// If a model is available, returns the Expr in position Index of Array
  virtual SMTExprRef getArrayElement(const SMTExprRef &Array,
                                     const SMTExprRef &Index) = 0;

  /// If a model is available, returns the model's sparse representation of
  /// an array expression: the finite set of (index, element) entries the
  /// solver's model distinguishes, plus the default element every other
  /// index reads (see ArrayModel). The entry list is whatever finite shape
  /// the model uses — it is not an enumeration of the index space, and its
  /// size is unspecified. Backends without a walkable array model (STP
  /// symbol arrays, the SMT-LIB pipeline) return an UnsupportedOperation
  /// error.
  virtual SMTResult<ArrayModel> getArrayValues(const SMTExprRef &Array) = 0;

  /// Constructs an SMTExprRef from a boolean.
  virtual SMTExprRef mkBool(const bool b) = 0;

  /// Constructs an SMTExprRef from an integer.
  virtual SMTExprRef mkInt(int64_t v) = 0;

  /// Constructs an SMTExprRef from a base-10 integer string.
  virtual SMTExprRef mkInt(const std::string &v) = 0;

  /// Constructs an SMTExprRef from a real written as base-10 SMT-LIB numeral
  /// text.
  virtual SMTExprRef mkReal(const std::string &v) = 0;

  /// Constructs an SMTExprRef from an integral real.
  virtual SMTExprRef mkReal(int64_t v) = 0;

  /// Constructs an SMTExprRef from a rational real numerator/denominator.
  virtual SMTExprRef mkReal(int64_t num, int64_t den) = 0;

  /// Constructs an SMTExprRef from an integer in base 10 and its sort
  virtual SMTExprRef mkBVFromDec(const int64_t Int, const SMTSortRef &Sort) = 0;

  /// Convenience method to create a bitvector from an integer in base 10 and
  /// its bitwidth
  virtual SMTExprRef mkBVFromDec(const int64_t Int, unsigned BitWidth) = 0;

  /// Constructs an SMTExprRef from an integer in base 2 and its sort
  virtual SMTExprRef mkBVFromBin(const std::string &Int,
                                 const SMTSortRef &Sort) = 0;

  /// Convenience method to create a bitvector from an integer in base 2 and
  /// its bitwidth
  virtual SMTExprRef mkBVFromBin(const std::string &Int, unsigned BitWidth) = 0;

  /// Convenience method to create a bitvector from an integer in base 2
  virtual SMTExprRef mkBVFromBin(const std::string &Int) = 0;

  /// Creates a new symbol, given a name and a sort
  virtual SMTExprRef mkSymbol(const std::string &Name,
                              const SMTSortRef &Sort) = 0;

  /// Constructs a floating-point from a binary string, in the IEEE-754 format:
  /// 1 bit for the sign + N bits for the exponent + M bits for the significand
  virtual SMTExprRef mkFPFromBin(const std::string &FP, unsigned EWidth,
                                 FPEncoding Encoding) = 0;

  /// Constructs an SMTExprRef from a float. We assume the floating-point is
  /// using the IEEE-754 format: 1 bit for the sign + 8 bits for the exponent +
  /// 23 bits for the significand and 1 hidden bit in the significand
  virtual SMTExprRef mkFP32(const float Float, FPEncoding Encoding) = 0;

  /// Constructs an SMTExprRef from a double.  We assume the floating-point is
  /// using the IEEE-754 format: 1 bit for the sign + 11 bits for the exponent +
  /// 52 bits for the significand and 1 hidden bit in the significand
  virtual SMTExprRef mkFP64(const double Double, FPEncoding Encoding) = 0;

  /// Returns an appropriate floating-point rounding mode.
  virtual SMTExprRef mkRM(const RM &R, FPEncoding Encoding) = 0;

  /// Returns a NaN floating-point
  virtual SMTExprRef mkNaN(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth, FPEncoding Encoding) = 0;

  /// Convenience method to create 32 bits long NaN
  virtual SMTExprRef mkNaN32(const bool Sgn, FPEncoding Encoding) = 0;

  /// Convenience method to create 64 bits long NaN
  virtual SMTExprRef mkNaN64(const bool Sgn, FPEncoding Encoding) = 0;

  /// Returns a Inf floating-point
  virtual SMTExprRef mkInf(const bool Sgn, const unsigned ExpWidth,
                           const unsigned SigWidth, FPEncoding Encoding) = 0;

  /// Convenience method to create 32 bits long Inf
  virtual SMTExprRef mkInf32(const bool Sgn, FPEncoding Encoding) = 0;

  /// Convenience method to create 64 bits long Inf
  virtual SMTExprRef mkInf64(const bool Sgn, FPEncoding Encoding) = 0;

  /// Creates an array and initializes all elements to InitValue, choosing
  /// the lowering automatically (see ConstArrayLowering::Auto).
  virtual SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                                  const SMTExprRef &InitValue) = 0;

  /// Creates an array and initializes all elements to InitValue with an
  /// explicit lowering strategy.
  virtual SMTExprRef mkArrayConst(const SMTSortRef &IndexSort,
                                  const SMTExprRef &InitValue,
                                  ConstArrayLowering Lowering) = 0;

  /// Reinterpret a bitvector as a floating-point, using the IEEE format
  virtual SMTExprRef mkBVToIEEEFP(const SMTExprRef &Exp,
                                  const SMTSortRef &To) = 0;

  /// Reinterpret a floating-point as a bitvector, using the IEEE format.
  ///
  /// NaN caveat: the underlying operation (fp.to_ieee_bv) is
  /// underspecified for NaN inputs — the FP sort has a single NaN value
  /// while the bit-vector encoding has many NaN patterns, so no function
  /// out of the sort can recover which pattern produced a NaN, and a
  /// backend may answer with any of them. Camada compensates where it can
  /// PROVE the bits: when Exp was built by mkBVToIEEEFP or an FP-constant
  /// constructor, or a top-level asserted equality ties it to such a
  /// term, the original bit pattern is returned exactly (a term-level
  /// rewrite, uniform across backends, exact for round-trips like
  /// byte-level memory models). The trade: with that rewrite the result
  /// is a function of the TERM's provenance, not only of the FP value —
  /// two value-equal NaN terms may report different patterns, which is
  /// C's memory semantics rather than SMT-LIB's functional one.
  ///
  /// IMPORTANT: a term whose provenance camada cannot prove falls back to
  /// the underspecified backend operation SILENTLY — there is no
  /// diagnostic. Callers that need unconditional bit-exactness must use
  /// FPEncoding::BV, where FP values ARE their bit patterns.
  ///
  /// The fallback is nevertheless FUNCTIONALLY CONSISTENT on every
  /// backend: value-equal FP terms report equal bits. Z3 and MathSAT get
  /// this from their native fp->bv primitives; backends without one
  /// (bitwuzla, cvc5, the SMT-LIB pipeline) emulate the primitive as a
  /// per-sort uninterpreted function tied per-term by `to_fp(fn(x)) == x`,
  /// so functional congruence provides the same guarantee. The tie is a
  /// definitional fact re-asserted across (pop), so the result stays
  /// meaningful at any nesting level.
  virtual SMTExprRef mkIEEEFPToBV(const SMTExprRef &Exp) = 0;

  /// Check if the constraints are satisfiable
  virtual checkResult check() = 0;

  /// Set a wall-clock time limit, in milliseconds, applied to each
  /// subsequent check() or checkSatAssuming() individually; 0 removes the
  /// limit. A check that hits the limit returns checkResult::UNKNOWN and
  /// leaves the solver usable. The limit persists across reset(). Returns
  /// false when the backend cannot enforce time limits — the limit is
  /// then ignored. Equivalently queryable up front as
  /// supports(SolverFeature::Timeouts).
  virtual bool setTimeout(uint64_t Milliseconds) = 0;

  /// Check if the constraints conjoined with the given boolean assumptions
  /// are satisfiable. The assumptions are only active for this query: they
  /// have no effect on the satisfiability of later checks. (Backends whose
  /// native API only accepts literals lower compound assumptions through
  /// fresh activation literals, which is observable in dump() output.)
  virtual checkResult
  checkSatAssuming(const std::vector<SMTExprRef> &Assumptions) = 0;

  /// Returns the subset of the assumptions the solver used to derive
  /// unsatisfiability. Only valid right after a checkSatAssuming() call
  /// that returned UNSAT: any solver mutation (addConstraint, push, pop,
  /// reset) or later check invalidates the result, and querying it then is
  /// an error. Backends reporting
  /// supports(SolverFeature::UnsatAssumptions) == false return an
  /// UnsupportedOperation error.
  virtual SMTResult<std::vector<SMTExprRef>> getUnsatAssumptions() = 0;

  /// Reset the solver and remove all constraints.
  virtual void reset() = 0;

  /// Create a new assertion scope.
  virtual void push(unsigned nscopes = 1) = 0;

  /// Pop one or more assertion scopes.
  virtual void pop(unsigned nscopes = 1) = 0;

  /// Returns whether this backend implements the given feature. See the
  /// SolverFeature enumerators for what each bit covers.
  virtual bool supports(SolverFeature Feature) const = 0;

  /// Returns the solver name and version
  virtual std::string getSolverNameAndVersion() const = 0;

  /// Dump formula
  virtual void dump() = 0;
  virtual void dump(std::string &Out) = 0;

  /// Dump Model
  virtual void dumpModel() = 0;
  virtual void dumpModel(std::string &Out) = 0;
};

/// Unique pointer for SMTSolvers.
using SMTSolverRef = std::unique_ptr<SMTSolver>;

/// Convenience method to create a Z3Solver object. `ArrayMode` selects the
/// array encoding (see ArrayEncoding); the default keeps Z3's native theory
/// of arrays.
SMTSolverRef createZ3Solver(ArrayEncoding ArrayMode = ArrayEncoding::Native);

/// Convenience method to create a MathSATSolver object. `ArrayMode`
/// selects the array encoding (see ArrayEncoding).
SMTSolverRef
createMathSATSolver(ArrayEncoding ArrayMode = ArrayEncoding::Native);

/// Convenience method to create a CVC5Solver object. Core extraction via
/// getUnsatAssumptions() is opt-in (see UnsatAssumptionsMode); `ArrayMode`
/// selects the array encoding (see ArrayEncoding).
SMTSolverRef
createCVC5Solver(UnsatAssumptionsMode Mode = UnsatAssumptionsMode::Off,
                 ArrayEncoding ArrayMode = ArrayEncoding::Native);

/// Convenience method to create a BitwuzlaSolver object. Core extraction
/// via getUnsatAssumptions() is opt-in (see UnsatAssumptionsMode);
/// `ArrayMode` selects the array encoding (see ArrayEncoding).
SMTSolverRef
createBitwuzlaSolver(UnsatAssumptionsMode Mode = UnsatAssumptionsMode::Off,
                     ArrayEncoding ArrayMode = ArrayEncoding::Native);

/// Convenience method to create a YicesSolver object. `ArrayMode` selects
/// the array encoding (see ArrayEncoding).
SMTSolverRef createYicesSolver(ArrayEncoding ArrayMode = ArrayEncoding::Native);

/// Convenience method to create a STPSolver object. `ArrayMode` selects
/// the array encoding (see ArrayEncoding); Ackermann mode keeps arrays out
/// of STP entirely, replacing its non-extensional array theory.
SMTSolverRef createSTPSolver(ArrayEncoding ArrayMode = ArrayEncoding::Native);

/// Create an SMT-LIB-backed solver that drives an external solver process.
///
/// The child is spawned with `execvp(Argv[0], Argv)`. Argv[0] is the solver
/// binary (path or PATH-resolvable name); subsequent entries are passed
/// verbatim as separate argv entries. No shell is involved, so spaces,
/// quotes, and other shell metacharacters in any entry carry no special
/// meaning — safe to use with paths/arguments coming from configuration,
/// environment, or other untrusted sources.
///
/// Examples:
///   createSMTLIBSolver({"z3", "-in"})
///   createSMTLIBSolver({"cvc5", "--lang", "smt2", "--incremental"})
///   createSMTLIBSolver({"/path/to/solver", "--some-flag"})
///
/// The child must speak standard SMT-LIB on stdin/stdout. Camada sends
/// `(set-option :print-success true)` to it at startup, so any solver that
/// honors that contract works.
SMTSolverRef
createSMTLIBSolver(const std::vector<std::string> &Argv,
                   TupleEncoding TupleMode = TupleEncoding::Native,
                   ArrayEncoding ArrayMode = ArrayEncoding::Native);

/// Same as `createSMTLIBSolver(Argv)` but also tees the emitted SMT-LIB
/// script to OutputPath (or stdout if OutputPath is "-") for offline
/// reproduction.
SMTSolverRef
createSMTLIBSolver(const std::vector<std::string> &Argv,
                   const std::string &OutputPath,
                   TupleEncoding TupleMode = TupleEncoding::Native,
                   ArrayEncoding ArrayMode = ArrayEncoding::Native);

} // namespace camada

#endif
