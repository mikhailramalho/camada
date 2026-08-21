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

#ifndef CAMADATYPES_H_
#define CAMADATYPES_H_

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

// SMTError carries an SMTBackendKind, and ArrayModel holds SMTExprRefs.
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
enum class FPEncoding : bool { Native, BV };

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
enum class ConstArrayLowering : std::uint8_t { Auto, Native, Lazy };

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
enum class FPNegBehavior : bool {
  FlipSignBit,
  PreserveNaNPayload,
};

/// Rounding direction for the fixed-point operations that discard bits.
///
/// Separate from `RM` rather than reusing it, because fixed point needs a
/// mode IEEE-754 has no name for. TR 18037's `roundfx` rounds to nearest
/// but leaves the halfway direction to the implementation, and LLVM libc
/// breaks ties toward positive infinity — nearest for every other value.
/// `RM::ROUND_TO_PLUS_INF` is a different operation: it rounds *all*
/// values up, so 0.25 becomes 1 where nearest-ties-up leaves it 0. With no
/// RM member denoting "nearest, ties toward +inf", reusing RM would have
/// silently dropped the one `roundfx` direction verified against an
/// executing implementation.
///
/// The three nearest modes differ only on exact halfway values:
///
/// - NearestTiesTowardPositive: 0.5 rounds to 1 and -0.5 rounds to 0.
///   LLVM libc's `roundfx` (it adds half an ulp and masks off the low
///   bits), and the only direction verified against a running libc.
/// - NearestTiesAwayFromZero: 0.5 rounds to 1 and -0.5 rounds to -1 —
///   symmetric about zero, what most C programmers expect from `round()`.
///   Equivalent to `RM::ROUND_TO_AWAY`.
/// - NearestTiesToEven: a halfway value rounds to whichever neighbour has
///   a zero in the last kept bit, IEEE-754's default and the unbiased
///   choice. Equivalent to `RM::ROUND_TO_EVEN`.
///
/// The directed modes never consult the halfway point:
///
/// - TowardZero: truncate. C's fixed-to-integer and float-to-fixed
///   direction, pinned by the execution oracle.
/// - TowardNegative: floor. What Clang's `-ffixed-point` division does —
///   verified: -0.5 / 0.75 gives -0.671875, not -0.6640625.
/// - TowardPositive: ceiling.
///
/// Every nearest mode saturates to the format's maximum when the rounding
/// would carry past it, which every implementation surveyed agrees on.
enum class FXPRM : std::uint8_t {
  NearestTiesTowardPositive,
  NearestTiesAwayFromZero,
  NearestTiesToEven,
  TowardZero,
  TowardNegative,
  TowardPositive,
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
enum class TupleEncoding : bool { Native, Camada };

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
enum class ArrayEncoding : bool { Native, Ackermann };

enum class RM : std::uint8_t {
  ROUND_TO_EVEN = 0,
  ROUND_TO_AWAY = 1,
  ROUND_TO_PLUS_INF = 2,
  ROUND_TO_MINUS_INF = 3,
  ROUND_TO_ZERO = 4,
};

enum class CheckResult : std::uint8_t { SAT, UNSAT, UNKNOWN };

/// Why a check returned CheckResult::UNKNOWN. Query through
/// SMTSolver::reasonUnknown(); meaningful only for the check that just
/// answered UNKNOWN.
enum class UnknownReason : std::uint8_t {
  /// The check hit the limit set by setTimeout().
  Timeout,
  /// The solver terminated the search without deciding: an incomplete
  /// fragment (quantifiers, non-linear arithmetic), a resource limit of
  /// its own, or a deliberate give-up.
  Incomplete,
  /// The backend reported an error rather than a result. The formula's
  /// satisfiability is unknown because the query did not run.
  BackendError,
  /// The SMT-LIB child answered with something other than a result --
  /// an `(error ...)` reply, a malformed line, or end-of-stream because
  /// it died. Also reported in write-only mode, where no solver ran.
  ProtocolError,
  /// No check has answered UNKNOWN yet, or the state has moved on.
  NotApplicable,
};

/// Capabilities a backend may or may not implement, queryable through
/// SMTSolver::supports() instead of discovering them through aborts or
/// UnsupportedOperation errors.
///
/// A true bit means the corresponding API surface is implemented for the
/// backend; individual calls can still fail for input-specific reasons
/// through their SMTResult. On the SMT-LIB pipeline backend the bits
/// describe what Camada emits — a particular child solver may still
/// reject a construct at runtime.
enum class SolverFeature : std::uint8_t {
  /// Int/Real sorts and arithmetic (mkIntSort, mkRealSort, mkArith*).
  IntRealArithmetic,
  /// Quantified formulas (mkForall, mkExists).
  Quantifiers,
  /// Uninterpreted functions (mkFunctionSort, mkApply).
  UninterpretedFunctions,
  /// FPEncoding::Native sorts and operations; FPEncoding::BV works on
  /// every backend regardless.
  NativeFloatingPoint,
  /// RM::ROUND_TO_AWAY as a native rounding mode. Separate from
  /// NativeFloatingPoint because MathSAT implements native FP but has no
  /// term for this mode, and mkRM() has nothing to return in that case.
  /// FPEncoding::BV supplies all five modes on every backend.
  NativeRoundToAway,
  /// Backend-native tuple/datatype sorts; other backends route tuples
  /// through the Camada per-field lowering. Like every bit here this is a
  /// property of the backend, not of this instance: it stays true on a
  /// solver configured for TupleEncoding::Camada, or for Ackermann arrays
  /// (which force the lowering because a datatype cannot hold an array
  /// member with no backend term). To ask what this solver will actually
  /// do, compose with tupleMode() and arrayMode().
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
enum class SMTErrorCode : std::uint8_t {
  None,
  BackendError,
  InvalidModelValue,
  UnsupportedOperation,
  /// The call sequence violated an API contract (e.g. querying unsat
  /// assumptions after the solver state changed), as opposed to a
  /// backend-originated failure.
  InvalidUsage,
};

/// Construction-frozen solver options, passed to every create*Solver()
/// factory (and the corresponding backend constructors). One struct for
/// all backends: a field a backend does not implement is silently
/// inapplicable there — the same contract UseUnsatAssumptions always had
/// (Z3, MathSAT, and Yices answer cores regardless of it). Default
/// construction gives the historical behavior of every backend.
///
/// Options that can change during the solver's lifetime (setTimeout) stay
/// methods; everything here is frozen because changing it mid-flight
/// would strand already-built terms or already-configured contexts.
struct SolverConfig {
  /// Caller-chosen logic. Empty (the default) keeps each backend's
  /// built-in choice. SMT-LIB: emitted verbatim as `(set-logic ...)`, no
  /// negotiation, child rejection is fatal (one-shot model children are
  /// dropped instead). Yices: the context logic (default QF_AUFBV).
  /// MathSAT: the default-configuration logic (default AUFBV; ignored by
  /// the constructor taking a caller-built msat_config).
  std::string Logic;

  /// SMT-LIB one-shot mode only: deadline in milliseconds for each
  /// protocol ack from the auxiliary model solver. Acks are instantaneous
  /// for any conforming child; one that stays silent past the deadline
  /// does not speak the `:print-success` protocol and is dropped, costing
  /// only counterexample support. Does not apply to the read of the model
  /// solver's own verdict, which may legitimately take as long as the
  /// solve.
  unsigned OneShotModelAckTimeoutMs = 5000;

  /// Array encoding (see ArrayEncoding). All backends.
  ArrayEncoding Arrays = ArrayEncoding::Native;

  /// Tuple lowering (see TupleEncoding). Native applies only where the
  /// backend has datatypes (Z3, CVC5, SMT-LIB); Camada forces the
  /// per-field lowering there too — useful to take the datatype engine
  /// out of the picture. Backends without datatypes always use the
  /// Camada lowering. Ackermann arrays force Camada tuples regardless.
  TupleEncoding Tuples = TupleEncoding::Native;

  /// Whether the context is created with unsat-assumption production
  /// enabled. Producing the core is not free: backends whose SAT engine
  /// must track assumption participation (Bitwuzla, CVC5) pay a
  /// solve-time cost on *every* check, and the setting is frozen at
  /// context creation -- so it is opt-in.
  ///
  /// False (the default) gives fast contexts: checkSatAssuming() works
  /// unchanged and getUnsatAssumptions() reports UnsupportedOperation.
  /// supports(SolverFeature::UnsatAssumptions) still answers true: it
  /// reports the backend's capability, not this setting. True makes
  /// the backend track assumptions so getUnsatAssumptions() returns real
  /// cores after an UNSAT checkSatAssuming().
  ///
  /// Backends that answer cores without a creation-time option (Z3
  /// enables unsat_core per query, MathSAT and Yices track natively)
  /// ignore this and always support core extraction.
  bool UseUnsatAssumptions = false;
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

/// Exact fixed-point model value: the raw two's-complement bits plus the
/// format needed to interpret them (value = raw / 2^FracBits). Kept as a
/// binary string so any width round-trips exactly.
struct FXPValue {
  std::string RawBits;
  unsigned FracBits = 0;
  bool IsSigned = false;
};

} // namespace camada

#endif
