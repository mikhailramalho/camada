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

#ifndef SMTLIBSOLVER_H_
#define SMTLIBSOLVER_H_

#include <cstdint>
#include <cstdio>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "../camadaexpr.h"
#include "../camadasort.h"
#include "../core/camadaimpl.h"

namespace camada {

class SMTLIBSolver;
using SMTLIBContextRef = SMTLIBSolver *;

/// SMT-LIB sort. The "native" representation is the SMT-LIB text for the sort
/// (e.g. "Bool", "(_ BitVec 32)"). There is no underlying solver context, so
/// the context-ref is a back-pointer to the owning SMTLIBSolver.
class SMTLIBSort : public SolverSort<SMTLIBContextRef, std::string> {
public:
  static constexpr SMTBackendKind BackendKindValue = SMTBackendKind::SMTLIB;
  using SolverSort<SMTLIBContextRef, std::string>::SolverSort;
  ~SMTLIBSort() override = default;

  SMTBackendKind getBackendKind() const override { return BackendKindValue; }

  unsigned getWidthFromSolver() const override;

  void dump(std::string &Out) const override;
  using SMTSort::dump;
};

/// Structural SMT-LIB term. Head is either the complete text of a terminal
/// (symbol, literal) or the operator head of a compound term whose operands
/// are in Args. Text is produced only at emission time (assert, get-value,
/// define-fun, dump): subterms referenced more than once within an emission
/// are bound to let temporaries, so heavily shared DAGs cost wire text
/// linear in the DAG size instead of their unfolded tree size.
struct SMTLIBTerm {
  std::string Head;
  std::vector<SMTExprRef> Args;
  /// Binder-style nodes (quantifiers): every Arg is rendered in its own
  /// let scope, since hoisting a subterm that mentions a bound variable
  /// past the binder would unbind it.
  bool OwnScope = false;
};

/// SMT-LIB expression carrying a structural SMTLIBTerm.
class SMTLIBExpr : public SolverExpr<SMTLIBContextRef, SMTLIBTerm> {
public:
  static constexpr SMTBackendKind BackendKindValue = SMTBackendKind::SMTLIB;
  using SolverExpr<SMTLIBContextRef, SMTLIBTerm>::SolverExpr;
  ~SMTLIBExpr() override = default;

  SMTBackendKind getBackendKind() const override { return BackendKindValue; }

  bool equal_to(SMTExpr const &Other) const override;

  void dump(std::string &Out) const override;
  using SMTExpr::dump;
};

/// Emits SMT-LIB output to a file (or stdout if path is "-").
///
/// SMTLIBSolver constructed with only a FileEmitter is purely write-only:
/// check() emits `(check-sat)` and returns UNKNOWN, get* queries error.
/// When paired with a ProcessEmitter, the same script is teed to disk
/// alongside the interactive solving session.
class FileEmitter {
public:
  explicit FileEmitter(const std::string &Path);
  FileEmitter(const FileEmitter &) = delete;
  FileEmitter &operator=(const FileEmitter &) = delete;
  ~FileEmitter() noexcept;

  void emitRaw(const std::string &Text) const;
  void flush() const;

  bool isOpen() const { return Out != nullptr; }

private:
  std::FILE *Out = nullptr;
  bool OwnsHandle = false;
};

/// Drives an external SMT-LIB-speaking solver via stdin/stdout pipes.
///
/// The child is spawned with `execvp(Argv[0], Argv)` — no shell involved, so
/// argv entries are passed verbatim and shell metacharacters (quotes, `;`,
/// `|`, `$()`, …) carry no special meaning. Argv[0] is resolved against
/// `$PATH` if it has no `/`, otherwise treated as a literal path.
///
/// The constructor sends `(set-option :print-success true)` at startup so
/// every non-query command produces a `success`/`error` response, giving a
/// deterministic resync point after each emitted line.
class ProcessEmitter {
public:
  explicit ProcessEmitter(const std::vector<std::string> &Argv);
  ProcessEmitter(const ProcessEmitter &) = delete;
  ProcessEmitter &operator=(const ProcessEmitter &) = delete;
  ~ProcessEmitter() noexcept;

  /// Write a chunk of SMT-LIB text to the child's stdin. The caller is
  /// responsible for terminating each command with a newline.
  void emitRaw(const std::string &Text) const;

  /// Flush the write side. Must be called before reading a response.
  void flush() const;

  /// Read one SMT-LIB response from the child. Returns the text with leading
  /// and trailing whitespace trimmed. Handles three shapes:
  ///   - bare token: `success`, `sat`, `unsat`, `unknown`
  ///   - parenthesized: `((<symbol> <value>))`
  ///   - error: `(error "...")`
  std::string readResponse() const;

  /// Like readResponse(), but waits at most `TimeoutMs` for the child to
  /// start answering (select on the pipe, same technique as
  /// drainResponses). Returns nullopt when nothing arrived in time and an
  /// empty string on EOF. Used for protocol acks from the auxiliary
  /// one-shot model solver, which must never block camada indefinitely.
  ///
  /// The select-vs-stdio-buffer caveat from drainResponses does not bite
  /// here: a conforming child answers exactly one response per command, so
  /// the stdio buffer is empty whenever this is called. Only a
  /// nonconforming child can batch responses ahead, and for those the
  /// resulting spurious timeout drops the child — exactly the intended
  /// outcome.
  std::optional<std::string> readResponseWithin(unsigned TimeoutMs) const;

  /// Best-effort non-blocking drain: read responses until none are pending
  /// within `TimeoutMs`. Used by resetImpl() to absorb solver-specific stray
  /// `success` lines emitted alongside the standard reset/option acks (e.g.
  /// mathsat acks `(echo)` itself, on top of the echoed content). Returns the
  /// number of responses drained.
  unsigned drainResponses(unsigned TimeoutMs) const;

  bool isOpen() const { return Out != nullptr; }

private:
  std::FILE *In = nullptr;  // read side: child's stdout
  std::FILE *Out = nullptr; // write side: child's stdin
  long Pid = -1;            // typed as long to avoid leaking <sys/types.h>
};

/// Tag type used to disambiguate the SMTLIBSolver constructor that spawns a
/// child solver process from the one that writes to a file.
struct SMTLIBProcessTag {};

/// Tag type for the one-shot constructor: serialize the whole script to a
/// file and run a shell command on it once (see the constructor docs).
struct SMTLIBOneShotTag {};

/// Invoked in the parent immediately after the one-shot child is spawned
/// and placed in its own process group, with the child's pgid. Lets the
/// caller register the group for teardown on signal/timeout exit paths
/// that skip destructors (a library destructor is not an equivalent
/// fallback: _exit() runs neither destructors nor atexit handlers, and a
/// one-shot solver may own a whole process subtree, e.g. an mpirun job).
using PgidCallback = std::function<void(long Pgid)>;

/// Strict verdict scanner for one-shot solver output, applied per line.
/// Accepts exactly the bare SMT-LIB verdicts (`sat`, `unsat`, `unknown`)
/// and the SAT-competition forms (`s SATISFIABLE`, `s UNSATISFIABLE`,
/// `s UNKNOWN`), with surrounding whitespace tolerated; `unknown` maps to
/// CheckResult::UNKNOWN. Everything else is rejected — deliberately no
/// substring matching, or a log line mentioning "unsat core" would become
/// a verification verdict.
std::optional<CheckResult> parseOneShotVerdictLine(const std::string &Line);

/// Facts about the last one-shot run, for the caller's diagnostics: the
/// command after %f substitution, a decoded exit status ("exit code N" /
/// "signal N"), and the last (up to) 20 lines of its stdout. Presentation
/// is the caller's job — Camada reports, the host logs.
struct OneShotDiagnostics {
  std::string Command;
  std::string ExitStatus;
  std::string OutputTail;
};

/// Camada backend that emits SMT-LIB instead of calling a native solver.
///
/// Two construction modes:
///
///   - Write-only: the script is appended to a file (or stdout if the
///     path is "-"). check() emits `(check-sat)` and returns UNKNOWN;
///     get* queries return UnsupportedOperation errors.
///
///   - Interactive: a child solver process is spawned via
///     `execvp(argv[0], argv)`. check() sends `(check-sat)` and reads
///     sat/unsat/unknown back. The interactive mode also accepts an
///     optional output path to log the same script to disk for offline
///     reproduction.
class SMTLIBSolver : public SMTSolverImpl {
public:
  /// Write-only constructor: write the emitted SMT-LIB script to OutputPath.
  /// Pass "-" for stdout. check() returns UNKNOWN; get* queries error.
  ///
  /// `Config` (all four constructors) carries the construction-frozen
  /// options — see SolverConfig. This backend consumes:
  ///   - Tuples: how tuples are lowered on the wire (TupleEncoding);
  ///   - Logic: overrides the emitted `(set-logic ...)`. Empty (the
  ///     default) keeps the built-in behaviour: `ALL`, with a one-shot
  ///     `QF_AUFBV` retry for interactive children that reject it. A
  ///     non-empty value is emitted verbatim and no negotiation is
  ///     attempted — the caller is asserting it knows what the child
  ///     accepts, and a child that rejects it is a fatal error, not a
  ///     retry (a one-shot model child is dropped instead);
  ///   - Arrays: the array encoding (ArrayEncoding). Ackermann mode keeps
  ///     the theory of arrays off the wire entirely and forces the Camada
  ///     tuple encoding;
  ///   - OneShotModelAckTimeoutMs: one-shot mode only, see below.
  explicit SMTLIBSolver(const std::string &OutputPath,
                        const SolverConfig &Config = {});

  /// Interactive constructor: spawn a child solver via
  /// `execvp(Argv[0], Argv)`. The solver must speak standard SMT-LIB on
  /// stdin/stdout (z3, cvc5, etc.). check() and get* queries round-trip
  /// through the child. No shell is involved — argv entries are passed
  /// verbatim, so spaces, quotes, and other metacharacters in any entry
  /// carry no special meaning.
  SMTLIBSolver(SMTLIBProcessTag, const std::vector<std::string> &Argv,
               const SolverConfig &Config = {});

  /// Combined constructor: spawn a child solver via execvp *and* log the
  /// script to a file. Useful when you want both an interactive answer
  /// and a reproducer to hand to another tool.
  SMTLIBSolver(SMTLIBProcessTag, const std::vector<std::string> &Argv,
               const std::string &OutputPath, const SolverConfig &Config = {});

  /// One-shot constructor: serialize the script (including `(check-sat)`)
  /// to FormulaPath, then run ShellCmd on it **via a shell** — every `%f`
  /// is replaced by the shell-quoted formula path, or the path is appended
  /// when no `%f` is present — scanning its stdout for a verdict with
  /// parseOneShotVerdictLine (each line trimmed, the last verdict wins).
  /// The child runs in its own process group; OnSpawn, when set, receives
  /// the pgid immediately after the spawn so the caller can register it
  /// for teardown on exit paths that skip destructors.
  ///
  /// When ModelArgv is non-empty, the same script is also streamed to that
  /// interactive solver (execvp, no shell), which starts solving in
  /// parallel at check() and serves get-value queries after a sat verdict;
  /// its own answer is available via oneShotModelVerdict() so the caller
  /// can detect a diverging model solver. A model solver that misbehaves
  /// in any way — dies, hangs, answers garbage, does not speak the
  /// `:print-success` ack protocol — is dropped silently (acks are read
  /// with a deadline, see OneShotModelAckTimeoutMs): the one-shot run
  /// remains the verdict source and only counterexample support is lost.
  ///
  /// check() may be called once; a second call aborts. On no verdict the
  /// result is UNKNOWN and oneShotDiagnostics() carries the evidence.
  ///
  /// SECURITY: unlike every other SMTLIBSolver mode, ShellCmd is executed
  /// by `$SHELL -c` (or `sh -c`) and must not be built from untrusted
  /// input. FormulaPath is shell-quoted; the template is not.
  SMTLIBSolver(SMTLIBOneShotTag, const std::string &FormulaPath,
               const std::string &ShellCmd,
               const std::vector<std::string> &ModelArgv = {},
               PgidCallback OnSpawn = {}, const SolverConfig &Config = {});

  /// One-shot mode: the model solver's own answer to the shared query,
  /// read only after a sat verdict from the one-shot run. Unset when no
  /// model solver was configured, it died, or the verdict was not sat.
  std::optional<CheckResult> oneShotModelVerdict() const {
    return OneShotModelVerdictValue;
  }

  /// One-shot mode: whether the interactive model solver is alive (it is
  /// dropped when it dies, when the verdict is not sat, or when its own
  /// answer was not sat).
  bool oneShotModelSolverLive() const { return Proc != nullptr; }

  /// One-shot mode: facts about the last run (command, exit status,
  /// output tail) for the caller's diagnostics.
  const OneShotDiagnostics &oneShotDiagnostics() const { return Diags; }

  ~SMTLIBSolver() override;

protected:
  void addConstraintImpl(const SMTExprRef &Exp) override;

  SMTExprRef rewrapExprImpl(const SMTExpr &Exp, const SMTSortRef &Sort,
                            SMTExprKind Kind) override;

  // --- sorts ---
  SMTSortRef mkBoolSortImpl() override;
  SMTSortRef mkBVSortImpl(unsigned BitWidth) override;
  SMTSortRef mkBVFPSortImpl(unsigned ExpWidth, unsigned SigWidth) override;
  SMTSortRef mkFXPSortImpl(unsigned Width, unsigned FracBits,
                           bool IsSigned) override;
  SMTSortRef mkBVRMSortImpl() override;
  SMTSortRef mkFPSortImpl(unsigned ExpWidth, unsigned SigWidth) override;
  SMTSortRef mkRMSortImpl() override;
  SMTSortRef mkIntSortImpl() override;
  SMTSortRef mkRealSortImpl() override;
  SMTSortRef mkArraySortImpl(const SMTSortRef &IndexSort,
                             const SMTSortRef &ElemSort) override;
  SMTSortRef mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                                const SMTSortRef &CodomainSort) override;
  SMTSortRef
  mkTupleSortImpl(const std::vector<SMTSortRef> &ElementSorts) override;

  // The Ackermann array mode forces the Camada tuple encoding: a native
  // datatype cannot hold an array member that has no backend term.
  bool nativeDatatypeSupport() const override { return true; }

  // --- expressions ---
  SMTExprRef mkBVNegImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkBVNotImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkNotImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkBVAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVSRemImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;
  SMTExprRef mkBVURemImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;
  SMTExprRef mkBVSDivImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;
  SMTExprRef mkBVUDivImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;
  SMTExprRef mkBVShlImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVAshrImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;
  SMTExprRef mkBVLshrImpl(const SMTExprRef &LHS,
                          const SMTExprRef &RHS) override;
  SMTExprRef mkBVXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVUltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVSltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVUleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkBVSleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkEqualImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                       const SMTExprRef &F) override;
  SMTExprRef mkBVSignExtImpl(const SMTExprRef &Exp,
                             unsigned ExtraBits) override;
  SMTExprRef mkBVZeroExtImpl(const SMTExprRef &Exp,
                             unsigned ExtraBits) override;
  SMTExprRef mkBVExtractImpl(unsigned High, unsigned Low,
                             const SMTExprRef &Exp) override;
  SMTExprRef mkBVConcatImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArraySelectImpl(const SMTExprRef &Array,
                               const SMTExprRef &Index) override;
  SMTExprRef mkArrayStoreImpl(const SMTExprRef &Array, const SMTExprRef &Index,
                              const SMTExprRef &Element) override;

  SMTExprRef mkBoolImpl(bool b) override;
  SMTExprRef mkBVFromDecImpl(int64_t Int, const SMTSortRef &Sort) override;
  SMTExprRef mkBVFromBinImpl(const std::string &Int,
                             const SMTSortRef &Sort) override;
  SMTExprRef mkSymbolImpl(const std::string &Name,
                          const SMTSortRef &Sort) override;
  SMTExprRef mkArrayConstImpl(const SMTSortRef &IndexSort,
                              const SMTExprRef &InitValue) override;

  // --- native FP literals + RM ---
  SMTExprRef mkFPFromBinImpl(const std::string &FP, unsigned EWidth) override;
  SMTExprRef mkRMImpl(const RM &R) override;
  SMTExprRef mkNaNImpl(bool Sgn, unsigned ExpWidth, unsigned SigWidth) override;
  SMTExprRef mkInfImpl(bool Sgn, unsigned ExpWidth, unsigned SigWidth) override;

  // --- native FP arithmetic + predicates ---
  SMTExprRef mkFPAbsImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkFPNegImpl(const SMTExprRef &Exp,
                         FPNegBehavior Behavior) override;
  SMTExprRef mkFPIsInfiniteImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkFPIsNaNImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkFPIsSubnormalImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkFPIsNormalImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkFPIsZeroImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const SMTExprRef &R) override;
  SMTExprRef mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const SMTExprRef &R) override;
  SMTExprRef mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const SMTExprRef &R) override;
  SMTExprRef mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                         const SMTExprRef &R) override;
  SMTExprRef mkFPSqrtImpl(const SMTExprRef &Exp, const SMTExprRef &R) override;
  SMTExprRef mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                         const SMTExprRef &Z, const SMTExprRef &R) override;
  SMTExprRef mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkFPGtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkFPGeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) override;
  SMTExprRef mkFPEqualImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkFPToFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                          const SMTExprRef &R) override;
  SMTExprRef mkSBVToFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                           const SMTExprRef &R) override;
  SMTExprRef mkUBVToFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                           const SMTExprRef &R) override;
  SMTExprRef mkFPToSBVImpl(const SMTExprRef &From, unsigned ToWidth) override;
  SMTExprRef mkFPToUBVImpl(const SMTExprRef &From, unsigned ToWidth) override;
  SMTExprRef mkFPToIntegralImpl(const SMTExprRef &From,
                                const SMTExprRef &R) override;
  SMTExprRef mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                              const SMTSortRef &To) override;
  SMTExprRef mkIEEEFPToBVImpl(const SMTExprRef &Exp) override;

  // --- Int / Real literals + arithmetic ---
  SMTExprRef mkIntImpl(int64_t v) override;
  SMTExprRef mkIntImpl(const std::string &v) override;
  SMTExprRef mkRealImpl(const std::string &v) override;
  SMTExprRef mkRealImpl(int64_t v) override;
  SMTExprRef mkRealImpl(int64_t num, int64_t den) override;
  SMTExprRef mkArithNegImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkArithAddImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithSubImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithMulImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithDivImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithModImpl(const SMTExprRef &LHS,
                            const SMTExprRef &RHS) override;
  SMTExprRef mkArithLtImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkArithGtImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkArithLeImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkArithGeImpl(const SMTExprRef &LHS,
                           const SMTExprRef &RHS) override;
  SMTExprRef mkInt2RealImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkReal2IntImpl(const SMTExprRef &Exp) override;
  SMTExprRef mkIsIntImpl(const SMTExprRef &Exp) override;

  // --- UF + quantifiers ---
  SMTExprRef mkApplyImpl(const SMTExprRef &Function,
                         const std::vector<SMTExprRef> &Args) override;
  SMTExprRef mkForallImpl(const std::vector<SMTExprRef> &Vars,
                          const SMTExprRef &Body) override;
  SMTExprRef mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                          const SMTExprRef &Body) override;

  // --- tuples (z3/cvc5 only via SMT-LIB declare-datatypes) ---
  SMTExprRef mkTupleImpl(const std::vector<SMTExprRef> &Elements) override;
  SMTExprRef mkTupleSelectImpl(const SMTExprRef &Tuple,
                               unsigned Index) override;

  // --- model queries: write-only mode aborts on these ---
  SMTResult<bool> getBoolImpl(const SMTExprRef &Exp) override;
  SMTResult<std::string> getBVInBinImpl(const SMTExprRef &Exp) override;
  SMTResult<std::string> getFPInBinImpl(const SMTExprRef &Exp) override;
  SMTResult<std::string> getIntImpl(const SMTExprRef &Exp) override;
  SMTResult<std::pair<std::string, std::string>>
  getRationalImpl(const SMTExprRef &Exp) override;
  SMTResult<SMTExprRef> getArrayElementImpl(const SMTExprRef &Array,
                                            const SMTExprRef &Index) override;

  // --- check / push / pop / reset ---
  CheckResult checkImpl() override;
  CheckResult
  checkSatAssumingImpl(const std::vector<SMTExprRef> &Assumptions) override;
  SMTResult<std::vector<SMTExprRef>> getUnsatAssumptionsImpl() override;

  bool timeoutSupport() const override { return false; }
  bool arrayModelSupport() const override { return false; }
  // Not the caller's request but what the child actually accepted: the
  // preamble already learned whether it took :produce-unsat-assumptions
  // (false in write-only mode, where there is no model to query either).
  //
  // The base's default bits describe what the emitter can put on the
  // wire; a given child may still reject a construct at runtime --
  // yices-smt2 has no FP, bitwuzla no Int/Real -- which is not knowable
  // here.
  bool unsatAssumptionSupport() const override {
    return UnsatAssumptionsSupported;
  }
  void resetImpl() override;
  void pushImpl(unsigned nscopes) override;
  void popImpl(unsigned nscopes) override;

  void dumpImpl(std::string &Out) override;
  void dumpModelImpl(std::string &Out) override;

  std::string getSolverNameAndVersion() const override;

public:
  /// Test-only: parse a `(get-value ...)` Int-typed model value into a
  /// signed decimal string. Exposed so unit tests can drive the parser
  /// against wire shapes (unreduced rationals, decimal-typed integers,
  /// etc.) without needing a child solver that emits exactly that
  /// shape. Returns the empty string on parse failure. Not part of the
  /// public Camada API.
  static std::string parseIntModelValueForTest(const std::string &Value);

private:
  // Build a terminal expression (symbol or literal) carrying its full text.
  SMTExprRef makeSMTLIBExpr(SMTExprKind Kind, const SMTSortRef &Sort,
                            std::string Text);

  // Build a compound expression from an operator head and its operands.
  SMTExprRef makeSMTLIBExpr(SMTExprKind Kind, const SMTSortRef &Sort,
                            std::string Head, std::vector<SMTExprRef> Args,
                            bool OwnScope = false);

  // Emit a single line (newline appended) to the active emitter(s).
  void emitLine(const std::string &Text);

  /// One-shot mode only: read one protocol ack from the auxiliary model
  /// solver, bounded by OneShotModelAckTimeoutMs. On timeout or EOF the
  /// child is dropped (Proc reset) and nullopt is returned; otherwise the
  /// reply is returned for the caller to judge. Callers that require
  /// `success` drop the child on anything else — an auxiliary child that
  /// misbehaves in any way costs counterexample support, never the run.
  std::optional<std::string> oneShotModelReply();

  // Emit a check command (a query: no `success` ack) and read the
  // sat/unsat/unknown verdict; UNKNOWN in write-only mode.
  CheckResult emitCheckCommand(const std::string &Cmd);

  // Send (get-value (Exp)) to the child solver and extract the value text
  // from its response. Fails in write-only mode (no child process). Resp
  // receives the raw response for use in error messages.
  SMTResult<std::string> sendGetValue(const SMTExprRef &Exp, std::string &Resp);

  // Emit the standard preamble (set-option, set-logic, set-info).
  void emitPreamble();

  // One-shot mode plumbing (see the SMTLIBOneShotTag constructor).
  CheckResult oneShotCheck();
  CheckResult runOneShotCommand();

  bool OneShotMode = false;
  bool OneShotCheckDone = false;
  std::string OneShotFormulaPath;
  std::string OneShotShellCmd;
  PgidCallback OneShotOnSpawn;
  std::optional<CheckResult> OneShotModelVerdictValue;
  OneShotDiagnostics Diags;

  std::unique_ptr<FileEmitter> File;
  std::unique_ptr<ProcessEmitter> Proc;

  // Counter for fresh tuple-sort names. mkTupleSortImpl declares a fresh
  // datatype per distinct tuple shape (Camada caches sort identity, so the
  // declaration runs at most once per shape).
  uint64_t NextTupleId = 0;

  // Counter for fresh symbols introduced by mkArrayConstImpl. mathsat's
  // SMT-LIB parser rejects `((as const ...))` inside `(get-value ...)`, so
  // we bind every const-array literal to a fresh symbol up front and
  // reference the symbol from then on.
  uint64_t NextArrConstId = 0;

  // Whether the child solver acknowledged
  // `(set-option :produce-unsat-assumptions true)` with `success`.
  // Children that answer `unsupported` (the standard reply for an
  // unimplemented option) still solve normally; only
  // getUnsatAssumptions() degrades to an error.
  bool UnsatAssumptionsSupported = false;

  // checkSatAssumingImpl assumes fresh activation literals
  // (`__CAMADA_assume_N`) instead of the caller's terms: the standard
  // restricts (check-sat-assuming ...) to property literals, and
  // (get-unsat-assumptions) echoes whatever was assumed, so minted
  // symbols make the response trivially and unambiguously decodable.
  // This maps each literal of the most recent call back to the
  // assumption it activates.
  uint64_t NextAssumeId = 0;
  std::vector<std::pair<std::string, SMTExprRef>> LastAssumptionLits;
};

} // namespace camada

#endif
