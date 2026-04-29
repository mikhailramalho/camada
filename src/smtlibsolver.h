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
#include <memory>
#include <string>

#include "camadaexpr.h"
#include "camadaimpl.h"
#include "camadasort.h"

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

  void dump() const override;
  void dump(std::string &Out) const override;
};

/// SMT-LIB expression. The "native" representation is the SMT-LIB text for
/// the expression — either inline like "(bvadd a b)" or, after let-binding,
/// a temporary symbol name like "?x3".
class SMTLIBExpr : public SolverExpr<SMTLIBContextRef, std::string> {
public:
  static constexpr SMTBackendKind BackendKindValue = SMTBackendKind::SMTLIB;
  using SolverExpr<SMTLIBContextRef, std::string>::SolverExpr;
  ~SMTLIBExpr() override = default;

  SMTBackendKind getBackendKind() const override { return BackendKindValue; }

  bool equal_to(SMTExpr const &Other) const override;

  void dump() const override;
  void dump(std::string &Out) const override;
};

/// Emits SMT-LIB output to a file (or stdout if path is "-").
///
/// Phase 1: this is the only emitter used; SMTLIBSolver constructed with a
/// FileEmitter is purely write-only. Phase 2 will add ProcessEmitter and
/// allow both to be active simultaneously (script + interactive solving).
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
/// Spawns the child via `sh -c <cmd>`, so callers can pass shell-friendly
/// commands like `z3 -in` or `cvc5 --lang smt2`. The constructor sends
/// `(set-option :print-success true)` at startup so every non-query command
/// produces a `success`/`error` response, which gives a deterministic way to
/// resynchronize with the child after each emitted line.
class ProcessEmitter {
public:
  explicit ProcessEmitter(const std::string &Cmd);
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

  bool isOpen() const { return Out != nullptr; }

private:
  std::FILE *In = nullptr;  // read side: child's stdout
  std::FILE *Out = nullptr; // write side: child's stdin
  long Pid = -1;            // typed as long to avoid leaking <sys/types.h>
  void *OldSigpipeHandler = nullptr;
};

/// Tag type used to disambiguate the SMTLIBSolver constructor that spawns a
/// child solver process from the one that writes to a file.
struct SMTLIBProcessTag {};

/// Camada backend that emits SMT-LIB instead of calling a native solver.
///
/// Two construction modes:
///
///   - Write-only (Phase 1): the script is appended to a file (or stdout if
///     the path is "-"). check() emits `(check-sat)` and returns UNKNOWN;
///     get* queries return UnsupportedOperation errors.
///
///   - Interactive (Phase 2): a child solver process is spawned via
///     `sh -c <cmd>`. check() sends `(check-sat)` and reads sat/unsat/unknown
///     back. The interactive mode also supports an optional output path to
///     log the same script to disk for offline reproduction.
class SMTLIBSolver : public SMTSolverImpl {
public:
  /// Write-only constructor: write the emitted SMT-LIB script to OutputPath.
  /// Pass "-" for stdout. check() returns UNKNOWN; get* queries error.
  explicit SMTLIBSolver(const std::string &OutputPath);

  /// Interactive constructor: spawn a child solver via `sh -c <Cmd>`. The
  /// solver must speak standard SMT-LIB on stdin/stdout (z3, cvc5, etc.).
  /// check() and get* queries round-trip through the child.
  SMTLIBSolver(SMTLIBProcessTag, const std::string &Cmd);

  /// Combined constructor: spawn a child solver *and* log the script to a
  /// file. Useful when you want both an interactive answer and a reproducer
  /// to hand to another tool.
  SMTLIBSolver(SMTLIBProcessTag, const std::string &Cmd,
               const std::string &OutputPath);

  ~SMTLIBSolver() override;

protected:
  void addConstraintImpl(const SMTExprRef &Exp) override;

  SMTExprRef newExprRefImpl(const SMTExpr &Exp) override;
  SMTExprRef rewrapExprImpl(const SMTExpr &Exp, const SMTSortRef &Sort,
                            SMTExprKind Kind) override;

  // --- sorts ---
  SMTSortRef mkBoolSortImpl() override;
  SMTSortRef mkBVSortImpl(unsigned BitWidth) override;
  SMTSortRef mkBVFPSortImpl(unsigned ExpWidth, unsigned SigWidth) override;
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

  // --- expressions: bare minimum for the Phase 1 smoke test ---
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
  SMTExprRef mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) override;
  SMTExprRef mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) override;
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
  SMTExprRef mkFPIsDenormalImpl(const SMTExprRef &Exp) override;
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
  SMTExprRef mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                          const SMTExprRef &R) override;
  SMTExprRef mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                           const SMTExprRef &R) override;
  SMTExprRef mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                           const SMTExprRef &R) override;
  SMTExprRef mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth) override;
  SMTExprRef mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth) override;
  SMTExprRef mkFPtoIntegralImpl(const SMTExprRef &From,
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
  SMTExprRef getArrayElementImpl(const SMTExprRef &Array,
                                 const SMTExprRef &Index) override;

  // --- check / push / pop / reset ---
  checkResult checkImpl() override;
  void resetImpl() override;
  void pushImpl(unsigned nscopes) override;
  void popImpl(unsigned nscopes) override;

  void dumpImpl(std::string &Out) override;
  void dumpModelImpl(std::string &Out) override;

  std::string getSolverNameAndVersion() const override;

private:
  // Build a bare expression carrying the given SMT-LIB text.
  SMTExprRef makeSMTLIBExpr(SMTExprKind Kind, const SMTSortRef &Sort,
                            std::string Text);

  // Emit a single line (newline appended) to the active emitter(s).
  void emitLine(const std::string &Text) const;

  // Emit the standard preamble (set-option, set-logic, set-info).
  void emitPreamble();

  std::unique_ptr<FileEmitter> File;
  std::unique_ptr<ProcessEmitter> Proc;

  // Counter for fresh let-bound names (?x0, ?x1, ...). Phase 1 does not
  // currently emit lets — the printer is straight-line — but the counter
  // is wired in so the let-binding visitor can be added without churning
  // the rest of the class.
  uint64_t NextLetId = 0;

  // Counter for fresh symbols introduced by mkIEEEFPToBVImpl. SMT-LIB has no
  // direct fp→bv same-encoding op, so we materialize a fresh BV symbol and
  // constrain it via the inverse fp.from-IEEE-bv direction.
  uint64_t NextIEEEBVId = 0;

  // Counter for fresh tuple-sort names. mkTupleSortImpl declares a fresh
  // datatype per distinct tuple shape (Camada caches sort identity, so the
  // declaration runs at most once per shape).
  uint64_t NextTupleId = 0;
};

} // namespace camada

#endif
