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
/// Phase 2 only. Phase 1 ships this class as a stub — every method throws to
/// keep the API signatures stable while bodies are deferred.
class ProcessEmitter {
public:
  explicit ProcessEmitter(const std::string &Cmd);
  ProcessEmitter(const ProcessEmitter &) = delete;
  ProcessEmitter &operator=(const ProcessEmitter &) = delete;
  ~ProcessEmitter() noexcept;

  void emitRaw(const std::string &Text) const;
  void flush() const;
  std::string readResponse() const;

  bool isOpen() const;
};

/// Camada backend that emits SMT-LIB instead of calling a native solver.
///
/// Phase 1: write-only — the constructor takes an output path; check() and
/// model queries error out. There is no public createSMTLIBSolver() factory
/// in camada.h. Tests construct SMTLIBSolver directly.
class SMTLIBSolver : public SMTSolverImpl {
public:
  /// Phase 1 constructor: write the emitted SMT-LIB script to OutputPath.
  /// Pass "-" for stdout. The instance is write-only; check() and model
  /// queries will abort.
  explicit SMTLIBSolver(const std::string &OutputPath);

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
  SMTSortRef mkArraySortImpl(const SMTSortRef &IndexSort,
                             const SMTSortRef &ElemSort) override;

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

  // --- model queries: write-only mode aborts on these ---
  SMTResult<bool> getBoolImpl(const SMTExprRef &Exp) override;
  SMTResult<std::string> getBVInBinImpl(const SMTExprRef &Exp) override;
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

  // Counter for fresh let-bound names (?x0, ?x1, ...). Phase 1 does not
  // currently emit lets — the printer is straight-line — but the counter
  // is wired in so the let-binding visitor can be added without churning
  // the rest of the class.
  uint64_t NextLetId = 0;
};

} // namespace camada

#endif
