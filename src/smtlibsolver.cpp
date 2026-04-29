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

#include "smtlibsolver.h"
#include "camadacommon.h"

#include <algorithm>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <utility>
#include <vector>

namespace camada {

// ---------------------------------------------------------------------------
// SMTLIBSort / SMTLIBExpr
// ---------------------------------------------------------------------------

unsigned SMTLIBSort::getWidthFromSolver() const {
  // We do not have an external solver to consult; the stored width *is* the
  // truth. Return the stored payload directly. validateSortWidth() short-
  // circuits for array/function/tuple/arith sorts, so this method is only
  // ever called for kinds where getStoredWidth() succeeds (BV, FP, BVFP, RM,
  // BVRM, Bool). For FP sorts in particular the stored Width already reflects
  // the encoded representation; do not re-derive it from sig/exp here, since
  // BVFP stores SigWidth as the *encoded* significand width.
  return getStoredWidth();
}

void SMTLIBSort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTLIBSort::dump(std::string &Out) const {
  Out = Sort;
  Out += "\n";
}

bool SMTLIBExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return Expr == static_cast<const SMTLIBExpr &>(Other).Expr;
}

void SMTLIBExpr::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void SMTLIBExpr::dump(std::string &Out) const {
  Out = Expr;
  Out += "\n";
}

// ---------------------------------------------------------------------------
// FileEmitter
// ---------------------------------------------------------------------------

FileEmitter::FileEmitter(const std::string &Path) {
  if (Path.empty())
    return;
  if (Path == "-") {
    Out = stdout;
    OwnsHandle = false;
    return;
  }
  Out = std::fopen(Path.c_str(), "w");
  fatalErrorIf(Out == nullptr, "FileEmitter could not open output file");
  OwnsHandle = true;
}

FileEmitter::~FileEmitter() noexcept {
  if (Out && OwnsHandle)
    std::fclose(Out);
}

void FileEmitter::emitRaw(const std::string &Text) const {
  if (!Out)
    return;
  std::fwrite(Text.data(), 1, Text.size(), Out);
}

void FileEmitter::flush() const {
  if (Out)
    std::fflush(Out);
}

// ---------------------------------------------------------------------------
// ProcessEmitter
// ---------------------------------------------------------------------------

namespace {

// Read one SMT-LIB response from the given stream. Returns the text with
// surrounding whitespace trimmed. Handles three shapes:
//   - bare token line: `success`, `sat`, `unsat`, `unknown`, or numbers
//   - parenthesized: `((<symbol> <value>))` — read until parens balance,
//     respecting `|...|` quoted symbols and `"..."` string literals
//   - error: `(error "...")` — same parens-balanced shape
//
// Returns the empty string on EOF.
std::string readOneSmtlibResponse(std::FILE *In) {
  fatalErrorIf(!In, "ProcessEmitter::readResponse: stream is null");

  // Skip leading whitespace.
  int C;
  do {
    C = std::fgetc(In);
    if (C == EOF)
      return {};
  } while (C == ' ' || C == '\t' || C == '\n' || C == '\r');

  std::string Out;
  if (C != '(') {
    // Bare token: read until whitespace or EOF.
    Out.push_back(static_cast<char>(C));
    while ((C = std::fgetc(In)) != EOF && C != '\n' && C != '\r' && C != ' ' &&
           C != '\t')
      Out.push_back(static_cast<char>(C));
    return Out;
  }

  // Parenthesized: balance parens, with `|...|` and `"..."` awareness.
  Out.push_back('(');
  int Depth = 1;
  bool InQuoted = false; // inside |...|
  bool InString = false; // inside "..."
  while (Depth > 0) {
    C = std::fgetc(In);
    if (C == EOF)
      return Out; // child died mid-response; let the caller deal with it
    char Ch = static_cast<char>(C);
    Out.push_back(Ch);
    if (InQuoted) {
      if (Ch == '|')
        InQuoted = false;
      continue;
    }
    if (InString) {
      if (Ch == '"')
        InString = false;
      continue;
    }
    if (Ch == '|')
      InQuoted = true;
    else if (Ch == '"')
      InString = true;
    else if (Ch == '(')
      ++Depth;
    else if (Ch == ')')
      --Depth;
  }
  return Out;
}

} // namespace

ProcessEmitter::ProcessEmitter(const std::string &Cmd) {
  fatalErrorIf(Cmd.empty(),
               "SMTLIBSolver: ProcessEmitter requires a non-empty command");

  int InPipe[2];  // child stdout -> parent reads
  int OutPipe[2]; // parent writes -> child stdin
  fatalErrorIf(::pipe(InPipe) != 0, "ProcessEmitter: failed to open pipe");
  fatalErrorIf(::pipe(OutPipe) != 0, "ProcessEmitter: failed to open pipe");

  pid_t Child = ::fork();
  fatalErrorIf(Child < 0, "ProcessEmitter: fork() failed");

  if (Child == 0) {
    // Child: rewire stdin/stdout/stderr to the pipes and exec sh -c <Cmd>.
    ::close(OutPipe[1]);
    ::close(InPipe[0]);
    ::dup2(OutPipe[0], STDIN_FILENO);
    ::dup2(InPipe[1], STDOUT_FILENO);
    ::dup2(InPipe[1], STDERR_FILENO);
    ::close(OutPipe[0]);
    ::close(InPipe[1]);

    const char *Shell = std::getenv("SHELL");
    if (!Shell || !*Shell)
      Shell = "/bin/sh";
    ::execlp(Shell, Shell, "-c", Cmd.c_str(), static_cast<char *>(nullptr));
    // Reaching here means execlp failed.
    std::_Exit(127);
  }

  // Parent.
  ::close(OutPipe[0]);
  ::close(InPipe[1]);
  Out = ::fdopen(OutPipe[1], "w");
  In = ::fdopen(InPipe[0], "r");
  fatalErrorIf(Out == nullptr || In == nullptr,
               "ProcessEmitter: fdopen() failed on pipe ends");
  Pid = static_cast<long>(Child);

  // If the child dies, writes to its closed stdin would otherwise raise
  // SIGPIPE and kill us. Ignore the signal; we'll detect EOF on read.
  using Handler = void (*)(int);
  Handler Prev = std::signal(SIGPIPE, SIG_IGN);
  fatalErrorIf(Prev == SIG_ERR,
               "ProcessEmitter: failed to install SIGPIPE handler");
  OldSigpipeHandler = reinterpret_cast<void *>(Prev);
}

ProcessEmitter::~ProcessEmitter() noexcept {
  if (Out)
    std::fclose(Out);
  if (In)
    std::fclose(In);
  if (Pid > 0) {
    ::kill(static_cast<pid_t>(Pid), SIGTERM);
    int Status = 0;
    ::waitpid(static_cast<pid_t>(Pid), &Status, 0);
  }
  if (OldSigpipeHandler) {
    using Handler = void (*)(int);
    std::signal(SIGPIPE, reinterpret_cast<Handler>(OldSigpipeHandler));
  }
}

void ProcessEmitter::emitRaw(const std::string &Text) const {
  if (!Out)
    return;
  std::fwrite(Text.data(), 1, Text.size(), Out);
}

void ProcessEmitter::flush() const {
  if (Out)
    std::fflush(Out);
}

std::string ProcessEmitter::readResponse() const {
  return readOneSmtlibResponse(In);
}

// ---------------------------------------------------------------------------
// SMTLIBSolver
// ---------------------------------------------------------------------------

namespace {

// Helper: format an unsigned width into a decimal string.
std::string utoa(unsigned V) { return std::to_string(V); }

// Convert a Camada user-supplied symbol name into a quoted SMT-LIB symbol.
//
// We unconditionally wrap in vertical bars to side-step the SMT-LIB simple-
// symbol grammar (which forbids characters like `:` and `.` that ESBMC
// produces in names like `main::1::faces.a`).
//
// The two characters forbidden *inside* a `|...|` quoted symbol are `|` and
// `\`. We percent-encode them (and `%` itself, to keep the encoding
// reversible and collision-free): `|` -> `%7C`, `\` -> `%5C`, `%` -> `%25`.
// This guarantees every distinct Camada name maps to a distinct SMT-LIB
// symbol, so two different callers can never alias each other's
// declarations.
std::string quoteSymbol(const std::string &Name) {
  std::string Out;
  Out.reserve(Name.size() + 2);
  Out.push_back('|');
  for (char C : Name) {
    switch (C) {
    case '%':
      Out.append("%25");
      break;
    case '|':
      Out.append("%7C");
      break;
    case '\\':
      Out.append("%5C");
      break;
    default:
      Out.push_back(C);
      break;
    }
  }
  Out.push_back('|');
  return Out;
}

const std::string &textOf(const SMTExprRef &E) {
  return toSolverExpr<SMTLIBExpr>(*E).Expr;
}

const std::string &textOf(const SMTSortRef &S) {
  return toSolverSort<SMTLIBSort>(*S).Sort;
}

} // namespace

SMTLIBSolver::SMTLIBSolver(const std::string &OutputPath)
    : File(std::make_unique<FileEmitter>(OutputPath)) {
  emitPreamble();
  initializeCommonSingletons();
}

SMTLIBSolver::SMTLIBSolver(SMTLIBProcessTag, const std::string &Cmd)
    : Proc(std::make_unique<ProcessEmitter>(Cmd)) {
  emitPreamble();
  initializeCommonSingletons();
}

SMTLIBSolver::SMTLIBSolver(SMTLIBProcessTag, const std::string &Cmd,
                           const std::string &OutputPath)
    : File(std::make_unique<FileEmitter>(OutputPath)),
      Proc(std::make_unique<ProcessEmitter>(Cmd)) {
  emitPreamble();
  initializeCommonSingletons();
}

SMTLIBSolver::~SMTLIBSolver() { invalidateGeneratedObjects(); }

void SMTLIBSolver::emitPreamble() {
  // Interactive mode: the very first emitted command is
  // `(set-option :print-success true)`. Standard-conforming SMT-LIB solvers
  // (z3, cvc5) acknowledge that command itself with `success`, so emitLine's
  // ack-on-every-line regime works from the start. Write-only mode emits
  // `:print-success false` to keep captured scripts terse for offline replay.
  if (Proc)
    emitLine("(set-option :print-success true)");
  else if (File)
    File->emitRaw("(set-option :print-success false)\n");

  // cvc5 and bitwuzla refuse (get-value ...) unless model production is
  // explicitly enabled; z3 and yices-smt2 default to producing models. Set
  // the option unconditionally for protocol portability.
  emitLine("(set-option :produce-models true)");
  // Without :global-declarations true, declarations made inside a (push) are
  // discarded on (pop). Camada's API lets a caller mkSymbol() inside a pushed
  // scope and use the returned expression after pop(); without this option,
  // the next (assert ...) or (get-value ...) referring to that symbol would
  // hit "unknown constant" in the child solver. All solvers in the verified
  // matrix accept this option.
  emitLine("(set-option :global-declarations true)");
  emitLine("(set-info :status unknown)");
  // ALL covers BV/Bool/arrays/FP/Int/Real, which is everything Phase 3
  // exercises. Children that don't support a particular sort will reject the
  // first command that uses it (yices-smt2 has no FP, for example). Callers
  // who want a portable script across heterogeneous solvers should pick
  // FPEncoding::BV at sort-construction time — that already routes every FP
  // op through the common-layer bit-blast path.
  emitLine("(set-logic ALL)");
}

void SMTLIBSolver::emitLine(const std::string &Text) const {
  const std::string Line = Text + "\n";
  if (File)
    File->emitRaw(Line);
  if (Proc) {
    Proc->emitRaw(Line);
    Proc->flush();
    // Discard the `success` ack. If the child returned `(error "...")`, abort
    // with the message — there's no recovery from a malformed command in this
    // simple synchronous protocol.
    std::string Resp = Proc->readResponse();
    if (Resp != "success")
      fatalErrorIf(true,
                   ("SMTLIBSolver: child solver returned: " + Resp).c_str());
  }
}

SMTExprRef SMTLIBSolver::makeSMTLIBExpr(SMTExprKind Kind,
                                        const SMTSortRef &Sort,
                                        std::string Text) {
  return makeExprRef<SMTLIBExpr>(Kind, this, Sort, std::move(Text));
}

// --- core dispatch helpers ---

SMTExprRef SMTLIBSolver::newExprRefImpl(const SMTExpr &Exp) {
  const auto &E = toSolverExpr<SMTLIBExpr>(Exp);
  return makeExprRef<SMTLIBExpr>(Exp.getKind(), E.Context, Exp.Sort, E.Expr);
}

SMTExprRef SMTLIBSolver::rewrapExprImpl(const SMTExpr &Exp,
                                        const SMTSortRef &Sort,
                                        SMTExprKind Kind) {
  const auto &E = toSolverExpr<SMTLIBExpr>(Exp);
  return makeExprRef<SMTLIBExpr>(Kind, E.Context, Sort, E.Expr);
}

void SMTLIBSolver::addConstraintImpl(const SMTExprRef &Exp) {
  emitLine("(assert " + textOf(Exp) + ")");
}

// --- sorts ---

SMTSortRef SMTLIBSolver::mkBoolSortImpl() {
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::Bool, this, "Bool", SMTSort::ScalarSortData{1}));
}

SMTSortRef SMTLIBSolver::mkBVSortImpl(unsigned BitWidth) {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(SMTSortKind::BV, this,
                                            "(_ BitVec " + utoa(BitWidth) + ")",
                                            SMTSort::ScalarSortData{BitWidth}));
}

SMTSortRef SMTLIBSolver::mkBVFPSortImpl(unsigned ExpWidth, unsigned SigWidth) {
  unsigned Width = ExpWidth + SigWidth + 1;
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::BVFP, this, "(_ BitVec " + utoa(Width) + ")",
                 SMTSort::FPSortData{Width, ExpWidth, SigWidth + 1}));
}

SMTSortRef SMTLIBSolver::mkBVRMSortImpl() {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(
      SMTSortKind::BVRM, this, "(_ BitVec 3)", SMTSort::ScalarSortData{3}));
}

// Native FP. Camada's API takes SigWidth excluding the hidden bit (matches the
// CVC5 backend's convention: mkFPSortImpl(8, 23) → 32-bit FP). SMT-LIB's
// (_ FloatingPoint eb sb) counts the hidden bit, so we emit sb+1.
SMTSortRef SMTLIBSolver::mkFPSortImpl(unsigned ExpWidth, unsigned SigWidth) {
  unsigned Width = ExpWidth + SigWidth + 1;
  std::string Text =
      "(_ FloatingPoint " + utoa(ExpWidth) + " " + utoa(SigWidth + 1) + ")";
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::FP, this, std::move(Text),
                 SMTSort::FPSortData{Width, ExpWidth, SigWidth}));
}

SMTSortRef SMTLIBSolver::mkRMSortImpl() {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(
      SMTSortKind::RM, this, "RoundingMode", SMTSort::ScalarSortData{3}));
}

SMTSortRef SMTLIBSolver::mkIntSortImpl() {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(SMTSortKind::Int, this, "Int"));
}

SMTSortRef SMTLIBSolver::mkRealSortImpl() {
  return makeSortRef<SMTLIBSort>(SMTLIBSort(SMTSortKind::Real, this, "Real"));
}

// Function sort. SMT-LIB has no first-class function-sort syntax to put on
// the wire — function sorts only appear in (declare-fun name (D1 ...) Cod).
// We still need a SortRef the rest of Camada can carry around, so emit a
// placeholder text that is never spliced into wire output. mkSymbolImpl
// destructures the FunctionSortData when emitting the actual declaration.
SMTSortRef
SMTLIBSolver::mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                                 const SMTSortRef &CodomainSort) {
  std::string Text = "(";
  for (std::size_t I = 0; I < DomainSorts.size(); ++I) {
    if (I)
      Text += " ";
    Text += textOf(DomainSorts[I]);
  }
  Text += ") ";
  Text += textOf(CodomainSort);
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::Function, this, std::move(Text),
                 SMTSort::FunctionSortData{DomainSorts, CodomainSort}));
}

SMTSortRef SMTLIBSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                         const SMTSortRef &ElemSort) {
  std::string Text =
      "(Array " + textOf(IndexSort) + " " + textOf(ElemSort) + ")";
  return makeSortRef<SMTLIBSort>(
      SMTLIBSort(SMTSortKind::Array, this, std::move(Text),
                 SMTSort::ArraySortData{IndexSort, ElemSort}));
}

// --- straight-line expression builders ---

#define CAMADA_SMTLIB_UNARY(Name, OpName)                                      \
  SMTExprRef SMTLIBSolver::Name(const SMTExprRef &Exp) {                       \
    return makeSMTLIBExpr(SMTExprKind::OpName, Exp->Sort,                      \
                          "(" #OpName " " + textOf(Exp) + ")");                \
  }

#define CAMADA_SMTLIB_BINARY(Name, OpStr, Kind, ResultSort)                    \
  SMTExprRef SMTLIBSolver::Name(const SMTExprRef &LHS,                         \
                                const SMTExprRef &RHS) {                       \
    return makeSMTLIBExpr(SMTExprKind::Kind, ResultSort,                       \
                          "(" OpStr " " + textOf(LHS) + " " + textOf(RHS) +    \
                              ")");                                            \
  }

SMTExprRef SMTLIBSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::BVNeg, Exp->Sort,
                        "(bvneg " + textOf(Exp) + ")");
}
SMTExprRef SMTLIBSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::BVNot, Exp->Sort,
                        "(bvnot " + textOf(Exp) + ")");
}
SMTExprRef SMTLIBSolver::mkNotImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::Not, Exp->Sort,
                        "(not " + textOf(Exp) + ")");
}

CAMADA_SMTLIB_BINARY(mkBVAddImpl, "bvadd", BVAdd, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVSubImpl, "bvsub", BVSub, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVMulImpl, "bvmul", BVMul, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVSRemImpl, "bvsrem", BVSRem, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVURemImpl, "bvurem", BVURem, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVSDivImpl, "bvsdiv", BVSDiv, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVUDivImpl, "bvudiv", BVUDiv, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVShlImpl, "bvshl", BVShl, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVAshrImpl, "bvashr", BVAshr, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVLshrImpl, "bvlshr", BVLshr, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVXorImpl, "bvxor", BVXor, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVOrImpl, "bvor", BVOr, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVAndImpl, "bvand", BVAnd, LHS->Sort)
CAMADA_SMTLIB_BINARY(mkBVUltImpl, "bvult", BVUlt, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkBVSltImpl, "bvslt", BVSlt, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkBVUleImpl, "bvule", BVUle, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkBVSleImpl, "bvsle", BVSle, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkEqualImpl, "=", Equal, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkAndImpl, "and", And, mkBoolSort())
CAMADA_SMTLIB_BINARY(mkOrImpl, "or", Or, mkBoolSort())

#undef CAMADA_SMTLIB_UNARY
#undef CAMADA_SMTLIB_BINARY

SMTExprRef SMTLIBSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                   const SMTExprRef &F) {
  return makeSMTLIBExpr(SMTExprKind::Ite, T->Sort,
                        "(ite " + textOf(Cond) + " " + textOf(T) + " " +
                            textOf(F) + ")");
}

SMTExprRef SMTLIBSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  unsigned NewWidth = Exp->getWidth() + i;
  return makeSMTLIBExpr(SMTExprKind::BVSignExt, mkBVSort(NewWidth),
                        "((_ sign_extend " + utoa(i) + ") " + textOf(Exp) +
                            ")");
}

SMTExprRef SMTLIBSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  unsigned NewWidth = Exp->getWidth() + i;
  return makeSMTLIBExpr(SMTExprKind::BVZeroExt, mkBVSort(NewWidth),
                        "((_ zero_extend " + utoa(i) + ") " + textOf(Exp) +
                            ")");
}

SMTExprRef SMTLIBSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                         const SMTExprRef &Exp) {
  unsigned Width = High - Low + 1;
  return makeSMTLIBExpr(SMTExprKind::BVExtract, mkBVSort(Width),
                        "((_ extract " + utoa(High) + " " + utoa(Low) + ") " +
                            textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  unsigned Width = LHS->getWidth() + RHS->getWidth();
  return makeSMTLIBExpr(SMTExprKind::BVConcat, mkBVSort(Width),
                        "(concat " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                           const SMTExprRef &Index) {
  return makeSMTLIBExpr(SMTExprKind::ArraySelect, Array->Sort->getElementSort(),
                        "(select " + textOf(Array) + " " + textOf(Index) + ")");
}

SMTExprRef SMTLIBSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                          const SMTExprRef &Index,
                                          const SMTExprRef &Element) {
  return makeSMTLIBExpr(SMTExprKind::ArrayStore, Array->Sort,
                        "(store " + textOf(Array) + " " + textOf(Index) + " " +
                            textOf(Element) + ")");
}

// --- constants and symbols ---

SMTExprRef SMTLIBSolver::mkBoolImpl(bool b) {
  return makeSMTLIBExpr(SMTExprKind::BoolConst, mkBoolSort(),
                        b ? "true" : "false");
}

SMTExprRef SMTLIBSolver::mkBVFromDecImpl(int64_t Int, const SMTSortRef &Sort) {
  // Emit as a binary literal so we get correct two's-complement
  // sign-extension for widths > 64. The (_ bv<value> <width>) decimal form
  // would require big-integer arithmetic to handle that range, which we do
  // not have here. toTwosComplementBin handles all widths >= 1.
  const unsigned Width = Sort->getWidth();
  fatalErrorIf(Width == 0, "SMTLIBSolver: BV literal width must be non-zero");
  return makeSMTLIBExpr(SMTExprKind::BVConst, Sort,
                        "#b" + toTwosComplementBin(Int, Width));
}

SMTExprRef SMTLIBSolver::mkBVFromBinImpl(const std::string &Int,
                                         const SMTSortRef &Sort) {
  return makeSMTLIBExpr(SMTExprKind::BVConst, Sort, "#b" + Int);
}

SMTExprRef SMTLIBSolver::mkSymbolImpl(const std::string &Name,
                                      const SMTSortRef &Sort) {
  // Eagerly emit the declaration.
  std::string Quoted = quoteSymbol(Name);
  if (Sort->isFunctionSort()) {
    // (declare-fun f (D1 D2 ...) Codomain)
    std::string Decl = "(declare-fun " + Quoted + " (";
    const auto &Domain = Sort->getDomainSorts();
    for (std::size_t I = 0; I < Domain.size(); ++I) {
      if (I)
        Decl += " ";
      Decl += textOf(Domain[I]);
    }
    Decl += ") ";
    Decl += textOf(Sort->getCodomainSort());
    Decl += ")";
    emitLine(Decl);
  } else {
    emitLine("(declare-fun " + Quoted + " () " + textOf(Sort) + ")");
  }
  return makeSMTLIBExpr(SMTExprKind::Symbol, Sort, std::move(Quoted));
}

SMTExprRef SMTLIBSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                          const SMTExprRef &InitValue) {
  SMTSortRef Arr = mkArraySort(IndexSort, InitValue->Sort);
  return makeSMTLIBExpr(SMTExprKind::ArrayConst, Arr,
                        "((as const " + textOf(Arr) + ") " + textOf(InitValue) +
                            ")");
}

// --- native FP literals + RM ---

// Camada's mkFPFromBin convention: FP is the full IEEE-754 bit string
// (sign + exponent + trailing-significand-without-hidden-bit). For FP32 that's
// 32 bits with a 23-bit trailing significand. SMT-LIB's (fp #b<s> #b<e> #b<m>)
// takes the same three components — the hidden bit is implicit there too.
SMTExprRef SMTLIBSolver::mkFPFromBinImpl(const std::string &FP,
                                         unsigned EWidth) {
  fatalErrorIf(FP.size() <= 1 + EWidth,
               "SMTLIBSolver: FP literal too short for declared widths");
  // Camada's mkFPSort(eb, sb) takes the trailing significand width (no hidden
  // bit), matching the cvc5 backend convention. The FP string is exactly
  // `1 + EWidth + SigWidth` bits long, so SigWidth = FP.size() - 1 - EWidth.
  unsigned SigWidth = FP.size() - 1 - EWidth;
  SMTSortRef Sort = mkFPSort(EWidth, SigWidth, FPEncoding::Native);
  std::string Sign = FP.substr(0, 1);
  std::string Exp = FP.substr(1, EWidth);
  std::string Sig = FP.substr(1 + EWidth);
  std::string Text = "(fp #b" + Sign + " #b" + Exp + " #b" + Sig + ")";
  return makeSMTLIBExpr(SMTExprKind::FPConst, Sort, std::move(Text));
}

SMTExprRef SMTLIBSolver::mkRMImpl(const RM &R) {
  const char *Name = nullptr;
  switch (R) {
  case RM::ROUND_TO_EVEN:
    Name = "roundNearestTiesToEven";
    break;
  case RM::ROUND_TO_AWAY:
    Name = "roundNearestTiesToAway";
    break;
  case RM::ROUND_TO_PLUS_INF:
    Name = "roundTowardPositive";
    break;
  case RM::ROUND_TO_MINUS_INF:
    Name = "roundTowardNegative";
    break;
  case RM::ROUND_TO_ZERO:
    Name = "roundTowardZero";
    break;
  }
  fatalErrorIf(!Name, "SMTLIBSolver: unknown rounding mode");
  return makeSMTLIBExpr(SMTExprKind::RMConst, mkRMSort(FPEncoding::Native),
                        Name);
}

SMTExprRef SMTLIBSolver::mkNaNImpl(bool Sgn, unsigned ExpWidth,
                                   unsigned SigWidth) {
  // (_ NaN eb sb) — sb here includes the hidden bit. Camada's mkNaN passes
  // SigWidth already including the hidden bit.
  SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  std::string Text = "(_ NaN " + utoa(ExpWidth) + " " + utoa(SigWidth) + ")";
  // SMT-LIB has no signed-NaN literal — there is exactly one canonical NaN.
  // Callers that pass Sgn=true get the same value; that matches the cvc5 /
  // bitwuzla behavior (their NaN literals also ignore the sign).
  (void)Sgn;
  return makeSMTLIBExpr(SMTExprKind::FPConst, Sort, std::move(Text));
}

SMTExprRef SMTLIBSolver::mkInfImpl(bool Sgn, unsigned ExpWidth,
                                   unsigned SigWidth) {
  SMTSortRef Sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  std::string Text = std::string("(_ ") + (Sgn ? "-" : "+") + "oo " +
                     utoa(ExpWidth) + " " + utoa(SigWidth) + ")";
  return makeSMTLIBExpr(SMTExprKind::FPConst, Sort, std::move(Text));
}

// --- native FP arithmetic + predicates ---

SMTExprRef SMTLIBSolver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::FPAbs, Exp->Sort,
                        "(fp.abs " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkFPNegImpl(const SMTExprRef &Exp,
                                     FPNegBehavior Behavior) {
  // SMT-LIB's fp.neg has PreserveNaNPayload semantics — sign bit flipped on
  // non-NaNs, NaN payload preserved. That maps directly.
  if (Behavior == FPNegBehavior::PreserveNaNPayload)
    return makeSMTLIBExpr(SMTExprKind::FPNeg, Exp->Sort,
                          "(fp.neg " + textOf(Exp) + ")");

  // FlipSignBit must flip the top bit unconditionally, NaN included. SMT-LIB
  // has no direct op for that, so round-trip through the IEEE BV view: pull
  // the bits out, flip bit [N-1], reinterpret. mkIEEEFPToBV materializes a
  // fresh BV symbol constrained to Exp's bit pattern; mkBVToIEEEFP reads them
  // back as an FP value.
  unsigned Width =
      Exp->Sort->getFPExponentWidth() + Exp->Sort->getFPSignificandWidth() + 1;
  SMTExprRef Bits = mkIEEEFPToBV(Exp);
  SMTExprRef Sign = mkBVExtract(Width - 1, Width - 1, Bits);
  SMTExprRef Rest = mkBVExtract(Width - 2, 0, Bits);
  SMTExprRef Flipped = mkBVConcat(mkBVNot(Sign), Rest);
  return rewrapExprImpl(*mkBVToIEEEFP(Flipped, Exp->Sort), Exp->Sort,
                        SMTExprKind::FPNeg);
}

SMTExprRef SMTLIBSolver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::FPIsInfinite, mkBoolSort(),
                        "(fp.isInfinite " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::FPIsNaN, mkBoolSort(),
                        "(fp.isNaN " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::FPIsDenormal, mkBoolSort(),
                        "(fp.isSubnormal " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::FPIsNormal, mkBoolSort(),
                        "(fp.isNormal " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::FPIsZero, mkBoolSort(),
                        "(fp.isZero " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkFPMulImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS,
                                     const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPMul, LHS->Sort,
                        "(fp.mul " + textOf(R) + " " + textOf(LHS) + " " +
                            textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPDivImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS,
                                     const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPDiv, LHS->Sort,
                        "(fp.div " + textOf(R) + " " + textOf(LHS) + " " +
                            textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPRemImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::FPRem, LHS->Sort,
                        "(fp.rem " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPAddImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS,
                                     const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPAdd, LHS->Sort,
                        "(fp.add " + textOf(R) + " " + textOf(LHS) + " " +
                            textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPSubImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS,
                                     const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPSub, LHS->Sort,
                        "(fp.sub " + textOf(R) + " " + textOf(LHS) + " " +
                            textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPSqrtImpl(const SMTExprRef &Exp,
                                      const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPSqrt, Exp->Sort,
                        "(fp.sqrt " + textOf(R) + " " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                     const SMTExprRef &Z, const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPFMA, X->Sort,
                        "(fp.fma " + textOf(R) + " " + textOf(X) + " " +
                            textOf(Y) + " " + textOf(Z) + ")");
}

SMTExprRef SMTLIBSolver::mkFPLtImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::FPLt, mkBoolSort(),
                        "(fp.lt " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPGtImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::FPGt, mkBoolSort(),
                        "(fp.gt " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPLeImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::FPLe, mkBoolSort(),
                        "(fp.leq " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPGeImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::FPGe, mkBoolSort(),
                        "(fp.geq " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPEqualImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::FPEqual, mkBoolSort(),
                        "(fp.eq " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkFPtoFPImpl(const SMTExprRef &From,
                                      const SMTSortRef &To,
                                      const SMTExprRef &R) {
  std::string Text = "((_ to_fp " + utoa(To->getFPExponentWidth()) + " " +
                     utoa(To->getFPSignificandWidth() + 1) + ") " + textOf(R) +
                     " " + textOf(From) + ")";
  return makeSMTLIBExpr(SMTExprKind::FPtoFP, To, std::move(Text));
}

SMTExprRef SMTLIBSolver::mkSBVtoFPImpl(const SMTExprRef &From,
                                       const SMTSortRef &To,
                                       const SMTExprRef &R) {
  // Same opcode as fp→fp; SMT-LIB disambiguates by argument sort.
  std::string Text = "((_ to_fp " + utoa(To->getFPExponentWidth()) + " " +
                     utoa(To->getFPSignificandWidth() + 1) + ") " + textOf(R) +
                     " " + textOf(From) + ")";
  return makeSMTLIBExpr(SMTExprKind::SBVtoFP, To, std::move(Text));
}

SMTExprRef SMTLIBSolver::mkUBVtoFPImpl(const SMTExprRef &From,
                                       const SMTSortRef &To,
                                       const SMTExprRef &R) {
  std::string Text = "((_ to_fp_unsigned " + utoa(To->getFPExponentWidth()) +
                     " " + utoa(To->getFPSignificandWidth() + 1) + ") " +
                     textOf(R) + " " + textOf(From) + ")";
  return makeSMTLIBExpr(SMTExprKind::UBVtoFP, To, std::move(Text));
}

SMTExprRef SMTLIBSolver::mkFPtoSBVImpl(const SMTExprRef &From,
                                       unsigned ToWidth) {
  const SMTExprRef &R = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  std::string Text = "((_ fp.to_sbv " + utoa(ToWidth) + ") " + textOf(R) + " " +
                     textOf(From) + ")";
  return makeSMTLIBExpr(SMTExprKind::FPtoSBV, mkBVSort(ToWidth),
                        std::move(Text));
}

SMTExprRef SMTLIBSolver::mkFPtoUBVImpl(const SMTExprRef &From,
                                       unsigned ToWidth) {
  const SMTExprRef &R = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  std::string Text = "((_ fp.to_ubv " + utoa(ToWidth) + ") " + textOf(R) + " " +
                     textOf(From) + ")";
  return makeSMTLIBExpr(SMTExprKind::FPtoUBV, mkBVSort(ToWidth),
                        std::move(Text));
}

SMTExprRef SMTLIBSolver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                            const SMTExprRef &R) {
  return makeSMTLIBExpr(SMTExprKind::FPtoIntegral, From->Sort,
                        "(fp.roundToIntegral " + textOf(R) + " " +
                            textOf(From) + ")");
}

SMTExprRef SMTLIBSolver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                          const SMTSortRef &To) {
  // ((_ to_fp eb sb) bv) form (no rounding mode) reinterprets a same-width BV
  // as an IEEE FP.
  std::string Text = "((_ to_fp " + utoa(To->getFPExponentWidth()) + " " +
                     utoa(To->getFPSignificandWidth() + 1) + ") " +
                     textOf(Exp) + ")";
  return makeSMTLIBExpr(SMTExprKind::BVToIEEEFP, To, std::move(Text));
}

SMTExprRef SMTLIBSolver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  // Same trick as the cvc5 backend: SMT-LIB has no direct fp→bv that
  // preserves the IEEE bit pattern, so introduce a fresh BV symbol and tie it
  // back via the inverse direction.
  const std::string Name = "__CAMADA_ieeebv" + std::to_string(NextIEEEBVId++);
  SMTSortRef BVSort = mkBVSort(Exp->Sort->getFPExponentWidth() +
                               Exp->Sort->getFPSignificandWidth() + 1);
  SMTExprRef NewSymbol = mkSymbol(Name, BVSort);
  addConstraint(mkEqual(Exp, mkBVToIEEEFP(NewSymbol, Exp->Sort)));
  return NewSymbol;
}

// --- Int / Real literals + arithmetic ---

// Integer literals in SMT-LIB are written as bare numerals, with `(- N)` for
// negatives — there is no signed numeric token.
SMTExprRef SMTLIBSolver::mkIntImpl(int64_t v) {
  std::string Text;
  if (v < 0) {
    // Avoid overflow when negating INT64_MIN. Build the magnitude as an
    // unsigned and stringify, then wrap in (- ...).
    uint64_t Mag = static_cast<uint64_t>(-(v + 1)) + 1;
    Text = "(- " + std::to_string(Mag) + ")";
  } else {
    Text = std::to_string(v);
  }
  return makeSMTLIBExpr(SMTExprKind::IntConst, mkIntSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkIntImpl(const std::string &v) {
  // Caller passes a decimal string, possibly leading '-'. Wrap with (- ...)
  // for the negative case so the wire form is canonical SMT-LIB.
  if (!v.empty() && v[0] == '-')
    return makeSMTLIBExpr(SMTExprKind::IntConst, mkIntSort(),
                          "(- " + v.substr(1) + ")");
  return makeSMTLIBExpr(SMTExprKind::IntConst, mkIntSort(), v);
}

SMTExprRef SMTLIBSolver::mkRealImpl(const std::string &v) {
  // Real literals: the input may be a decimal ("3.14"), an integer ("7"), a
  // signed integer ("-7"), or a rational like "3/4". Normalize to the form
  // SMT-LIB accepts in expression position: bare decimals/integers, with
  // (- ...) for negatives and (/ p q) for rationals.
  if (v.empty())
    return makeSMTLIBExpr(SMTExprKind::RealConst, mkRealSort(), "0.0");
  std::string Body = v;
  bool Negative = false;
  if (Body[0] == '-') {
    Negative = true;
    Body = Body.substr(1);
  }
  std::string Text;
  std::size_t Slash = Body.find('/');
  if (Slash != std::string::npos)
    Text = "(/ " + Body.substr(0, Slash) + " " + Body.substr(Slash + 1) + ")";
  else
    Text = Body;
  if (Negative)
    Text = "(- " + Text + ")";
  return makeSMTLIBExpr(SMTExprKind::RealConst, mkRealSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkRealImpl(int64_t v) {
  // Reuse the int64-stringify path, but mark the result Real-sorted.
  std::string Text;
  if (v < 0) {
    uint64_t Mag = static_cast<uint64_t>(-(v + 1)) + 1;
    Text = "(- " + std::to_string(Mag) + ")";
  } else {
    Text = std::to_string(v);
  }
  return makeSMTLIBExpr(SMTExprKind::RealConst, mkRealSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkRealImpl(int64_t num, int64_t den) {
  std::string NumText;
  std::string DenText = std::to_string(den < 0 ? -den : den);
  bool Negative = (num < 0) ^ (den < 0);
  uint64_t NumMag = num < 0 ? static_cast<uint64_t>(-(num + 1)) + 1
                            : static_cast<uint64_t>(num);
  NumText = std::to_string(NumMag);
  std::string Text = "(/ " + NumText + " " + DenText + ")";
  if (Negative)
    Text = "(- " + Text + ")";
  return makeSMTLIBExpr(SMTExprKind::RealConst, mkRealSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkArithNegImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::ArithNeg, Exp->Sort,
                        "(- " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkArithAddImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithAdd, LHS->Sort,
                        "(+ " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArithSubImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithSub, LHS->Sort,
                        "(- " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArithMulImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithMul, LHS->Sort,
                        "(* " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArithDivImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  // SMT-LIB uses `div` for integer arithmetic and `/` for real arithmetic.
  // Camada dispatches on operand sort, so this method receives both kinds —
  // pick the right token based on the LHS sort.
  const char *Op = LHS->Sort->isIntSort() ? "div" : "/";
  return makeSMTLIBExpr(SMTExprKind::ArithDiv, LHS->Sort,
                        std::string("(") + Op + " " + textOf(LHS) + " " +
                            textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArithModImpl(const SMTExprRef &LHS,
                                        const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithMod, mkIntSort(),
                        "(mod " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArithLtImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithLt, mkBoolSort(),
                        "(< " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArithGtImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithGt, mkBoolSort(),
                        "(> " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArithLeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithLe, mkBoolSort(),
                        "(<= " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkArithGeImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeSMTLIBExpr(SMTExprKind::ArithGe, mkBoolSort(),
                        "(>= " + textOf(LHS) + " " + textOf(RHS) + ")");
}

SMTExprRef SMTLIBSolver::mkInt2RealImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::Int2Real, mkRealSort(),
                        "(to_real " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkReal2IntImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::Real2Int, mkIntSort(),
                        "(to_int " + textOf(Exp) + ")");
}

SMTExprRef SMTLIBSolver::mkIsIntImpl(const SMTExprRef &Exp) {
  return makeSMTLIBExpr(SMTExprKind::IsInt, mkBoolSort(),
                        "(is_int " + textOf(Exp) + ")");
}

// --- UF + quantifiers ---

// (FuncName arg1 arg2 ...). The Function expression's text already carries
// the function symbol name (set when the symbol was declared).
SMTExprRef SMTLIBSolver::mkApplyImpl(const SMTExprRef &Function,
                                     const std::vector<SMTExprRef> &Args) {
  std::string Text = "(" + textOf(Function);
  for (const auto &Arg : Args) {
    Text += " ";
    Text += textOf(Arg);
  }
  Text += ")";
  return makeSMTLIBExpr(SMTExprKind::Apply, Function->Sort->getCodomainSort(),
                        std::move(Text));
}

// Render a quantifier's bound-variable list `((v1 S1) (v2 S2) ...)`. Each var
// is a Symbol expression whose textOf() is the already-quoted variable name.
//
// Camada's regression tests pass quantifier vars that were created via
// mkSymbol — which means we already emitted `(declare-fun v () S)` at the
// global scope. The native backends silently accept this (Z3 ignores the
// redundant declaration; cvc5 shadows it inside the quantifier). The SMT-LIB
// pipeline mirrors that: the declaration was already emitted, we just
// reference the same name here in the binder list.
static std::string renderBinders(const std::vector<SMTExprRef> &Vars) {
  std::string Out;
  for (std::size_t I = 0; I < Vars.size(); ++I) {
    if (I)
      Out += " ";
    Out += "(";
    Out += static_cast<const SMTLIBExpr &>(*Vars[I]).Expr;
    Out += " ";
    Out += static_cast<const SMTLIBSort &>(*Vars[I]->Sort).Sort;
    Out += ")";
  }
  return Out;
}

SMTExprRef SMTLIBSolver::mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                      const SMTExprRef &Body) {
  std::string Text =
      "(forall (" + renderBinders(Vars) + ") " + textOf(Body) + ")";
  return makeSMTLIBExpr(SMTExprKind::Forall, mkBoolSort(), std::move(Text));
}

SMTExprRef SMTLIBSolver::mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                      const SMTExprRef &Body) {
  std::string Text =
      "(exists (" + renderBinders(Vars) + ") " + textOf(Body) + ")";
  return makeSMTLIBExpr(SMTExprKind::Exists, mkBoolSort(), std::move(Text));
}

// --- write-only model queries / check ---

namespace {

// Given a `(get-value (<term>))` response of the form `((<term> <value>))`,
// extract `<value>`. Returns the value sub-expression with surrounding
// whitespace trimmed.
//
// The response is normalized by readOneSmtlibResponse so it's a single
// balanced sexpr. We strip the outer `(( ... ))` wrapping, then strip the
// `<term>` prefix (everything up to the first top-level whitespace), then
// trim.
std::string extractValueFromGetValue(const std::string &Resp) {
  // Standard SMT-LIB `(get-value (<term>))` returns
  //   ( (<term> <value>) )
  // but solvers vary on whitespace: some emit `((x #b...))`, mathsat emits
  // `( (|x| (_ bv5 8)) )` with spaces inside the outer parens, etc. Walk the
  // string lexically rather than pattern-matching exact bracket positions.
  auto skipWS = [](const std::string &S, std::size_t I) {
    while (I < S.size() &&
           (S[I] == ' ' || S[I] == '\t' || S[I] == '\n' || S[I] == '\r'))
      ++I;
    return I;
  };
  std::size_t I = skipWS(Resp, 0);
  if (I >= Resp.size() || Resp[I] != '(')
    return {};
  ++I; // consume outer '('
  I = skipWS(Resp, I);
  if (I >= Resp.size() || Resp[I] != '(')
    return {};
  ++I; // consume inner '(' opening the valuation pair
  // Skip the <term>: walk until top-level whitespace, respecting `|...|`,
  // `"..."`, and nested parens.
  int Depth = 0;
  bool InQuoted = false;
  bool InString = false;
  while (I < Resp.size()) {
    char C = Resp[I];
    if (InQuoted) {
      if (C == '|')
        InQuoted = false;
    } else if (InString) {
      if (C == '"')
        InString = false;
    } else if (C == '|') {
      InQuoted = true;
    } else if (C == '"') {
      InString = true;
    } else if (C == '(') {
      ++Depth;
    } else if (C == ')') {
      if (Depth == 0)
        return {}; // pair closed before a value appeared
      --Depth;
    } else if (Depth == 0 &&
               (C == ' ' || C == '\t' || C == '\n' || C == '\r')) {
      break;
    }
    ++I;
  }
  I = skipWS(Resp, I);
  // Find the closing `)` of the valuation pair, respecting nested structure.
  std::size_t Start = I;
  Depth = 0;
  InQuoted = false;
  InString = false;
  while (I < Resp.size()) {
    char C = Resp[I];
    if (InQuoted) {
      if (C == '|')
        InQuoted = false;
    } else if (InString) {
      if (C == '"')
        InString = false;
    } else if (C == '|') {
      InQuoted = true;
    } else if (C == '"') {
      InString = true;
    } else if (C == '(') {
      ++Depth;
    } else if (C == ')') {
      if (Depth == 0)
        break; // this is the inner `)` closing the pair
      --Depth;
    }
    ++I;
  }
  // Trim trailing whitespace from the value.
  std::size_t End = I;
  while (End > Start && (Resp[End - 1] == ' ' || Resp[End - 1] == '\t' ||
                         Resp[End - 1] == '\n' || Resp[End - 1] == '\r'))
    --End;
  return Resp.substr(Start, End - Start);
}

// Convert an SMT-LIB BV value literal into a binary string (no `#b` prefix).
// Handles `#b...`, `#x...`, and `(_ bv<n> <w>)` forms. Returns empty on
// failure.
std::string bvValueToBinary(const std::string &Value, unsigned Width) {
  if (Value.size() >= 2 && Value[0] == '#' && Value[1] == 'b')
    return Value.substr(2);
  if (Value.size() >= 2 && Value[0] == '#' && Value[1] == 'x') {
    // Hex: each digit -> 4 bits.
    std::string Bits;
    Bits.reserve((Value.size() - 2) * 4);
    for (std::size_t I = 2; I < Value.size(); ++I) {
      char C = Value[I];
      int N = 0;
      if (C >= '0' && C <= '9')
        N = C - '0';
      else if (C >= 'a' && C <= 'f')
        N = 10 + (C - 'a');
      else if (C >= 'A' && C <= 'F')
        N = 10 + (C - 'A');
      else
        return {};
      for (int B = 3; B >= 0; --B)
        Bits.push_back(((N >> B) & 1) ? '1' : '0');
    }
    // Trim leading zeros to fit the expected width if needed.
    if (Bits.size() > Width)
      Bits = Bits.substr(Bits.size() - Width);
    while (Bits.size() < Width)
      Bits.insert(Bits.begin(), '0');
    return Bits;
  }
  // (_ bv<n> <w>): parse the decimal value and convert.
  if (Value.size() >= 5 && Value.substr(0, 5) == "(_ bv") {
    std::size_t Start = 5;
    std::size_t End = Value.find(' ', Start);
    if (End == std::string::npos)
      return {};
    std::string Decimal = Value.substr(Start, End - Start);
    if (Decimal.empty())
      return {};
    for (char C : Decimal)
      if (C < '0' || C > '9')
        return {};
    // Repeated long-division by 2 over the decimal string, reading the
    // remainders out from least to most significant. This works at any width
    // without pulling in big-integer libraries.
    std::vector<unsigned char> Digits(Decimal.size());
    for (std::size_t I = 0; I < Decimal.size(); ++I)
      Digits[I] = Decimal[I] - '0';
    std::string Bits;
    Bits.reserve(Width);
    while (true) {
      bool NonZero = false;
      unsigned Carry = 0;
      for (unsigned char &D : Digits) {
        unsigned Cur = Carry * 10 + D;
        D = Cur / 2;
        Carry = Cur % 2;
        if (D != 0)
          NonZero = true;
      }
      Bits.push_back(Carry ? '1' : '0');
      if (!NonZero)
        break;
    }
    if (Bits.size() > Width)
      Bits.resize(Width); // truncate high bits beyond declared width
    while (Bits.size() < Width)
      Bits.push_back('0');
    std::reverse(Bits.begin(), Bits.end());
    return Bits;
  }
  return {};
}

// Skip ASCII whitespace.
std::size_t skipWhitespace(const std::string &S, std::size_t I) {
  while (I < S.size() &&
         (S[I] == ' ' || S[I] == '\t' || S[I] == '\n' || S[I] == '\r'))
    ++I;
  return I;
}

// Parse a `#b<bits>` or `#x<hex>` token starting at `I`, append `Width` bits
// to `Out` (left-padded with zeros if the literal is shorter, truncated if
// longer). Returns the index just past the token, or std::string::npos on
// failure. Z3 emits some FP components as `#x80` instead of `#b10000000`, so
// the parser must handle both forms.
std::size_t parseBVLiteralAppend(const std::string &S, std::size_t I,
                                 unsigned Width, std::string &Out) {
  if (I + 1 >= S.size() || S[I] != '#')
    return std::string::npos;
  std::string Bits;
  if (S[I + 1] == 'b') {
    I += 2;
    while (I < S.size() && (S[I] == '0' || S[I] == '1'))
      Bits.push_back(S[I++]);
  } else if (S[I + 1] == 'x') {
    I += 2;
    while (I < S.size()) {
      char C = S[I];
      int N = 0;
      if (C >= '0' && C <= '9')
        N = C - '0';
      else if (C >= 'a' && C <= 'f')
        N = 10 + (C - 'a');
      else if (C >= 'A' && C <= 'F')
        N = 10 + (C - 'A');
      else
        break;
      for (int B = 3; B >= 0; --B)
        Bits.push_back(((N >> B) & 1) ? '1' : '0');
      ++I;
    }
  } else {
    return std::string::npos;
  }
  if (Bits.size() > Width)
    Bits = Bits.substr(Bits.size() - Width);
  while (Bits.size() < Width)
    Bits.insert(Bits.begin(), '0');
  Out += Bits;
  return I;
}

// Convert an SMT-LIB native FP value literal into an IEEE-754 binary string
// of width `ExpWidth + EncodedSigWidth + 1` (sign + exp + significand without
// hidden bit). Handles `(fp #b<s> #b<e> #b<m>)` and `(_ {+,-}oo {+,-}zero NaN
// eb sb)` forms. SigWidth here is the encoded width (already excludes the
// hidden bit). Returns empty on parse failure.
std::string fpValueToBinary(const std::string &Value, unsigned ExpWidth,
                            unsigned SigWidth) {
  // (fp #b<s> #b<e> #b<m>): concat the three operands. Z3 may emit any of the
  // three components in #x... hex form when its bit width is a multiple of 4
  // (e.g. an 8-bit exponent comes back as #x80, not #b10000000).
  if (Value.size() >= 4 && Value.substr(0, 4) == "(fp ") {
    std::size_t I = 4;
    std::string Out;
    I = skipWhitespace(Value, I);
    I = parseBVLiteralAppend(Value, I, 1, Out);
    if (I == std::string::npos)
      return {};
    I = skipWhitespace(Value, I);
    I = parseBVLiteralAppend(Value, I, ExpWidth, Out);
    if (I == std::string::npos)
      return {};
    I = skipWhitespace(Value, I);
    I = parseBVLiteralAppend(Value, I, SigWidth, Out);
    if (I == std::string::npos)
      return {};
    if (Out.size() != 1 + ExpWidth + SigWidth)
      return {};
    return Out;
  }
  // (_ +oo eb sb), (_ -oo eb sb), (_ +zero eb sb), (_ -zero eb sb),
  // (_ NaN eb sb). Total width = 1 + eb + (sb - 1) since sb in this notation
  // includes the hidden bit.
  if (Value.size() >= 3 && Value.substr(0, 3) == "(_ ") {
    std::size_t I = skipWhitespace(Value, 3);
    std::size_t WordStart = I;
    while (I < Value.size() && Value[I] != ' ' && Value[I] != ')')
      ++I;
    std::string Tag = Value.substr(WordStart, I - WordStart);
    bool Sign = false;
    bool IsZero = false;
    bool IsInf = false;
    bool IsNaN = false;
    if (Tag == "+oo") {
      Sign = false;
      IsInf = true;
    } else if (Tag == "-oo") {
      Sign = true;
      IsInf = true;
    } else if (Tag == "+zero") {
      Sign = false;
      IsZero = true;
    } else if (Tag == "-zero") {
      Sign = true;
      IsZero = true;
    } else if (Tag == "NaN") {
      IsNaN = true;
    } else {
      return {};
    }
    std::string Bits;
    Bits.push_back(Sign ? '1' : '0');
    if (IsZero) {
      Bits.append(ExpWidth, '0');
      Bits.append(SigWidth, '0');
    } else if (IsInf) {
      Bits.append(ExpWidth, '1');
      Bits.append(SigWidth, '0');
    } else if (IsNaN) {
      Bits.append(ExpWidth, '1');
      // Canonical NaN: top significand bit set, rest zero. (Camada's signed
      // NaN convention reads the sign bit as 0.)
      Bits.push_back('1');
      if (SigWidth >= 1)
        Bits.append(SigWidth - 1, '0');
    }
    return Bits;
  }
  return {};
}

// Trim ASCII whitespace from both ends of S.
std::string trimWS(const std::string &S) {
  std::size_t I = 0;
  std::size_t J = S.size();
  while (I < J && (S[I] == ' ' || S[I] == '\t' || S[I] == '\n' || S[I] == '\r'))
    ++I;
  while (J > I && (S[J - 1] == ' ' || S[J - 1] == '\t' || S[J - 1] == '\n' ||
                   S[J - 1] == '\r'))
    --J;
  return S.substr(I, J - I);
}

// Strip a `<number>.0...` decimal tail if the fractional part is all zeros,
// otherwise leave the string alone. This lets us treat z3's (/ 3.0 4.0) and
// cvc5's (/ 3 4) uniformly.
std::string normalizeNumeric(const std::string &S) {
  std::size_t Dot = S.find('.');
  if (Dot == std::string::npos)
    return S;
  for (std::size_t I = Dot + 1; I < S.size(); ++I)
    if (S[I] != '0')
      return S; // non-zero fractional digit; keep the original
  return S.substr(0, Dot);
}

// Convert a possibly-decimal numeric string into an integer / fraction pair.
// "3" → ("3", "1"), "3.0" → ("3", "1"), "0.5" → ("5", "10"),
// "1.25" → ("125", "100"). Returns false on any character outside [0-9.].
bool decimalToFraction(const std::string &S, std::string &Num,
                       std::string &Den) {
  if (S.empty())
    return false;
  std::size_t Dot = S.find('.');
  if (Dot == std::string::npos) {
    for (char C : S)
      if (C < '0' || C > '9')
        return false;
    Num = S;
    Den = "1";
    return true;
  }
  std::string Whole = S.substr(0, Dot);
  std::string Frac = S.substr(Dot + 1);
  for (char C : Whole)
    if (C < '0' || C > '9')
      return false;
  for (char C : Frac)
    if (C < '0' || C > '9')
      return false;
  Num = Whole + Frac;
  // Strip leading zeros from numerator (but keep "0").
  std::size_t Start = Num.find_first_not_of('0');
  if (Start == std::string::npos)
    Num = "0";
  else
    Num = Num.substr(Start);
  Den = "1" + std::string(Frac.size(), '0');
  return true;
}

// Parse an SMT-LIB integer model value into a signed decimal string.
// Accepted shapes: `N`, `(- N)` where N is a non-negative integer literal.
// Returns the empty string on failure.
std::string intValueToDecimal(const std::string &Value) {
  std::string V = trimWS(Value);
  // Negative form: `(- N)`.
  if (V.size() >= 4 && V[0] == '(' && V[1] == '-' && V[2] == ' ' &&
      V.back() == ')') {
    std::string Inner = trimWS(V.substr(3, V.size() - 4));
    for (char C : Inner)
      if (C < '0' || C > '9')
        return {};
    if (Inner.empty())
      return {};
    return "-" + Inner;
  }
  for (char C : V)
    if (C < '0' || C > '9')
      return {};
  return V.empty() ? std::string{} : V;
}

// Parse an SMT-LIB rational/real model value into a (numerator, denominator)
// pair of decimal strings. Both can be negative; the convention is that the
// numerator carries the sign and the denominator is non-negative.
//
// Accepted shapes:
//   N                       (integer)
//   (- N)                   (negative integer)
//   D                       (decimal: "3.14")
//   (- D)                   (negative decimal)
//   (/ p q)                 (rational; p and q are integer or decimal)
//   (- (/ p q))             (negative rational)
//   (/ (- p) q), (/ p (- q))  (rare but valid)
bool rationalValueToFraction(const std::string &Value, std::string &Num,
                             std::string &Den) {
  std::string V = trimWS(Value);
  // Strip a leading (- ...) negation, recurse, and flip the numerator sign.
  if (V.size() >= 4 && V[0] == '(' && V[1] == '-' && V[2] == ' ' &&
      V.back() == ')') {
    std::string Inner = trimWS(V.substr(3, V.size() - 4));
    if (!rationalValueToFraction(Inner, Num, Den))
      return false;
    if (!Num.empty() && Num[0] == '-')
      Num = Num.substr(1);
    else
      Num = "-" + Num;
    return true;
  }
  // (/ p q): parse p and q recursively as numerics.
  if (V.size() >= 4 && V.substr(0, 3) == "(/ " && V.back() == ')') {
    // Walk the body to split p and q at top-level whitespace.
    std::string Body = V.substr(3, V.size() - 4);
    int Depth = 0;
    std::size_t Split = std::string::npos;
    for (std::size_t I = 0; I < Body.size(); ++I) {
      if (Body[I] == '(')
        ++Depth;
      else if (Body[I] == ')')
        --Depth;
      else if (Depth == 0 &&
               (Body[I] == ' ' || Body[I] == '\t' || Body[I] == '\n')) {
        Split = I;
        break;
      }
    }
    if (Split == std::string::npos)
      return false;
    std::string P = trimWS(Body.substr(0, Split));
    std::string Q = trimWS(Body.substr(Split + 1));
    std::string PNum, PDen, QNum, QDen;
    if (!rationalValueToFraction(P, PNum, PDen))
      return false;
    if (!rationalValueToFraction(Q, QNum, QDen))
      return false;
    // (PNum/PDen) / (QNum/QDen) = (PNum*QDen) / (PDen*QNum). For the common
    // case where PDen and QDen are both "1" this collapses to PNum/QNum.
    if (PDen == "1" && QDen == "1") {
      Num = PNum;
      Den = QNum;
    } else {
      // Cross-multiplication on decimal strings would need a multi-precision
      // helper; we don't expect solvers to nest decimals inside (/ ...) in
      // practice, so flag the unhandled shape rather than approximating.
      return false;
    }
    // Move sign to numerator if it ended up on Den.
    if (!Den.empty() && Den[0] == '-') {
      Den = Den.substr(1);
      if (!Num.empty() && Num[0] == '-')
        Num = Num.substr(1);
      else
        Num = "-" + Num;
    }
    return true;
  }
  // Bare numeric (possibly decimal).
  std::string Norm = normalizeNumeric(V);
  return decimalToFraction(Norm, Num, Den);
}

} // namespace

SMTResult<bool> SMTLIBSolver::getBoolImpl(const SMTExprRef &Exp) {
  if (!Proc)
    return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver write-only mode does not support get*"};

  const std::string Cmd = "(get-value (" + textOf(Exp) + "))\n";
  if (File)
    File->emitRaw(Cmd);
  Proc->emitRaw(Cmd);
  Proc->flush();
  std::string Resp = Proc->readResponse();
  std::string Value = extractValueFromGetValue(Resp);
  if (Value == "true")
    return true;
  if (Value == "false")
    return false;
  return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                  "SMTLIBSolver: unexpected get-value response: " + Resp};
}

SMTResult<std::string> SMTLIBSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  if (!Proc)
    return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver write-only mode does not support get*"};

  const std::string Cmd = "(get-value (" + textOf(Exp) + "))\n";
  if (File)
    File->emitRaw(Cmd);
  Proc->emitRaw(Cmd);
  Proc->flush();
  std::string Resp = Proc->readResponse();
  std::string Value = extractValueFromGetValue(Resp);
  std::string Bits = bvValueToBinary(Value, Exp->getWidth());
  if (Bits.empty())
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: could not parse BV value: " + Resp};
  return Bits;
}

SMTResult<std::string> SMTLIBSolver::getFPInBinImpl(const SMTExprRef &Exp) {
  // For BV-encoded FP, the base-class default routes through getBVInBin and
  // works fine. This override is only reached for native FP sorts.
  if (!Proc)
    return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver write-only mode does not support get*"};

  const std::string Cmd = "(get-value (" + textOf(Exp) + "))\n";
  if (File)
    File->emitRaw(Cmd);
  Proc->emitRaw(Cmd);
  Proc->flush();
  std::string Resp = Proc->readResponse();
  std::string Value = extractValueFromGetValue(Resp);

  unsigned ExpWidth = Exp->Sort->getFPExponentWidth();
  unsigned SigWidth = Exp->Sort->getFPSignificandWidth(); // excludes hidden bit
  std::string Bits = fpValueToBinary(Value, ExpWidth, SigWidth);
  if (Bits.empty())
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: could not parse FP value: " + Resp};
  return Bits;
}

SMTResult<std::string> SMTLIBSolver::getIntImpl(const SMTExprRef &Exp) {
  if (!Proc)
    return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver write-only mode does not support get*"};

  const std::string Cmd = "(get-value (" + textOf(Exp) + "))\n";
  if (File)
    File->emitRaw(Cmd);
  Proc->emitRaw(Cmd);
  Proc->flush();
  std::string Resp = Proc->readResponse();
  std::string Value = extractValueFromGetValue(Resp);
  std::string Decimal = intValueToDecimal(Value);
  if (Decimal.empty())
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: could not parse Int value: " + Resp};
  return Decimal;
}

SMTResult<std::pair<std::string, std::string>>
SMTLIBSolver::getRationalImpl(const SMTExprRef &Exp) {
  if (!Proc)
    return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver write-only mode does not support get*"};

  const std::string Cmd = "(get-value (" + textOf(Exp) + "))\n";
  if (File)
    File->emitRaw(Cmd);
  Proc->emitRaw(Cmd);
  Proc->flush();
  std::string Resp = Proc->readResponse();
  std::string Value = extractValueFromGetValue(Resp);
  std::string Num, Den;
  if (!rationalValueToFraction(Value, Num, Den))
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::SMTLIB,
                    "SMTLIBSolver: could not parse Real value: " + Resp};
  return std::make_pair(Num, Den);
}

SMTExprRef SMTLIBSolver::getArrayElementImpl(const SMTExprRef &Array,
                                             const SMTExprRef &Index) {
  // The native backends evaluate (select Array Index) against their cached
  // model. Over the SMT-LIB pipe we don't have a cached model — but the
  // child solver does, so building a (select ...) expression and letting the
  // caller's subsequent get* call dispatch (get-value ((select ...))) gives
  // the same observable result.
  return mkArraySelect(Array, Index);
}

checkResult SMTLIBSolver::checkImpl() {
  // (check-sat) is a query — it does NOT produce a `success` ack even when
  // :print-success is true. Bypass emitLine's resync logic; write the
  // command directly and read the sat/unsat/unknown line ourselves.
  const std::string Cmd = "(check-sat)\n";
  if (File)
    File->emitRaw(Cmd);
  if (Proc) {
    Proc->emitRaw(Cmd);
    Proc->flush();
    std::string Resp = Proc->readResponse();
    if (Resp == "sat")
      return checkResult::SAT;
    if (Resp == "unsat")
      return checkResult::UNSAT;
    return checkResult::UNKNOWN;
  }
  // Write-only mode: no response to read.
  if (File)
    File->flush();
  return checkResult::UNKNOWN;
}

void SMTLIBSolver::resetImpl() {
  // (reset) is a non-uniform command: it clears every previously set option,
  // including :print-success. Solvers respond inconsistently:
  //   - z3: acks (reset) with `success`. set-option/get-info handled normally.
  //   - cvc5: NO ack for (reset).
  //   - yices: acks (reset) with `success`.
  //   - mathsat: acks (reset) AND emits a trailing `success` for each echo
  //     command, on top of the echoed content.
  //
  // Resync trick: send (reset) + (set-option :print-success true) +
  // (get-info :version), and read until we see the parenthesized version
  // response. Every leading `success` ack — from (reset), from (set-option) —
  // is silently discarded by the loop. (get-info) emits ONE distinguishable
  // response and no per-command ack on any of the four arith-capable
  // solvers in our matrix, so the buffer ends clean.
  //
  // Bitwuzla rejects (get-info). It's BV-only, so it's not in any test that
  // currently calls reset; if a caller does, the [error] response will be
  // surfaced to them rather than silently desyncing.
  if (File)
    File->emitRaw("(reset)\n");
  if (Proc) {
    Proc->emitRaw("(reset)\n");
    Proc->emitRaw("(set-option :print-success true)\n");
    Proc->emitRaw("(get-info :version)\n");
    Proc->flush();
    while (true) {
      std::string Resp = Proc->readResponse();
      fatalErrorIf(Resp.empty(),
                   "SMTLIBSolver: child solver closed the pipe during (reset)");
      // The version response always begins with `(:version` on a clean
      // protocol; the leading `success` lines from (reset) and (set-option)
      // are pure tokens and don't match.
      if (Resp.find(":version") != std::string::npos)
        break;
    }
  }
  emitPreamble();
}

void SMTLIBSolver::pushImpl(unsigned nscopes) {
  emitLine("(push " + std::to_string(nscopes) + ")");
}

void SMTLIBSolver::popImpl(unsigned nscopes) {
  emitLine("(pop " + std::to_string(nscopes) + ")");
}

void SMTLIBSolver::dumpImpl(std::string &Out) {
  Out = "SMTLIBSolver: dump-impl emits assertions to the configured stream.\n";
}

void SMTLIBSolver::dumpModelImpl(std::string &Out) {
  Out = "SMTLIBSolver Phase 1 is write-only; dumpModel unavailable.\n";
}

std::string SMTLIBSolver::getSolverNameAndVersion() const {
  return "SMTLIB write-only";
}

} // namespace camada
