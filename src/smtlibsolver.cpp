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

#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <utility>

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
  emitLine("(set-info :status unknown)");
  // Phase 2 only emits BV/Bool/arrays, so QF_AUFBV is the tightest fit and is
  // the broadest logic STP accepts. Phase 3 (FP/Int/Real) will need to revisit
  // — STP would drop out of the matrix at that point, since it is BV/arrays
  // only.
  emitLine("(set-logic QF_AUFBV)");
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
  emitLine("(declare-fun " + Quoted + " () " + textOf(Sort) + ")");
  return makeSMTLIBExpr(SMTExprKind::Symbol, Sort, std::move(Quoted));
}

SMTExprRef SMTLIBSolver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                          const SMTExprRef &InitValue) {
  SMTSortRef Arr = mkArraySort(IndexSort, InitValue->Sort);
  return makeSMTLIBExpr(SMTExprKind::ArrayConst, Arr,
                        "((as const " + textOf(Arr) + ") " + textOf(InitValue) +
                            ")");
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
    // Convert decimal to a Width-bit binary. We use a simple shift-and-add
    // approach without big-integer support — caps at 64 bits.
    if (Width > 64)
      return {};
    char *EndPtr = nullptr;
    unsigned long long N = std::strtoull(Decimal.c_str(), &EndPtr, 10);
    if (EndPtr == Decimal.c_str())
      return {};
    std::string Bits(Width, '0');
    for (unsigned I = 0; I < Width; ++I)
      Bits[Width - 1 - I] = ((N >> I) & 1ULL) ? '1' : '0';
    return Bits;
  }
  return {};
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

SMTExprRef SMTLIBSolver::getArrayElementImpl(const SMTExprRef & /*Array*/,
                                             const SMTExprRef & /*Index*/) {
  unsupportedFeature("SMTLIBSolver array model parsing (Phase 3)");
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
  emitLine("(reset)");
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
