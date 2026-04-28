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

#include <cstdio>
#include <stdexcept>
#include <string>
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
// ProcessEmitter (Phase 2 stub)
// ---------------------------------------------------------------------------

ProcessEmitter::ProcessEmitter(const std::string & /*Cmd*/) {
  throw std::runtime_error(
      "SMTLIBSolver: ProcessEmitter is a Phase 2 feature and is not "
      "implemented yet");
}

ProcessEmitter::~ProcessEmitter() noexcept = default;

void ProcessEmitter::emitRaw(const std::string & /*Text*/) const {
  throw std::runtime_error("SMTLIBSolver: ProcessEmitter::emitRaw is a Phase 2 "
                           "feature and is not implemented yet");
}

void ProcessEmitter::flush() const {
  throw std::runtime_error("SMTLIBSolver: ProcessEmitter::flush is a Phase 2 "
                           "feature and is not implemented yet");
}

std::string ProcessEmitter::readResponse() const {
  throw std::runtime_error("SMTLIBSolver: ProcessEmitter::readResponse is a "
                           "Phase 2 feature and is not implemented yet");
}

bool ProcessEmitter::isOpen() const { return false; }

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

SMTLIBSolver::~SMTLIBSolver() { invalidateGeneratedObjects(); }

void SMTLIBSolver::emitPreamble() {
  emitLine("(set-option :print-success false)");
  emitLine("(set-option :global-declarations true)");
  emitLine("(set-info :status unknown)");
  emitLine("(set-logic ALL)");
}

void SMTLIBSolver::emitLine(const std::string &Text) const {
  if (File)
    File->emitRaw(Text + "\n");
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

SMTResult<bool> SMTLIBSolver::getBoolImpl(const SMTExprRef & /*Exp*/) {
  return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                  "SMTLIBSolver Phase 1 is write-only"};
}

SMTResult<std::string>
SMTLIBSolver::getBVInBinImpl(const SMTExprRef & /*Exp*/) {
  return SMTError{SMTErrorCode::UnsupportedOperation, SMTBackendKind::SMTLIB,
                  "SMTLIBSolver Phase 1 is write-only"};
}

SMTExprRef SMTLIBSolver::getArrayElementImpl(const SMTExprRef & /*Array*/,
                                             const SMTExprRef & /*Index*/) {
  unsupportedFeature("SMTLIBSolver Phase 1 is write-only");
}

checkResult SMTLIBSolver::checkImpl() {
  emitLine("(check-sat)");
  if (File)
    File->flush();
  // Phase 1 is write-only: there is no response to read. Return UNKNOWN so
  // callers that ignore the value still see something well-defined; callers
  // that rely on it should not be using Phase 1.
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
