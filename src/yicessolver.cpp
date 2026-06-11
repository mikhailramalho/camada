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

#if SOLVER_YICES_ENABLED

#include "yicessolver.h"
#include "camada.h"
#include "camadacommon.h"

#include <cstdio>
#include <gmp.h>
#include <mutex>
#include <utility>
#include <vector>

#if !defined(_WIN32)
#include <atomic>
#include <csignal>
#include <sys/time.h>
#endif
#include <yices.h>

namespace camada {

#if !defined(_WIN32)
namespace {
// Yices has no native time limit; the documented interruption mechanism is
// calling yices_stop_search from a signal handler (the same pattern
// smt-switch uses). The solver running the current check parks its context
// here for the handler. The timer, handler slot, and this context are all
// process-global, so at most one Yices check may run under a time limit at
// a time process-wide: concurrent timed checks on Yices instances in
// different threads would clobber each other's timer and deadline.
std::atomic<context_t *> YicesSearchContext{nullptr};
struct sigaction YicesOldAlarmAction = {};

void yicesAlarmHandler(int) {
  if (context_t *Ctx = YicesSearchContext.load())
    yices_stop_search(Ctx);
}
} // namespace
#endif

namespace {

std::mutex &yicesLifecycleMutex() {
  static std::mutex Mutex;
  return Mutex;
}

unsigned &yicesLifecycleRefCount() {
  static unsigned RefCount = 0;
  return RefCount;
}

void acquireYicesLibrary() {
  std::lock_guard<std::mutex> Lock(yicesLifecycleMutex());
  unsigned &RefCount = yicesLifecycleRefCount();
  if (RefCount++ == 0)
    yices_init();
  yices_clear_error();
}

void releaseYicesLibrary() {
  std::lock_guard<std::mutex> Lock(yicesLifecycleMutex());
  unsigned &RefCount = yicesLifecycleRefCount();
  assert(RefCount && "Yices lifecycle refcount underflow");
  if (--RefCount == 0)
    yices_exit();
}

static inline void yicesCheckError(int32_t Res, const char *Message) {
  if (Res == 0)
    return;

  char *Err = yices_error_string();
  if (Err == nullptr)
    fatalError(Message);

  std::string FullMessage = std::string(Message) + ": " + Err;
  yices_free_string(Err);
  fatalError(FullMessage.c_str());
}

static inline context_t *yicesCheckContext(context_t *Ctx,
                                           const char *Message) {
  if (Ctx != nullptr)
    return Ctx;

  yicesCheckError(-1, Message);
  return nullptr;
}

static inline term_t yicesCheckTerm(term_t Term, const char *Message) {
  if (Term != NULL_TERM)
    return Term;

  yicesCheckError(-1, Message);
  return NULL_TERM;
}

} // namespace

unsigned YicesSort::getWidthFromSolver() const {
  if (yices_type_is_bool(Sort))
    return 1;

  if (yices_type_is_int(Sort) || yices_type_is_real(Sort))
    return 0;

  assert(yices_type_is_bitvector(Sort));
  return yices_bvtype_size(Sort);
}

void YicesSort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void YicesSort::dump(std::string &Out) const {
  char *ty_str = yices_type_to_string(Sort, 160, 80, 0);
  Out = ty_str;
  Out += "\n";
  yices_free_string(ty_str);
}

bool YicesExpr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return (Expr == static_cast<const YicesExpr &>(Other).Expr);
}

void YicesExpr::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void YicesExpr::dump(std::string &Out) const {
  char *term_str = yices_term_to_string(Expr, 160, 80, 0);
  Out = term_str;
  Out += "\n";
  yices_free_string(term_str);
}

YicesSolver::YicesSolver() {
  acquireYicesLibrary();
  recreateContext("QF_AUFBV");
  initializeCommonSingletons();
}

YicesSolver::~YicesSolver() {
  invalidateGeneratedObjects();
  destroyContext();
  releaseYicesLibrary();
}

void YicesSolver::destroyContext() {
  releaseSymbolNames();
  if (Context)
    yices_free_context(Context);
  Context = nullptr;
}

void YicesSolver::releaseSymbolNames() {
  for (const auto &Name : NamedSymbols)
    yices_remove_term_name(Name.c_str());
  NamedSymbols.clear();
}

void YicesSolver::recreateContext(const char *Logic) {
  recreateContextWithConfig(Logic, nullptr);
}

void YicesSolver::recreateContextWithConfig(const char *Logic,
                                            void (*Configure)(ctx_config_t *)) {
  destroyContext();
  yices_clear_error();

  ctx_config_t *config = yices_new_config();
  yices_default_config_for_logic(config, Logic);
  if (Configure)
    Configure(config);
  // The context mode is owned by Camada, deliberately after the Configure
  // callback: push()/pop() need at least push-pop mode, and "interactive"
  // additionally restores the context automatically when a search is
  // interrupted (yices_stop_search) — how setTimeout() is enforced here.
  // Any weaker mode leaves an interrupted context in
  // YICES_STATUS_INTERRUPTED permanently: later checks return STATUS_ERROR
  // (mapped to instant UNKNOWN), asserts fail, and push aborts.
  yicesCheckError(yices_set_config(config, "mode", "interactive"),
                  "Could not configure Yices interactive mode");

  Context = yicesCheckContext(yices_new_context(config),
                              "Could not create Yices context");
  yices_free_config(config);
}

void YicesSolver::addConstraintImpl(const SMTExprRef &Exp) {
  Assertions.push_back(Exp);
  // Checked so a bad context state can never silently drop a constraint.
  yicesCheckError(
      yices_assert_formula(Context, toSolverExpr<YicesExpr>(*Exp).Expr),
      "Could not assert formula in Yices context");
}

SMTExprRef YicesSolver::rewrapExprImpl(const SMTExpr &Exp,
                                       const SMTSortRef &Sort,
                                       SMTExprKind Kind) {
  const auto &Wrapped = toSolverExpr<YicesExpr>(Exp);
  yicesCheckTerm(Wrapped.Expr, "Error when creating Yices expr");
  return makeExprRef<YicesExpr>(Kind, Wrapped.Context, Sort, Wrapped.Expr);
}

SMTSortRef YicesSolver::mkBoolSortImpl() {
  return makeSortRef<YicesSort>(YicesSort(SMTSortKind::Bool, Context,
                                          yices_bool_type(),
                                          SMTSort::ScalarSortData{1}));
}

SMTSortRef YicesSolver::mkIntSortImpl() {
  return makeSortRef<YicesSort>(
      YicesSort(SMTSortKind::Int, Context, yices_int_type()));
}

SMTSortRef YicesSolver::mkRealSortImpl() {
  return makeSortRef<YicesSort>(
      YicesSort(SMTSortKind::Real, Context, yices_real_type()));
}

SMTSortRef YicesSolver::mkBVSortImpl(unsigned BitWidth) {
  return makeSortRef<YicesSort>(YicesSort(SMTSortKind::BV, Context,
                                          yices_bv_type(BitWidth),
                                          SMTSort::ScalarSortData{BitWidth}));
}

SMTSortRef YicesSolver::mkBVFPSortImpl(const unsigned ExpWidth,
                                       const unsigned SigWidth) {
  return makeSortRef<YicesSort>(YicesSort(
      SMTSortKind::BVFP, Context, yices_bv_type(ExpWidth + SigWidth + 1),
      SMTSort::FPSortData{ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1}));
}

SMTSortRef YicesSolver::mkBVRMSortImpl() {
  return makeSortRef<YicesSort>(YicesSort(SMTSortKind::BVRM, Context,
                                          yices_bv_type(3),
                                          SMTSort::ScalarSortData{3}));
}

SMTSortRef YicesSolver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                        const SMTSortRef &ElemSort) {
  return makeSortRef<YicesSort>(
      YicesSort(SMTSortKind::Array, Context,
                yices_function_type1(toSolverSort<YicesSort>(*IndexSort).Sort,
                                     toSolverSort<YicesSort>(*ElemSort).Sort),
                SMTSort::ArraySortData{IndexSort, ElemSort}));
}

SMTSortRef
YicesSolver::mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                                const SMTSortRef &CodomainSort) {
  std::vector<type_t> Domain;
  Domain.reserve(DomainSorts.size());
  for (const auto &Sort : DomainSorts)
    Domain.push_back(toSolverSort<YicesSort>(*Sort).Sort);
  return makeSortRef<YicesSort>(YicesSort(
      SMTSortKind::Function, Context,
      yices_function_type(Domain.size(), Domain.data(),
                          toSolverSort<YicesSort>(*CodomainSort).Sort),
      SMTSort::FunctionSortData{DomainSorts, CodomainSort}));
}

SMTExprRef YicesSolver::mkBVNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVNeg, Context, Exp->Sort,
      yices_bvneg(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkBVNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVNot, Context, Exp->Sort,
      yices_bvnot(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(SMTExprKind::Not, Context, Exp->Sort,
                                yices_not(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkArithNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithNeg, Context, Exp->Sort,
                                yices_neg(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkReal2IntImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::Real2Int, Context, mkIntSort(),
      yices_floor(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkIsIntImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::IsInt, Context, mkBoolSort(),
      yices_is_int_atom(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkBVAddImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVAdd, Context, LHS->Sort,
      yices_bvadd(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSubImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSub, Context, LHS->Sort,
      yices_bvsub(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVMulImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVMul, Context, LHS->Sort,
      yices_bvmul(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSRemImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSRem, Context, LHS->Sort,
      yices_bvsrem(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVURemImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVURem, Context, LHS->Sort,
      yices_bvrem(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSDivImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSDiv, Context, LHS->Sort,
      yices_bvsdiv(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUDivImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUDiv, Context, LHS->Sort,
      yices_bvdiv(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVShlImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVShl, Context, LHS->Sort,
      yices_bvshl(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVAshrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVAshr, Context, LHS->Sort,
      yices_bvashr(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVLshrImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVLshr, Context, LHS->Sort,
      yices_bvlshr(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVXorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVXor, Context, LHS->Sort,
      yices_bvxor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVOrImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVOr, Context, LHS->Sort,
      yices_bvor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVAndImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVAnd, Context, LHS->Sort,
      yices_bvand2(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVXnorImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVXnor, Context, LHS->Sort,
      yices_bvxnor(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVNorImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVNor, Context, LHS->Sort,
      yices_bvnor(toSolverExpr<YicesExpr>(*LHS).Expr,
                  toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVNandImpl(const SMTExprRef &LHS,
                                     const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVNand, Context, LHS->Sort,
      yices_bvnand(toSolverExpr<YicesExpr>(*LHS).Expr,
                   toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUltImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUlt, Context, mkBoolSort(),
      yices_bvlt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSltImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSlt, Context, mkBoolSort(),
      yices_bvslt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                       toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUgtImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUgt, Context, mkBoolSort(),
      yices_bvgt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSgtImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSgt, Context, mkBoolSort(),
      yices_bvsgt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                       toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUleImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUle, Context, mkBoolSort(),
      yices_bvle_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSleImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSle, Context, mkBoolSort(),
      yices_bvsle_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                       toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVUgeImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVUge, Context, mkBoolSort(),
      yices_bvge_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVSgeImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSge, Context, mkBoolSort(),
      yices_bvsge_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                       toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkImpliesImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::Implies, Context, mkBoolSort(),
      yices_implies(toSolverExpr<YicesExpr>(*LHS).Expr,
                    toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkAndImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::And, Context, mkBoolSort(),
                                yices_and2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::Or, Context, mkBoolSort(),
                                yices_or2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkXorImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::Xor, Context, mkBoolSort(),
                                yices_xor2(toSolverExpr<YicesExpr>(*LHS).Expr,
                                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithAddImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithAdd, Context, LHS->Sort,
                                yices_add(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithSubImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithSub, Context, LHS->Sort,
                                yices_sub(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithMulImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithMul, Context, LHS->Sort,
                                yices_mul(toSolverExpr<YicesExpr>(*LHS).Expr,
                                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithDivImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithDiv, Context, LHS->Sort,
      yices_division(toSolverExpr<YicesExpr>(*LHS).Expr,
                     toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithLtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithLt, Context, mkBoolSort(),
      yices_arith_lt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithGtImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithGt, Context, mkBoolSort(),
      yices_arith_gt_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                          toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithLeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithLe, Context, mkBoolSort(),
      yices_arith_leq_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithGeImpl(const SMTExprRef &LHS,
                                      const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArithGe, Context, mkBoolSort(),
      yices_arith_geq_atom(toSolverExpr<YicesExpr>(*LHS).Expr,
                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkEqualImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::Equal, Context, mkBoolSort(),
                                yices_eq(toSolverExpr<YicesExpr>(*LHS).Expr,
                                         toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkBVConcatImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVConcat, Context,
      mkBVSort(LHS->getWidth() + RHS->getWidth()),
      yices_bvconcat2(toSolverExpr<YicesExpr>(*LHS).Expr,
                      toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkArithModImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<YicesExpr>(SMTExprKind::ArithMod, Context, mkIntSort(),
                                yices_imod(toSolverExpr<YicesExpr>(*LHS).Expr,
                                           toSolverExpr<YicesExpr>(*RHS).Expr));
}

SMTExprRef YicesSolver::mkInt2RealImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::Int2Real, Context, mkRealSort(),
      yices_division(toSolverExpr<YicesExpr>(*Exp).Expr,
                     toSolverExpr<YicesExpr>(*mkReal(1)).Expr));
}

SMTExprRef YicesSolver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                                  const SMTExprRef &F) {
  return makeExprRef<YicesExpr>(SMTExprKind::Ite, Context, T->Sort,
                                yices_ite(toSolverExpr<YicesExpr>(*Cond).Expr,
                                          toSolverExpr<YicesExpr>(*T).Expr,
                                          toSolverExpr<YicesExpr>(*F).Expr));
}

SMTExprRef YicesSolver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVSignExt, Context, mkBVSort(i + Exp->getWidth()),
      yices_sign_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i));
}

SMTExprRef YicesSolver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVZeroExt, Context, mkBVSort(i + Exp->getWidth()),
      yices_zero_extend(toSolverExpr<YicesExpr>(*Exp).Expr, i));
}

SMTExprRef YicesSolver::mkBVExtractImpl(unsigned High, unsigned Low,
                                        const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVExtract, Context, mkBVSort(High - Low + 1),
      yices_bvextract(toSolverExpr<YicesExpr>(*Exp).Expr, Low, High));
}

SMTExprRef YicesSolver::mkBVRedOrImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVRedOr, Context, mkBVSort(1),
      yices_redor(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkBVRedAndImpl(const SMTExprRef &Exp) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::BVRedAnd, Context, mkBVSort(1),
      yices_redand(toSolverExpr<YicesExpr>(*Exp).Expr));
}

SMTExprRef YicesSolver::mkArraySelectImpl(const SMTExprRef &Array,
                                          const SMTExprRef &Index) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArraySelect, Context, Array->Sort->getElementSort(),
      yices_application1(toSolverExpr<YicesExpr>(*Array).Expr,
                         toSolverExpr<YicesExpr>(*Index).Expr));
}

SMTExprRef YicesSolver::mkArrayStoreImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index,
                                         const SMTExprRef &Element) {
  return makeExprRef<YicesExpr>(
      SMTExprKind::ArrayStore, Context, Array->Sort,
      yices_update1(toSolverExpr<YicesExpr>(*Array).Expr,
                    toSolverExpr<YicesExpr>(*Index).Expr,
                    toSolverExpr<YicesExpr>(*Element).Expr));
}

SMTExprRef YicesSolver::mkApplyImpl(const SMTExprRef &Function,
                                    const std::vector<SMTExprRef> &Args) {
  std::vector<term_t> ApplyArgs;
  ApplyArgs.reserve(Args.size());
  for (const auto &Arg : Args)
    ApplyArgs.push_back(toSolverExpr<YicesExpr>(*Arg).Expr);
  return makeExprRef<YicesExpr>(
      SMTExprKind::Apply, Context, Function->Sort->getCodomainSort(),
      yices_application(toSolverExpr<YicesExpr>(*Function).Expr,
                        ApplyArgs.size(), ApplyArgs.data()));
}

SMTResult<bool> YicesSolver::getBoolImpl(const SMTExprRef &Exp) {
  int32_t val;
  auto res = yices_get_bool_value(yices_get_model(Context, 1),
                                  toSolverExpr<YicesExpr>(*Exp).Expr, &val);
  yicesCheckError(res, "Can't get boolean value from Yices");
  return val;
}

static inline void getYicesMPQValue(context_t *Context, term_t Expr,
                                    mpq_t Val) {
  auto res = yices_get_mpq_value(yices_get_model(Context, 1), Expr, Val);
  yicesCheckError(res, "Can't get rational value from Yices");
}

SMTResult<std::string> YicesSolver::getBVInBinImpl(const SMTExprRef &Exp) {
  unsigned width = Exp->getWidth();

  std::vector<int32_t> data(width);
  auto res =
      yices_get_bv_value(yices_get_model(Context, 1),
                         toSolverExpr<YicesExpr>(*Exp).Expr, data.data());
  if (res != 0)
    yicesCheckError(res, "Can't get bitvector value from Yices");

  std::string val;
  for (unsigned i = 0; i < width; i++)
    val.append(std::to_string(data[width - i - 1]));

  return val;
}

SMTResult<std::string> YicesSolver::getIntImpl(const SMTExprRef &Exp) {
  if (Exp->isRealSort()) {
    SMTResult<std::pair<std::string, std::string>> result =
        getRationalImpl(Exp);
    if (!result)
      return result.error();
    if (result.value().second != "1")
      return SMTError{SMTErrorCode::InvalidModelValue, SMTBackendKind::Yices,
                      "Real model value is not integral"};
    return result.value().first;
  }

  int64_t val;
  auto res = yices_get_int64_value(yices_get_model(Context, 1),
                                   toSolverExpr<YicesExpr>(*Exp).Expr, &val);
  yicesCheckError(res, "Can't get integer value from Yices");
  return std::to_string(val);
}

SMTResult<std::pair<std::string, std::string>>
YicesSolver::getRationalImpl(const SMTExprRef &Exp) {
  mpq_t val;
  mpq_init(val);
  getYicesMPQValue(Context, toSolverExpr<YicesExpr>(*Exp).Expr, val);
  char *raw_num = mpz_get_str(nullptr, 10, mpq_numref(val));
  char *raw_den = mpz_get_str(nullptr, 10, mpq_denref(val));
  std::string Num = raw_num;
  std::string Den = raw_den;
  void (*gmp_free)(void *, std::size_t);
  mp_get_memory_functions(nullptr, nullptr, &gmp_free);
  gmp_free(raw_num, Num.size() + 1);
  gmp_free(raw_den, Den.size() + 1);
  mpq_clear(val);
  return std::make_pair(Num, Den);
}

SMTExprRef YicesSolver::getArrayElementImpl(const SMTExprRef &Array,
                                            const SMTExprRef &Index) {
  const SMTExprRef &sel = mkArraySelect(Array, Index);

  const SMTSortRef &elementSort = Array->Sort->getElementSort();
  if (elementSort->isBoolSort()) {
    SMTResult<bool> result = getBool(sel);
    fatalErrorIf(!result, "Failed to get Yices boolean array element");
    return mkBool(result.value());
  }

  if (elementSort->isBVSort()) {
    SMTResult<std::string> result = getBVInBin(sel);
    fatalErrorIf(!result, "Failed to get Yices bit-vector array element");
    return SMTSolverImpl::mkBVFromBin(result.value());
  }

  fatalErrorIf(!elementSort->isFPSort(), "Unknown Yices array element type");
  SMTResult<std::string> result = getFPInBin(sel);
  fatalErrorIf(!result, "Failed to get Yices FP array element");
  return SMTSolverImpl::mkFPFromBin(
      result.value(), elementSort->getFPExponentWidth(), FPEncoding::BV);
}

SMTResult<ArrayModel> YicesSolver::getArrayValuesImpl(const SMTExprRef &Array) {
  model_t *Model = yices_get_model(Context, 1);
  yval_t Root;
  if (yices_get_value(Model, toSolverExpr<YicesExpr>(*Array).Expr, &Root) !=
          0 ||
      Root.node_tag != YVAL_FUNCTION)
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::Yices,
                    "Yices did not produce a function value for the array"};

  // Camada arrays are unary Yices functions; the expansion below writes
  // one index descriptor per mapping into a one-slot buffer.
  if (yices_val_function_arity(Model, &Root) != 1)
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::Yices,
                    "Yices array model has unexpected function arity"};

  const SMTSortRef &IndexSort = Array->Sort->getIndexSort();
  const SMTSortRef &ElemSort = Array->Sort->getElementSort();
  // Yices model values are descriptor nodes, not terms: rebuild each leaf
  // as a constant term of the Camada-facing sort. Returns a null ref for
  // shapes the backend cannot hold (nested functions).
  const auto wrap = [&](const yval_t &Value,
                        const SMTSortRef &Sort) -> SMTExprRef {
    if (Sort->isBoolSort()) {
      int32_t B = 0;
      if (yices_val_get_bool(Model, &Value, &B) != 0)
        return {};
      return makeExprRef<YicesExpr>(SMTExprKind::BoolConst, Context, Sort,
                                    B ? yices_true() : yices_false());
    }
    std::vector<int32_t> Bits(Sort->getWidth());
    if (Bits.empty() || yices_val_get_bv(Model, &Value, Bits.data()) != 0)
      return {};
    return makeExprRef<YicesExpr>(
        valueKindForSort(Sort), Context, Sort,
        yices_bvconst_from_array(static_cast<uint32_t>(Bits.size()),
                                 Bits.data()));
  };

  yval_t Def;
  yval_vector_t Mappings;
  yices_init_yval_vector(&Mappings);
  if (yices_val_expand_function(Model, &Root, &Def, &Mappings) != 0) {
    yices_delete_yval_vector(&Mappings);
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::Yices,
                    "Yices could not expand the array's function value"};
  }

  ArrayModel Result;
  for (uint32_t I = 0; I < Mappings.size; ++I) {
    yval_t IndexVal[1];
    yval_t ElemVal;
    if (yices_val_expand_mapping(Model, &Mappings.data[I], IndexVal,
                                 &ElemVal) != 0) {
      // A mapping the model distinguishes but we cannot read would decode
      // as the default value — error out instead of dropping it.
      yices_delete_yval_vector(&Mappings);
      return SMTError{SMTErrorCode::BackendError, SMTBackendKind::Yices,
                      "Yices could not expand an array model mapping"};
    }
    SMTExprRef IndexExpr = wrap(IndexVal[0], IndexSort);
    SMTExprRef ElemExpr = wrap(ElemVal, ElemSort);
    if (!IndexExpr || !ElemExpr) {
      yices_delete_yval_vector(&Mappings);
      return SMTError{SMTErrorCode::BackendError, SMTBackendKind::Yices,
                      "Yices array model entry has an unsupported shape"};
    }
    Result.Entries.emplace_back(std::move(IndexExpr), std::move(ElemExpr));
  }
  if (Def.node_tag != YVAL_UNKNOWN) {
    Result.Base = wrap(Def, ElemSort);
    if (!Result.Base) {
      // Yices reported a default we cannot read; a null Base would claim
      // the unlisted indexes are unconstrained.
      yices_delete_yval_vector(&Mappings);
      return SMTError{SMTErrorCode::BackendError, SMTBackendKind::Yices,
                      "Yices array model default has an unsupported shape"};
    }
  }
  yices_delete_yval_vector(&Mappings);
  return Result;
}

SMTExprRef YicesSolver::mkBoolImpl(const bool b) {
  return makeExprRef<YicesExpr>(SMTExprKind::BoolConst, Context, mkBoolSort(),
                                b ? yices_true() : yices_false());
}

SMTExprRef YicesSolver::mkIntImpl(int64_t v) {
  return makeExprRef<YicesExpr>(SMTExprKind::IntConst, Context, mkIntSort(),
                                yices_int64(v));
}

SMTExprRef YicesSolver::mkIntImpl(const std::string &v) {
  mpz_t val;
  mpz_init_set_str(val, v.c_str(), 10);
  term_t term = yices_mpz(val);
  mpz_clear(val);
  return makeExprRef<YicesExpr>(SMTExprKind::IntConst, Context, mkIntSort(),
                                term);
}

SMTExprRef YicesSolver::mkRealImpl(const std::string &v) {
  return makeExprRef<YicesExpr>(SMTExprKind::RealConst, Context, mkRealSort(),
                                yices_parse_rational(v.c_str()));
}

SMTExprRef YicesSolver::mkRealImpl(int64_t v) {
  return mkRealImpl(std::to_string(v));
}

SMTExprRef YicesSolver::mkRealImpl(int64_t num, int64_t den) {
  return mkRealImpl(std::to_string(num) + "/" + std::to_string(den));
}

SMTExprRef YicesSolver::mkBVFromDecImpl(const int64_t Int,
                                        const SMTSortRef &Sort) {
  return makeExprRef<YicesExpr>(SMTExprKind::BVConst, Context, Sort,
                                yices_bvconst_int64(Sort->getWidth(), Int));
}

SMTExprRef YicesSolver::mkBVFromBinImpl(const std::string &Int,
                                        const SMTSortRef &Sort) {
  return makeExprRef<YicesExpr>(SMTExprKind::BVConst, Context, Sort,
                                yices_parse_bvbin(Int.c_str()));
}

SMTExprRef YicesSolver::mkSymbolImpl(const std::string &Name,
                                     const SMTSortRef &Sort) {
  term_t t = yicesCheckTerm(
      yices_new_uninterpreted_term(toSolverSort<YicesSort>(*Sort).Sort),
      "Error when trying to create a new Yices symbol");

  yicesCheckError(yices_set_term_name(t, Name.c_str()),
                  "Error when trying to set Yices symbol name");
  NamedSymbols.push_back(Name);

  return makeExprRef<YicesExpr>(SMTExprKind::Symbol, Context, Sort, t);
}

SMTExprRef YicesSolver::mkArrayConstImpl(const SMTSortRef &,
                                         const SMTExprRef &) {
  fatalError("Yices constant arrays are lowered lazily by the common layer");
}

void YicesSolver::armTimeout() {
#if !defined(_WIN32)
  if (TimeoutMs == 0)
    return;
  YicesSearchContext.store(Context);
  struct sigaction Action = {};
  Action.sa_handler = yicesAlarmHandler;
  // yices_stop_search works through a flag the search loop polls, so the
  // handler needs no syscall interruption: restart slow syscalls instead
  // of surfacing spurious EINTRs to the rest of the process.
  Action.sa_flags = SA_RESTART;
  sigemptyset(&Action.sa_mask);
  sigaction(SIGALRM, &Action, &YicesOldAlarmAction);
  itimerval Timer{};
  Timer.it_value.tv_sec = static_cast<time_t>(TimeoutMs / 1000);
  Timer.it_value.tv_usec = static_cast<suseconds_t>((TimeoutMs % 1000) * 1000);
  setitimer(ITIMER_REAL, &Timer, nullptr);
#endif
}

void YicesSolver::disarmTimeout() {
#if !defined(_WIN32)
  if (TimeoutMs == 0)
    return;
  // A timer that expired between the check returning and the cancel below
  // leaves SIGALRM pending; delivering it after the old disposition is
  // restored could terminate the process (SIG_DFL). Block the signal,
  // cancel the timer, discard any pending instance (POSIX guarantees
  // setting SIG_IGN discards pending signals), then restore.
  sigset_t AlarmSet, OldSet;
  sigemptyset(&AlarmSet);
  sigaddset(&AlarmSet, SIGALRM);
  pthread_sigmask(SIG_BLOCK, &AlarmSet, &OldSet);
  itimerval Off{};
  setitimer(ITIMER_REAL, &Off, nullptr);
  struct sigaction Ignore = {};
  Ignore.sa_handler = SIG_IGN;
  sigemptyset(&Ignore.sa_mask);
  sigaction(SIGALRM, &Ignore, nullptr);
  sigaction(SIGALRM, &YicesOldAlarmAction, nullptr);
  YicesSearchContext.store(nullptr);
  pthread_sigmask(SIG_SETMASK, &OldSet, nullptr);
#endif
}

bool YicesSolver::setTimeoutImpl(uint64_t) {
#if defined(_WIN32)
  return false;
#else
  return true;
#endif
}

bool YicesSolver::supportsImpl(SolverFeature Feature) const {
  switch (Feature) {
  case SolverFeature::IntRealArithmetic:
  case SolverFeature::UninterpretedFunctions:
  case SolverFeature::UnsatAssumptions:
  case SolverFeature::ArrayModels:
    return true;
  case SolverFeature::Timeouts:
    // Enforced through SIGALRM + yices_stop_search; POSIX only.
#if defined(_WIN32)
    return false;
#else
    return true;
#endif
  case SolverFeature::Quantifiers:
  case SolverFeature::NativeFloatingPoint:
    return false;
  case SolverFeature::NativeTuples:
  case SolverFeature::NativeConstantArrays:
    break; // answered by the common layer's hooks
  }
  return false;
}

checkResult YicesSolver::checkImpl() {
  armTimeout();
  smt_status_t res = yices_check_context(Context, nullptr);
  disarmTimeout();
  if (res == YICES_STATUS_SAT)
    return checkResult::SAT;

  if (res == YICES_STATUS_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

checkResult
YicesSolver::checkSatAssumingImpl(const std::vector<SMTExprRef> &Assumptions) {
  std::vector<term_t> assumptions;
  assumptions.reserve(Assumptions.size());
  for (const SMTExprRef &Assumption : Assumptions)
    assumptions.push_back(toSolverExpr<YicesExpr>(*Assumption).Expr);

  armTimeout();
  smt_status_t res = yices_check_context_with_assumptions(
      Context, nullptr, static_cast<uint32_t>(assumptions.size()),
      assumptions.data());
  disarmTimeout();
  if (res == YICES_STATUS_SAT)
    return checkResult::SAT;

  if (res == YICES_STATUS_UNSAT)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

SMTResult<std::vector<SMTExprRef>> YicesSolver::getUnsatAssumptionsImpl() {
  term_vector_t core;
  yices_init_term_vector(&core);
  if (yices_get_unsat_core(Context, &core) != 0) {
    yices_delete_term_vector(&core);
    return SMTError{SMTErrorCode::BackendError, SMTBackendKind::Yices,
                    "Yices could not retrieve the unsat core"};
  }
  std::vector<SMTExprRef> Result;
  for (uint32_t i = 0; i < core.size; ++i)
    for (const SMTExprRef &Assumption : LastAssumptions)
      if (core.data[i] == toSolverExpr<YicesExpr>(*Assumption).Expr) {
        Result.push_back(Assumption);
        break;
      }
  yices_delete_term_vector(&core);
  return Result;
}

void YicesSolver::resetImpl() {
  Assertions.clear();
  AssertionScopeSizes.clear();
  recreateContext("QF_AUFBV");
}

void YicesSolver::pushImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i) {
    AssertionScopeSizes.push_back(Assertions.size());
    yicesCheckError(yices_push(Context), "Could not push Yices context");
  }
}

void YicesSolver::popImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i) {
    assert(!AssertionScopeSizes.empty() && "Could not pop empty Yices scope");
    yicesCheckError(yices_pop(Context), "Could not pop Yices context");
    Assertions.resize(AssertionScopeSizes.back());
    AssertionScopeSizes.pop_back();
  }
}

std::string YicesSolver::getSolverNameAndVersion() const {
  return std::string("Yices v").append(yices_version);
}

void YicesSolver::dumpImpl(std::string &Out) {
  Out.clear();
  for (auto const &a : Assertions) {
    std::string Assertion;
    a->dump(Assertion);
    Out += Assertion;
  }
}

void YicesSolver::dumpModelImpl(std::string &Out) {
  char *model_str =
      yices_model_to_string(yices_get_model(Context, 1), 160, 80, 0);
  Out = model_str;
  Out += "\n";
  yices_free_string(model_str);
}

} // namespace camada

#endif
