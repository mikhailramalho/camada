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

#include "ac_config.h"
#if SOLVER_Z3_ENABLED

#include "z3solver.h"

#include <cstdio>

namespace camada {

namespace {

static inline const z3::ast &toZ3Ast(const SMTExpr &Exp) {
  return toSolverExpr<Z3Expr>(Exp).Expr;
}

static inline const z3::ast &toZ3Ast(const SMTExprRef &Exp) {
  return toSolverExpr<Z3Expr>(*Exp).Expr;
}

static inline z3::expr toZ3Expr(const SMTExpr &Exp) {
  auto const &ZE = toSolverExpr<Z3Expr>(Exp);
  return z3::to_expr(*ZE.Context, ZE.Expr);
}

static inline z3::expr toZ3Expr(const SMTExprRef &Exp) {
  auto const &ZE = toSolverExpr<Z3Expr>(*Exp);
  return z3::to_expr(*ZE.Context, ZE.Expr);
}

static inline z3::func_decl toZ3FuncDecl(const SMTExpr &Exp) {
  auto const &ZE = toSolverExpr<Z3Expr>(Exp);
  return z3::func_decl(*ZE.Context, reinterpret_cast<Z3_func_decl>(
                                        static_cast<Z3_ast>(ZE.Expr)));
}

static inline z3::func_decl toZ3FuncDecl(const SMTExprRef &Exp) {
  auto const &ZE = toSolverExpr<Z3Expr>(*Exp);
  return z3::func_decl(*ZE.Context, reinterpret_cast<Z3_func_decl>(
                                        static_cast<Z3_ast>(ZE.Expr)));
}

} // namespace

unsigned Z3Sort::getWidthFromSolver() const {
  if (isTupleSort())
    return 0;

  if (Sort.is_bv())
    return Sort.bv_size();

  if (Sort.is_bool())
    return 1;

  if (Sort.is_int() || Sort.is_real())
    return 0;

  if (Sort.is_fpa())
    return Sort.fpa_ebits() + Sort.fpa_sbits();

  assert(Sort.sort_kind() == Z3_ROUNDING_MODE_SORT);
  return 3;
}

void Z3Sort::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void Z3Sort::dump(std::string &Out) const {
  Out = Sort.to_string();
  Out += "\n";
}

bool Z3Expr::equal_to(SMTExpr const &Other) const {
  if (Sort != Other.Sort || Other.getBackendKind() != getBackendKind())
    return false;
  return z3::eq(Expr, static_cast<const Z3Expr &>(Other).Expr);
}

void Z3Expr::dump() const {
  std::string Out;
  dump(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void Z3Expr::dump(std::string &Out) const {
  Out = Expr.to_string();
  Out += "\n";
}

Z3Solver::Z3Solver() : SMTSolverImpl(), Context(), Solver(Context) {
  // Needs to be set in order to convert NaN to bitvector
  z3::set_param("rewriter.hi_fp_unspecified", true);
  initializeCommonSingletons();
}

Z3Solver::Z3Solver(z3::context C)
    : SMTSolverImpl(), Context(std::move(C)), Solver(Context) {
  z3::set_param("rewriter.hi_fp_unspecified", true);
  initializeCommonSingletons();
}

Z3Solver::Z3Solver(z3::context C, z3::solver S)
    : SMTSolverImpl(), Context(std::move(C)), Solver(std::move(S)) {
  // Needs to be set in order to convert NaN to bitvector
  z3::set_param("rewriter.hi_fp_unspecified", true);
  initializeCommonSingletons();
}

Z3Solver::~Z3Solver() { invalidateGeneratedObjects(); }

void Z3Solver::addConstraintImpl(const SMTExprRef &Exp) {
  Solver.add(toZ3Expr(Exp));
}

SMTExprRef Z3Solver::newExprRefImpl(const SMTExpr &Exp) const {
  return storeExprRef(toSolverExpr<Z3Expr>(Exp));
}

SMTExprRef Z3Solver::rewrapExprImpl(const SMTExpr &Exp, const SMTSortRef &Sort,
                                    SMTExprKind Kind) const {
  const auto &Wrapped = toSolverExpr<Z3Expr>(Exp);
  return storeExprRef(Z3Expr(Kind, Wrapped.Context, Sort, Wrapped.Expr));
}

SMTSortRef Z3Solver::mkBoolSortImpl() {
  return newSortRef<Z3Sort>(Z3Sort(SMTSortKind::Bool, &Context,
                                   Context.bool_sort(),
                                   SMTSort::ScalarSortData{1}));
}

SMTSortRef Z3Solver::mkIntSortImpl() {
  return newSortRef<Z3Sort>(
      Z3Sort(SMTSortKind::Int, &Context, Context.int_sort()));
}

SMTSortRef Z3Solver::mkRealSortImpl() {
  return newSortRef<Z3Sort>(
      Z3Sort(SMTSortKind::Real, &Context, Context.real_sort()));
}

SMTSortRef Z3Solver::mkBVSortImpl(unsigned BitWidth) {
  return newSortRef<Z3Sort>(Z3Sort(SMTSortKind::BV, &Context,
                                   Context.bv_sort(BitWidth),
                                   SMTSort::ScalarSortData{BitWidth}));
}

SMTSortRef Z3Solver::mkRMSortImpl() {
  return newSortRef<Z3Sort>(Z3Sort(SMTSortKind::RM, &Context,
                                   Context.fpa_rounding_mode_sort(),
                                   SMTSort::ScalarSortData{3}));
}

SMTSortRef Z3Solver::mkFPSortImpl(const unsigned ExpWidth,
                                  const unsigned SigWidth) {
  return newSortRef<Z3Sort>(Z3Sort(
      SMTSortKind::FP, &Context, Context.fpa_sort(ExpWidth, SigWidth + 1),
      SMTSort::FPSortData{ExpWidth + SigWidth + 1, ExpWidth, SigWidth}));
}

SMTSortRef Z3Solver::mkBVFPSortImpl(const unsigned ExpWidth,
                                    const unsigned SigWidth) {
  return newSortRef<Z3Sort>(Z3Sort(
      SMTSortKind::BVFP, &Context, Context.bv_sort(ExpWidth + SigWidth + 1),
      SMTSort::FPSortData{ExpWidth + SigWidth + 1, ExpWidth, SigWidth + 1}));
}

SMTSortRef Z3Solver::mkBVRMSortImpl() {
  return newSortRef<Z3Sort>(Z3Sort(SMTSortKind::BVRM, &Context,
                                   Context.bv_sort(3),
                                   SMTSort::ScalarSortData{3}));
}

SMTSortRef Z3Solver::mkArraySortImpl(const SMTSortRef &IndexSort,
                                     const SMTSortRef &ElemSort) {
  return newSortRef<Z3Sort>(
      Z3Sort(SMTSortKind::Array, &Context,
             Context.array_sort(toSolverSort<Z3Sort>(*IndexSort).Sort,
                                toSolverSort<Z3Sort>(*ElemSort).Sort),
             SMTSort::ArraySortData{IndexSort, ElemSort}));
}

SMTSortRef
Z3Solver::mkFunctionSortImpl(const std::vector<SMTSortRef> &DomainSorts,
                             const SMTSortRef &CodomainSort) {
  return newSortRef<Z3Sort>(Z3Sort(
      SMTSortKind::Function, &Context, toSolverSort<Z3Sort>(*CodomainSort).Sort,
      SMTSort::FunctionSortData{DomainSorts, CodomainSort}));
}

SMTSortRef
Z3Solver::mkTupleSortImpl(const std::vector<SMTSortRef> &ElementSorts) {
  std::vector<z3::sort> Fields;
  Fields.reserve(ElementSorts.size());
  std::vector<std::string> FieldNames;
  FieldNames.reserve(ElementSorts.size());
  for (std::size_t I = 0; I < ElementSorts.size(); ++I) {
    Fields.push_back(toSolverSort<Z3Sort>(*ElementSorts[I]).Sort);
    FieldNames.push_back("field_" + std::to_string(I));
  }

  std::vector<char const *> NamePtrs;
  NamePtrs.reserve(FieldNames.size());
  for (const auto &Name : FieldNames)
    NamePtrs.push_back(Name.c_str());

  z3::func_decl_vector Projs(Context);
  z3::func_decl Ctor = Context.tuple_sort(
      ("camada_tuple_" + std::to_string(TupleCounter++)).c_str(),
      static_cast<unsigned>(Fields.size()), NamePtrs.data(), Fields.data(),
      Projs);

  return newSortRef<Z3Sort>(Z3Sort(SMTSortKind::Tuple, &Context, Ctor.range(),
                                   SMTSort::TupleSortData{ElementSorts}));
}

SMTExprRef Z3Solver::mkBVNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVNeg, &Context, Exp->Sort,
                             -toZ3Expr(Exp));
}

SMTExprRef Z3Solver::mkBVNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVNot, &Context, Exp->Sort,
                             ~toZ3Expr(Exp));
}

SMTExprRef Z3Solver::mkNotImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::Not, &Context, Exp->Sort,
                             !toZ3Expr(Exp));
}

SMTExprRef Z3Solver::mkBVRedOrImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVRedOr, &Context, mkBVSort(1),
                             z3::bvredor(toZ3Expr(Exp)));
}

SMTExprRef Z3Solver::mkBVRedAndImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVRedAnd, &Context, mkBVSort(1),
                             z3::bvredand(toZ3Expr(Exp)));
}

SMTExprRef Z3Solver::mkArithNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithNeg, &Context, Exp->Sort,
                             -toZ3Expr(Exp));
}

SMTExprRef Z3Solver::mkInt2RealImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::Int2Real, &Context, mkRealSort(),
                             z3::to_real(toZ3Expr(Exp)));
}

SMTExprRef Z3Solver::mkIsIntImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::IsInt, &Context, mkBoolSort(),
                             z3::is_int(toZ3Expr(Exp)));
}

SMTExprRef Z3Solver::mkFPAbsImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPAbs, &Context, Exp->Sort,
                             z3::abs(toZ3Expr(Exp)));
}

SMTExprRef Z3Solver::mkFPNegImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPNeg, &Context, Exp->Sort,
                             -toZ3Expr(Exp));
}

SMTExprRef Z3Solver::mkFPIsInfiniteImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPIsInfinite, &Context, mkBoolSort(),
                             toZ3Expr(Exp).mk_is_inf());
}

SMTExprRef Z3Solver::mkFPIsNaNImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPIsNaN, &Context, mkBoolSort(),
                             toZ3Expr(Exp).mk_is_nan());
}

SMTExprRef Z3Solver::mkFPIsDenormalImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPIsDenormal, &Context, mkBoolSort(),
                             toZ3Expr(Exp).mk_is_subnormal());
}

SMTExprRef Z3Solver::mkFPIsNormalImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPIsNormal, &Context, mkBoolSort(),
                             toZ3Expr(Exp).mk_is_normal());
}

SMTExprRef Z3Solver::mkFPIsZeroImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPIsZero, &Context, mkBoolSort(),
                             toZ3Expr(Exp).mk_is_zero());
}

SMTExprRef Z3Solver::mkBVAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVAdd, &Context, LHS->Sort,
                             toZ3Expr(LHS) + toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVSub, &Context, LHS->Sort,
                             toZ3Expr(LHS) - toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVMul, &Context, LHS->Sort,
                             toZ3Expr(LHS) * toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVSRemImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVSRem, &Context, LHS->Sort,
                             z3::srem(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVURemImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVURem, &Context, LHS->Sort,
                             z3::urem(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVSDivImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVSDiv, &Context, LHS->Sort,
                             toZ3Expr(LHS) / toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVUDivImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVUDiv, &Context, LHS->Sort,
                             z3::udiv(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVShlImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVShl, &Context, LHS->Sort,
                             z3::shl(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVAshrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVAshr, &Context, LHS->Sort,
                             z3::ashr(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVLshrImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVLshr, &Context, LHS->Sort,
                             z3::lshr(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVXor, &Context, LHS->Sort,
                             toZ3Expr(LHS) ^ toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVOr, &Context, LHS->Sort,
                             toZ3Expr(LHS) | toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVAnd, &Context, LHS->Sort,
                             toZ3Expr(LHS) & toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVXnorImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVXnor, &Context, LHS->Sort,
                             z3::xnor(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVNorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVNor, &Context, LHS->Sort,
                             z3::nor(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVNandImpl(const SMTExprRef &LHS,
                                  const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVNand, &Context, LHS->Sort,
                             z3::nand(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVUltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVUlt, &Context, mkBoolSort(),
                             z3::ult(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVSltImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVSlt, &Context, mkBoolSort(),
                             z3::slt(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVUgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVUgt, &Context, mkBoolSort(),
                             z3::ugt(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVSgtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVSgt, &Context, mkBoolSort(),
                             toZ3Expr(LHS) > toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVUleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVUle, &Context, mkBoolSort(),
                             z3::ule(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVSleImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVSle, &Context, mkBoolSort(),
                             z3::sle(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVUgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVUge, &Context, mkBoolSort(),
                             z3::uge(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkBVSgeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVSge, &Context, mkBoolSort(),
                             toZ3Expr(LHS) >= toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkImpliesImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::Implies, &Context, mkBoolSort(),
                             z3::implies(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkAndImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::And, &Context, mkBoolSort(),
                             toZ3Expr(LHS) && toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkOrImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::Or, &Context, mkBoolSort(),
                             toZ3Expr(LHS) || toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkXorImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::Xor, &Context, LHS->Sort,
                             toZ3Expr(LHS) ^ toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkArithAddImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithAdd, &Context, LHS->Sort,
                             toZ3Expr(LHS) + toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkArithSubImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithSub, &Context, LHS->Sort,
                             toZ3Expr(LHS) - toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkArithMulImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithMul, &Context, LHS->Sort,
                             toZ3Expr(LHS) * toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkArithDivImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithDiv, &Context, LHS->Sort,
                             toZ3Expr(LHS) / toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkArithModImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithMod, &Context, mkIntSort(),
                             z3::mod(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkArithShlImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithShl, &Context, mkIntSort(),
                             toZ3Expr(LHS) *
                                 z3::pw(toZ3Expr(mkInt("2")), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkArithLtImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithLt, &Context, mkBoolSort(),
                             toZ3Expr(LHS) < toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkArithGtImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithGt, &Context, mkBoolSort(),
                             toZ3Expr(LHS) > toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkArithLeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithLe, &Context, mkBoolSort(),
                             toZ3Expr(LHS) <= toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkArithGeImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArithGe, &Context, mkBoolSort(),
                             toZ3Expr(LHS) >= toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkEqualImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::Equal, &Context, mkBoolSort(),
                             toZ3Expr(LHS) == toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkBVConcatImpl(const SMTExprRef &LHS,
                                    const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVConcat, &Context,
                             mkBVSort(LHS->getWidth() + RHS->getWidth()),
                             z3::concat(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkArraySelectImpl(const SMTExprRef &LHS,
                                       const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::ArraySelect, &Context,
                             LHS->Sort->getElementSort(),
                             z3::select(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkFPRemImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPRem, &Context, LHS->Sort,
                             z3::rem(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkFPLtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPLt, &Context, mkBoolSort(),
                             toZ3Expr(LHS) < toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkFPGtImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPGt, &Context, mkBoolSort(),
                             toZ3Expr(LHS) > toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkFPLeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPLe, &Context, mkBoolSort(),
                             toZ3Expr(LHS) <= toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkFPGeImpl(const SMTExprRef &LHS, const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPGe, &Context, mkBoolSort(),
                             toZ3Expr(LHS) >= toZ3Expr(RHS));
}

SMTExprRef Z3Solver::mkFPEqualImpl(const SMTExprRef &LHS,
                                   const SMTExprRef &RHS) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPEqual, &Context, mkBoolSort(),
                             z3::fp_eq(toZ3Expr(LHS), toZ3Expr(RHS)));
}

SMTExprRef Z3Solver::mkReal2IntImpl(const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::Real2Int, &Context, mkIntSort(),
      z3::to_expr(Context, Z3_mk_real2int(Context, toZ3Expr(Exp))));
}

SMTExprRef Z3Solver::mkBVSignExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVSignExt, &Context,
                             mkBVSort(i + Exp->getWidth()),
                             z3::sext(toZ3Expr(Exp), i));
}

SMTExprRef Z3Solver::mkBVZeroExtImpl(unsigned i, const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVZeroExt, &Context,
                             mkBVSort(i + Exp->getWidth()),
                             z3::zext(toZ3Expr(Exp), i));
}

SMTExprRef Z3Solver::mkBVExtractImpl(unsigned High, unsigned Low,
                                     const SMTExprRef &Exp) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVExtract, &Context,
                             mkBVSort(High - Low + 1),
                             toZ3Expr(Exp).extract(High, Low));
}

SMTExprRef Z3Solver::mkIteImpl(const SMTExprRef &Cond, const SMTExprRef &T,
                               const SMTExprRef &F) {
  return makeExprRef<Z3Expr>(SMTExprKind::Ite, &Context, T->Sort,
                             z3::ite(toZ3Expr(Cond), toZ3Expr(T), toZ3Expr(F)));
}

SMTExprRef Z3Solver::mkArrayStoreImpl(const SMTExprRef &Array,
                                      const SMTExprRef &Index,
                                      const SMTExprRef &Element) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::ArrayStore, &Context, Array->Sort,
      z3::store(toZ3Expr(Array), toZ3Expr(Index), toZ3Expr(Element)));
}

SMTExprRef Z3Solver::mkTupleImpl(const std::vector<SMTExprRef> &Elements) {
  std::vector<SMTSortRef> ElementSorts;
  ElementSorts.reserve(Elements.size());
  for (const auto &Element : Elements)
    ElementSorts.push_back(Element->Sort);
  SMTSortRef TupleSort = mkTupleSort(ElementSorts);

  z3::func_decl Ctor(Context,
                     Z3_get_tuple_sort_mk_decl(
                         Context, toSolverSort<Z3Sort>(*TupleSort).Sort));
  std::vector<Z3_ast> Args;
  Args.reserve(Elements.size());
  for (const auto &Element : Elements)
    Args.push_back(toZ3Expr(Element));
  return makeExprRef<Z3Expr>(
      SMTExprKind::TupleConst, &Context, TupleSort,
      z3::to_expr(Context, Z3_mk_app(Context, Ctor, Args.size(), Args.data())));
}

SMTExprRef Z3Solver::mkTupleSelectImpl(const SMTExprRef &Tuple,
                                       unsigned Index) {
  Z3_func_decl FieldDecl = Z3_get_tuple_sort_field_decl(
      Context, toSolverSort<Z3Sort>(*Tuple->Sort).Sort, Index);
  Z3_ast Arg = toZ3Ast(Tuple);
  return makeExprRef<Z3Expr>(
      SMTExprKind::TupleSelect, &Context,
      Tuple->Sort->getTupleElementSorts()[Index],
      z3::to_expr(Context, Z3_mk_app(Context, FieldDecl, 1, &Arg)));
}

SMTExprRef Z3Solver::mkApplyImpl(const SMTExprRef &Function,
                                 const std::vector<SMTExprRef> &Args) {
  std::vector<Z3_ast> AppArgs;
  AppArgs.reserve(Args.size());
  for (const auto &Arg : Args)
    AppArgs.push_back(toZ3Expr(Arg));
  return makeExprRef<Z3Expr>(
      SMTExprKind::Apply, &Context, Function->Sort->getCodomainSort(),
      z3::to_expr(Context, Z3_mk_app(Context, toZ3FuncDecl(Function),
                                     AppArgs.size(), AppArgs.data())));
}

SMTExprRef Z3Solver::mkFPMulImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPMul, &Context, LHS->Sort,
      z3::to_expr(Context, Z3_mk_fpa_mul(Context, toZ3Expr(R), toZ3Expr(LHS),
                                         toZ3Expr(RHS))));
}

SMTExprRef Z3Solver::mkFPDivImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPDiv, &Context, LHS->Sort,
      z3::to_expr(Context, Z3_mk_fpa_div(Context, toZ3Expr(R), toZ3Expr(LHS),
                                         toZ3Expr(RHS))));
}

SMTExprRef Z3Solver::mkFPAddImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPAdd, &Context, LHS->Sort,
      z3::to_expr(Context, Z3_mk_fpa_add(Context, toZ3Expr(R), toZ3Expr(LHS),
                                         toZ3Expr(RHS))));
}

SMTExprRef Z3Solver::mkFPSubImpl(const SMTExprRef &LHS, const SMTExprRef &RHS,
                                 const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPSub, &Context, LHS->Sort,
      z3::to_expr(Context, Z3_mk_fpa_sub(Context, toZ3Expr(R), toZ3Expr(LHS),
                                         toZ3Expr(RHS))));
}

SMTExprRef Z3Solver::mkFPSqrtImpl(const SMTExprRef &Exp, const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(SMTExprKind::FPSqrt, &Context, Exp->Sort,
                             z3::sqrt(toZ3Expr(Exp), toZ3Expr(R)));
}

SMTExprRef Z3Solver::mkFPFMAImpl(const SMTExprRef &X, const SMTExprRef &Y,
                                 const SMTExprRef &Z, const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPFMA, &Context, X->Sort,
      z3::fma(toZ3Expr(X), toZ3Expr(Y), toZ3Expr(Z), toZ3Expr(R)));
}

SMTExprRef Z3Solver::mkFPtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                  const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPtoFP, &Context, To,
      z3::to_expr(Context,
                  Z3_mk_fpa_to_fp_float(Context, toZ3Expr(R), toZ3Expr(From),
                                        toSolverSort<Z3Sort>(*To).Sort)));
}

SMTExprRef Z3Solver::mkSBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::SBVtoFP, &Context, To,
      z3::to_expr(Context,
                  Z3_mk_fpa_to_fp_signed(Context, toZ3Expr(R), toZ3Expr(From),
                                         toSolverSort<Z3Sort>(*To).Sort)));
}

SMTExprRef Z3Solver::mkUBVtoFPImpl(const SMTExprRef &From, const SMTSortRef &To,
                                   const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::UBVtoFP, &Context, To,
      z3::to_expr(Context,
                  Z3_mk_fpa_to_fp_unsigned(Context, toZ3Expr(R), toZ3Expr(From),
                                           toSolverSort<Z3Sort>(*To).Sort)));
}

SMTExprRef Z3Solver::mkFPtoSBVImpl(const SMTExprRef &From, unsigned ToWidth) {
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPtoSBV, &Context, mkBVSort(ToWidth),
      z3::to_expr(Context, Z3_mk_fpa_to_sbv(Context, toZ3Expr(roundingMode),
                                            toZ3Expr(From), ToWidth)));
}

SMTExprRef Z3Solver::mkFPtoUBVImpl(const SMTExprRef &From, unsigned ToWidth) {
  const SMTExprRef &roundingMode = mkRM(RM::ROUND_TO_ZERO, FPEncoding::Native);
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPtoUBV, &Context, mkBVSort(ToWidth),
      z3::to_expr(Context, Z3_mk_fpa_to_ubv(Context, toZ3Expr(roundingMode),
                                            toZ3Expr(From), ToWidth)));
}

SMTExprRef Z3Solver::mkFPtoIntegralImpl(const SMTExprRef &From,
                                        const SMTExprRef &R) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPtoIntegral, &Context, From->Sort,
      z3::to_expr(Context, Z3_mk_fpa_round_to_integral(Context, toZ3Expr(R),
                                                       toZ3Expr(From))));
}

bool Z3Solver::getBoolImpl(const SMTExprRef &Exp) {
  switch (toZ3Expr(Exp).bool_value()) {
  case Z3_L_TRUE:
    return true;
  case Z3_L_FALSE:
    return false;
  case Z3_L_UNDEF:
    break;
  }
  fatalError("Bool is neither true nor false");
}

std::string Z3Solver::getBVInBinImpl(const SMTExprRef &Exp) {
  SMTExprRef value = Exp;
  if (Solver.get_model().has_interp(toZ3Expr(Exp).decl())) {
    value = makeExprRef<Z3Expr>(
        Exp->getKind(), &Context, Exp->Sort,
        Solver.get_model().get_const_interp(toZ3Expr(Exp).decl()));
  }
  std::string bv;
  bool is_num = toZ3Expr(value).as_binary(bv);
  (void)is_num;
  assert(is_num && "Failed to get bitvector from Z3");
  return bv;
}

std::string Z3Solver::getIntImpl(const SMTExprRef &Exp) {
  z3::expr value = Solver.get_model().eval(toZ3Expr(Exp), true);
  if (Exp->isRealSort()) {
    std::string Num, Den;
    getRationalImpl(Exp, Num, Den);
    assert(Den == "1" && "Real value is not integral");
    return Num;
  }
  assert(value.is_numeral() && "Expected integer numeral from Z3");
  std::string numeral;
  bool is_num = value.is_numeral(numeral);
  (void)is_num;
  assert(is_num && "Failed to get integer numeral from Z3");
  return numeral;
}

void Z3Solver::getRationalImpl(const SMTExprRef &Exp, std::string &Num,
                               std::string &Den) {
  z3::expr value = Solver.get_model().eval(toZ3Expr(Exp), true);
  assert(value.is_numeral() && "Expected rational numeral from Z3");
  std::string num;
  std::string den;
  bool has_num = value.numerator().is_numeral(num);
  bool has_den = value.denominator().is_numeral(den);
  (void)has_num;
  (void)has_den;
  assert(has_num && has_den && "Failed to get rational numeral from Z3");
  Num = num;
  Den = den;
}

std::string Z3Solver::getFPInBinImpl(const SMTExprRef &Exp) {
  SMTExprRef value = Exp;
  if (Solver.get_model().has_interp(toZ3Expr(Exp).decl())) {
    value = makeExprRef<Z3Expr>(
        Exp->getKind(), &Context, Exp->Sort,
        Solver.get_model().get_const_interp(toZ3Expr(Exp).decl()));
  }

  // Convert the float to bv
  z3::expr fp_value =
      Solver.get_model().eval(toZ3Expr(value).mk_to_ieee_bv(), true);
  std::string bv;
  bool is_num = fp_value.as_binary(bv);
  (void)is_num;
  assert(is_num && "Failed to convert FP to BV in Z3");
  return bv;
}

SMTExprRef Z3Solver::getArrayElementImpl(const SMTExprRef &Array,
                                         const SMTExprRef &Index) {
  const SMTExprRef &sel = mkArraySelect(Array, Index);
  return makeExprRef<Z3Expr>(sel->getKind(), &Context, sel->Sort,
                             Solver.get_model().eval(toZ3Expr(sel), true));
}

SMTExprRef Z3Solver::mkBoolImpl(const bool b) {
  return makeExprRef<Z3Expr>(SMTExprKind::BoolConst, &Context, mkBoolSort(),
                             Context.bool_val(b));
}

SMTExprRef Z3Solver::mkIntImpl(int64_t v) {
  return makeExprRef<Z3Expr>(SMTExprKind::IntConst, &Context, mkIntSort(),
                             Context.int_val(v));
}

SMTExprRef Z3Solver::mkIntImpl(const std::string &v) {
  return makeExprRef<Z3Expr>(SMTExprKind::IntConst, &Context, mkIntSort(),
                             Context.int_val(v.c_str()));
}

SMTExprRef Z3Solver::mkRealImpl(const std::string &v) {
  return makeExprRef<Z3Expr>(SMTExprKind::RealConst, &Context, mkRealSort(),
                             Context.real_val(v.c_str()));
}

SMTExprRef Z3Solver::mkRealImpl(int64_t v) {
  return makeExprRef<Z3Expr>(SMTExprKind::RealConst, &Context, mkRealSort(),
                             Context.real_val(v));
}

SMTExprRef Z3Solver::mkRealImpl(int64_t num, int64_t den) {
  return makeExprRef<Z3Expr>(SMTExprKind::RealConst, &Context, mkRealSort(),
                             Context.real_val(num, den));
}

SMTExprRef Z3Solver::mkBVFromDecImpl(const int64_t Int,
                                     const SMTSortRef &Sort) {
  return makeExprRef<Z3Expr>(SMTExprKind::BVConst, &Context, Sort,
                             Context.bv_val(Int, Sort->getWidth()));
}

SMTExprRef Z3Solver::mkBVFromBinImpl(const std::string &Int,
                                     const SMTSortRef &Sort) {
  std::size_t s = Sort->getWidth();
  bool *newInt = new bool[s];
  for (unsigned int i = 0; i < s; ++i)
    newInt[s - i - 1] = (Int[i] == '1');

  const SMTExprRef &bv = makeExprRef<Z3Expr>(SMTExprKind::BVConst, &Context,
                                             Sort, Context.bv_val(s, newInt));
  delete[] newInt;
  return bv;
}

SMTExprRef Z3Solver::mkSymbolImpl(const std::string &Name,
                                  const SMTSortRef &Sort) {
  if (Sort->isFunctionSort()) {
    z3::sort_vector Domain(Context);
    for (const auto &DomainSort : Sort->getDomainSorts())
      Domain.push_back(toSolverSort<Z3Sort>(*DomainSort).Sort);
    return makeExprRef<Z3Expr>(
        SMTExprKind::Symbol, &Context, Sort,
        Context.function(Name.c_str(), Domain,
                         toSolverSort<Z3Sort>(*Sort->getCodomainSort()).Sort));
  }
  return makeExprRef<Z3Expr>(
      SMTExprKind::Symbol, &Context, Sort,
      Context.constant(Name.c_str(), toSolverSort<Z3Sort>(*Sort).Sort));
}

SMTExprRef Z3Solver::mkFPFromBinImpl(const std::string &FP, unsigned EWidth) {
  const SMTExprRef &sgn = SMTSolverImpl::mkBVFromBin({FP[0]});
  const SMTExprRef &exp = SMTSolverImpl::mkBVFromBin(FP.substr(1, EWidth));
  const SMTExprRef &sig = SMTSolverImpl::mkBVFromBin(FP.substr(1 + EWidth));

  return makeExprRef<Z3Expr>(
      SMTExprKind::FPConst, &Context,
      mkFPSort(EWidth, FP.length() - EWidth - 1, FPEncoding::Native),
      z3::fpa_fp(toZ3Expr(sgn), toZ3Expr(exp), toZ3Expr(sig)));
}

SMTExprRef Z3Solver::mkRMImpl(const RM &R) {
  z3::expr e(Context);
  switch (R) {
  default:
    fatalError("Unsupported floating-point semantics.");
  case RM::ROUND_TO_EVEN:
    e = z3::to_expr(Context, Z3_mk_fpa_rne(Context));
    break;
  case RM::ROUND_TO_AWAY:
    e = z3::to_expr(Context, Z3_mk_fpa_rna(Context));
    break;
  case RM::ROUND_TO_PLUS_INF:
    e = z3::to_expr(Context, Z3_mk_fpa_rtp(Context));
    break;
  case RM::ROUND_TO_MINUS_INF:
    e = z3::to_expr(Context, Z3_mk_fpa_rtn(Context));
    break;
  case RM::ROUND_TO_ZERO:
    e = z3::to_expr(Context, Z3_mk_fpa_rtz(Context));
    break;
  }
  return makeExprRef<Z3Expr>(SMTExprKind::RMConst, &Context,
                             mkRMSort(FPEncoding::Native), e);
}

SMTExprRef Z3Solver::mkNaNImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  const SMTExprRef &theNaN =
      makeExprRef<Z3Expr>(SMTExprKind::FPConst, &Context, sort,
                          Context.fpa_nan(toSolverSort<Z3Sort>(*sort).Sort));

  return Sgn ? mkFPNeg(theNaN) : theNaN;
}

SMTExprRef Z3Solver::mkInfImpl(const bool Sgn, const unsigned ExpWidth,
                               const unsigned SigWidth) {
  const SMTSortRef &sort = mkFPSort(ExpWidth, SigWidth - 1, FPEncoding::Native);
  return makeExprRef<Z3Expr>(
      SMTExprKind::FPConst, &Context, sort,
      Context.fpa_inf(toSolverSort<Z3Sort>(*sort).Sort, Sgn));
}

SMTExprRef Z3Solver::mkBVToIEEEFPImpl(const SMTExprRef &Exp,
                                      const SMTSortRef &To) {
  return makeExprRef<Z3Expr>(
      SMTExprKind::BVToIEEEFP, &Context, To,
      toZ3Expr(Exp).mk_from_ieee_bv(toSolverSort<Z3Sort>(*To).Sort));
}

SMTExprRef Z3Solver::mkIEEEFPToBVImpl(const SMTExprRef &Exp) {
  const SMTSortRef &to =
      mkFPSort(Exp->Sort->getFPExponentWidth(),
               Exp->Sort->getFPSignificandWidth(), FPEncoding::BV);
  return makeExprRef<Z3Expr>(SMTExprKind::IEEEFPToBV, &Context, to,
                             toZ3Expr(Exp).mk_to_ieee_bv());
}

SMTExprRef Z3Solver::mkArrayConstImpl(const SMTSortRef &IndexSort,
                                      const SMTExprRef &InitValue) {
  const SMTSortRef &sort = mkArraySort(IndexSort, InitValue->Sort);
  return makeExprRef<Z3Expr>(
      SMTExprKind::ArrayConst, &Context, sort,
      z3::const_array(toSolverSort<Z3Sort>(*IndexSort).Sort,
                      toZ3Expr(InitValue)));
}

SMTExprRef Z3Solver::mkForallImpl(const std::vector<SMTExprRef> &Vars,
                                  const SMTExprRef &Body) {
  z3::expr_vector bound_vars(Context);
  for (auto const &Var : Vars)
    bound_vars.push_back(toZ3Expr(Var));
  return makeExprRef<Z3Expr>(SMTExprKind::Forall, &Context, mkBoolSort(),
                             z3::forall(bound_vars, toZ3Expr(Body)));
}

SMTExprRef Z3Solver::mkExistsImpl(const std::vector<SMTExprRef> &Vars,
                                  const SMTExprRef &Body) {
  z3::expr_vector bound_vars(Context);
  for (auto const &Var : Vars)
    bound_vars.push_back(toZ3Expr(Var));
  return makeExprRef<Z3Expr>(SMTExprKind::Exists, &Context, mkBoolSort(),
                             z3::exists(bound_vars, toZ3Expr(Body)));
}

checkResult Z3Solver::checkImpl() {
  z3::check_result res = Solver.check();
  if (res == z3::check_result::sat)
    return checkResult::SAT;

  if (res == z3::check_result::unsat)
    return checkResult::UNSAT;

  return checkResult::UNKNOWN;
}

void Z3Solver::resetImpl() { Solver.reset(); }

void Z3Solver::pushImpl(unsigned nscopes) {
  for (unsigned i = 0; i < nscopes; ++i)
    Solver.push();
}

void Z3Solver::popImpl(unsigned nscopes) { Solver.pop(nscopes); }

std::string Z3Solver::getSolverNameAndVersion() const {
  unsigned int major, minor, build, revision;
  Z3_get_version(&major, &minor, &build, &revision);
  return std::string("Z3 v")
      .append(std::to_string(major))
      .append(".")
      .append(std::to_string(minor))
      .append(".")
      .append(std::to_string(revision));
}

void Z3Solver::dumpImpl() {
  std::string Out;
  dumpImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void Z3Solver::dumpImpl(std::string &Out) {
  Out = Solver.to_smt2();
  Out += "\n";
}

void Z3Solver::dumpModelImpl() {
  std::string Out;
  dumpModelImpl(Out);
  std::fprintf(stderr, "%s", Out.c_str());
}

void Z3Solver::dumpModelImpl(std::string &Out) {
  Out = Solver.get_model().to_string();
  Out += "\n";
}

} // namespace camada

#endif
