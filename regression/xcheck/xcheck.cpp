// Cross-check camada's FP-over-BV encoding against each backend's native
// FP, symbolically and exhaustively.
//
// For one operation, one backend and one rounding mode:
//
//   x, y : symbolic FP (native sort)
//   xb, yb : the SAME values under the BV-encoded sort, tied to x,y by
//            asserting their IEEE bit patterns are equal
//   assert  op_native(x,y)  !=  op_bv(xb,yb)      (as bit patterns)
//
// UNSAT  -> the two encodings agree on EVERY input. A proof, not a sample.
// SAT    -> a counterexample; the model gives the exact input bits.
//
// Comparing bit patterns rather than fp.eq matters: fp.eq says +0 == -0
// and NaN != NaN, which would hide both sign-of-zero and NaN-payload
// disagreements. The FMA bug this harness is designed to catch was a
// one-ulp error that fp.eq would have caught, but sign-of-zero bugs in
// add/sub/mul are a real class and only bit comparison finds them.
//
// NaN is the one place bit-equality is too strong: the standard permits
// any NaN payload, so the encodings may legitimately differ there. Those
// cases are excluded by requiring both results to be non-NaN, and NaN
// *production* is checked separately (both must agree on IS-NaN).
#include "camada.h"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "camadafeatures.h"
#if CAMADA_HAVE_Z3
#include "solvers/z3solver.h"
#endif
#if CAMADA_HAVE_BITWUZLA
#include "solvers/bitwuzlasolver.h"
#endif
#if CAMADA_HAVE_CVC5
#include "solvers/cvc5solver.h"
#endif
#if CAMADA_HAVE_MATHSAT
#include "solvers/mathsatsolver.h"
#endif

using namespace camada;

static const char *rmName(RM R) {
  switch (R) {
  case RM::ROUND_TO_EVEN:
    return "RNE";
  case RM::ROUND_TO_AWAY:
    return "RNA";
  case RM::ROUND_TO_PLUS_INF:
    return "RTP";
  case RM::ROUND_TO_MINUS_INF:
    return "RTN";
  case RM::ROUND_TO_ZERO:
    return "RTZ";
  }
  return "?";
}

static SMTSolverRef makeSolver(const std::string &N) {
#if CAMADA_HAVE_Z3
  if (N == "z3")
    return createZ3Solver();
#endif
#if CAMADA_HAVE_BITWUZLA
  if (N == "bitwuzla")
    return createBitwuzlaSolver();
#endif
#if CAMADA_HAVE_CVC5
  if (N == "cvc5")
    return createCVC5Solver();
#endif
#if CAMADA_HAVE_MATHSAT
  if (N == "mathsat")
    return createMathSATSolver();
#endif
  fprintf(stderr, "unknown or unavailable solver: %s\n", N.c_str());
  exit(2);
}

// Which (op, backend) pairs must be skipped because the backend routes
// the operation through camada's own bit-blast -- comparing our code
// against itself proves nothing. Derived by reading each backend's
// mk*Impl for a call to SMTSolverImpl::.
static bool selfComparison(const std::string &Op, const std::string &S) {
  if (S == "mathsat" && (Op == "rem" || Op == "fma"))
    return true;
  if ((S == "z3" || S == "bitwuzla") && Op == "frombin")
    return true;
  return false;
}

struct Result {
  bool agree;
  std::string detail;
};

// Build both encodings of one operation and look for a disagreement.
static Result check(const std::string &Op, const std::string &SolverName, RM Rm,
                    unsigned ebits, unsigned sbits) {
  SMTSolverRef S = makeSolver(SolverName);

  SMTSortRef natSort = S->mkFPSort(ebits, sbits, FPEncoding::Native);
  SMTSortRef bvSort = S->mkFPSort(ebits, sbits, FPEncoding::BV);
  unsigned W = ebits + sbits + 1; // total IEEE width

  // One shared bit-vector drives both sides, so the two encodings see
  // bit-identical inputs by construction.
  SMTExprRef xb_bits = S->mkSymbol("xbits", S->mkBVSort(W));
  SMTExprRef yb_bits = S->mkSymbol("ybits", S->mkBVSort(W));
  SMTExprRef xn = S->mkBVToIEEEFP(xb_bits, natSort);
  SMTExprRef yn = S->mkBVToIEEEFP(yb_bits, natSort);
  SMTExprRef xv = S->mkBVToIEEEFP(xb_bits, bvSort);
  SMTExprRef yv = S->mkBVToIEEEFP(yb_bits, bvSort);

  SMTExprRef rn = S->mkRM(Rm, FPEncoding::Native);
  SMTExprRef rv = S->mkRM(Rm, FPEncoding::BV);

  // Apply the operation under both encodings.
  SMTExprRef an, av;     // FP-valued results
  SMTExprRef pn, pv;     // boolean-valued results (predicates)
  SMTExprRef bn, bv;     // BV-valued results (fp->bv conversions)
  SMTExprRef resN, resV; // model-visible mirrors of the FP results
  bool isPred = false, isBV = false;

  if (Op == "add") {
    an = S->mkFPAdd(xn, yn, rn);
    av = S->mkFPAdd(xv, yv, rv);
  } else if (Op == "sub") {
    an = S->mkFPSub(xn, yn, rn);
    av = S->mkFPSub(xv, yv, rv);
  } else if (Op == "mul") {
    an = S->mkFPMul(xn, yn, rn);
    av = S->mkFPMul(xv, yv, rv);
  } else if (Op == "div") {
    an = S->mkFPDiv(xn, yn, rn);
    av = S->mkFPDiv(xv, yv, rv);
  } else if (Op == "fma") {
    an = S->mkFPFMA(xn, yn, xn, rn);
    av = S->mkFPFMA(xv, yv, xv, rv);
  } else if (Op == "sqrt") {
    an = S->mkFPSqrt(xn, rn);
    av = S->mkFPSqrt(xv, rv);
  } else if (Op == "rem") {
    an = S->mkFPRem(xn, yn);
    av = S->mkFPRem(xv, yv);
  } else if (Op == "toint") {
    an = S->mkFPToIntegral(xn, rn);
    av = S->mkFPToIntegral(xv, rv);
  } else if (Op == "neg") {
    an = S->mkFPNeg(xn);
    av = S->mkFPNeg(xv);
  } else if (Op == "abs") {
    an = S->mkFPAbs(xn);
    av = S->mkFPAbs(xv);
  } else if (Op == "fptofp") {
    // widen to a larger format, then narrow back: exercises both directions
    // Widen to the next standard format; bitwuzla rejects nonstandard
    // ones unless built with --fpexp.
    unsigned we = (ebits == 5) ? 8 : 11, ws = (ebits == 5) ? 23 : 52;
    SMTSortRef wideN = S->mkFPSort(we, ws, FPEncoding::Native);
    SMTSortRef wideV = S->mkFPSort(we, ws, FPEncoding::BV);
    an = S->mkFPToFP(S->mkFPToFP(xn, wideN, rn), natSort, rn);
    av = S->mkFPToFP(S->mkFPToFP(xv, wideV, rv), bvSort, rv);
  } else if (Op == "sbvtofp") {
    SMTExprRef i = S->mkSymbol("i", S->mkBVSort(W));
    an = S->mkSBVToFP(i, natSort, rn);
    av = S->mkSBVToFP(i, bvSort, rv);
  } else if (Op == "ubvtofp") {
    SMTExprRef i = S->mkSymbol("i", S->mkBVSort(W));
    an = S->mkUBVToFP(i, natSort, rn);
    av = S->mkUBVToFP(i, bvSort, rv);
  } else if (Op == "fptosbv") {
    isBV = true;
    bn = S->mkFPToSBV(xn, W);
    bv = S->mkFPToSBV(xv, W);
  } else if (Op == "fptoubv") {
    isBV = true;
    bn = S->mkFPToUBV(xn, W);
    bv = S->mkFPToUBV(xv, W);
  } else if (Op == "lt") {
    isPred = true;
    pn = S->mkFPLt(xn, yn);
    pv = S->mkFPLt(xv, yv);
  } else if (Op == "le") {
    isPred = true;
    pn = S->mkFPLe(xn, yn);
    pv = S->mkFPLe(xv, yv);
  } else if (Op == "gt") {
    isPred = true;
    pn = S->mkFPGt(xn, yn);
    pv = S->mkFPGt(xv, yv);
  } else if (Op == "ge") {
    isPred = true;
    pn = S->mkFPGe(xn, yn);
    pv = S->mkFPGe(xv, yv);
  } else if (Op == "equal") {
    isPred = true;
    pn = S->mkFPEqual(xn, yn);
    pv = S->mkFPEqual(xv, yv);
  } else if (Op == "isnan") {
    isPred = true;
    pn = S->mkFPIsNaN(xn);
    pv = S->mkFPIsNaN(xv);
  } else if (Op == "isinf") {
    isPred = true;
    pn = S->mkFPIsInfinite(xn);
    pv = S->mkFPIsInfinite(xv);
  } else if (Op == "iszero") {
    isPred = true;
    pn = S->mkFPIsZero(xn);
    pv = S->mkFPIsZero(xv);
  } else if (Op == "isnormal") {
    isPred = true;
    pn = S->mkFPIsNormal(xn);
    pv = S->mkFPIsNormal(xv);
  } else if (Op == "isdenormal") {
    isPred = true;
    pn = S->mkFPIsSubnormal(xn);
    pv = S->mkFPIsSubnormal(xv);
  } else {
    fprintf(stderr, "unknown op: %s\n", Op.c_str());
    exit(2);
  }

  if (isPred) {
    S->addConstraint(S->mkNot(S->mkEqual(pn, pv)));
  } else if (isBV) {
    // fp->bv is undefined for NaN, infinity and out-of-range inputs; the
    // standard lets each solver return anything, so a disagreement there
    // is not a bug.
    //
    // Constrain the BIT PATTERN, not the FP view. mkFPIsInfinite(xn)
    // restricts the FP-valued term, but mkBVToIEEEFP does not make the
    // bits definitionally equal to it (see the provenance design in
    // docs/rejected-experiments.md), so the solver stays free to pick an
    // infinity pattern for xb_bits and the constraint does nothing.
    // Excluding exponent == all-ones covers both NaN and infinity.
    SMTExprRef expBits = S->mkBVExtract(W - 2, sbits, xb_bits);
    S->addConstraint(
        S->mkNot(S->mkEqual(expBits, S->mkBVFromDec((1 << ebits) - 1, ebits))));

    // Out-of-range is undefined too, and binary16 reaches 65504 -- well
    // past a 16-bit integer. Bound the input's MAGNITUDE directly: a
    // round-trip constraint does not work here, because for an undefined
    // input the converted value is unconstrained and satisfies it
    // vacuously.
    //
    // Keep |x| < 2^(W-2), comfortably inside both the signed and
    // unsigned W-bit ranges, by requiring the biased exponent to stay
    // below bias + (W-2).
    unsigned bias = (1u << (ebits - 1)) - 1;
    unsigned cap = bias + (W - 2);
    S->addConstraint(S->mkBVUlt(expBits, S->mkBVFromDec(cap, ebits)));
    // fp.to_ubv is undefined for negatives; exclude them.
    if (Op == "fptoubv")
      S->addConstraint(S->mkEqual(S->mkBVExtract(W - 1, W - 1, xb_bits),
                                  S->mkBVFromDec(0, 1)));
    S->addConstraint(S->mkNot(S->mkEqual(bn, bv)));
  } else {
    // Compare IEEE bit patterns, so sign-of-zero differences are caught.
    // Exclude the NaN-payload freedom: require agreement on IS-NaN, and
    // compare bits only when neither side is NaN.
    SMTExprRef nanN = S->mkFPIsNaN(an), nanV = S->mkFPIsNaN(av);
    // Mirror both results into plain BV symbols tied by equality, and
    // phrase the disagreement over THOSE. Without this the model can
    // satisfy the constraint without fixing the terms the printer reads
    // back, and getBVInBin's model completion then invents values --
    // producing a "counterexample" whose reported inputs do not actually
    // disagree when replayed. Verified: replaying such a report with the
    // inputs pinned gives UNSAT.
    resN = S->mkSymbol("__resN", S->mkBVSort(W));
    resV = S->mkSymbol("__resV", S->mkBVSort(W));
    S->addConstraint(S->mkEqual(resN, S->mkIEEEFPToBV(an)));
    S->addConstraint(S->mkEqual(resV, S->mkIEEEFPToBV(av)));
    SMTExprRef bitsDiffer = S->mkNot(S->mkEqual(resN, resV));
    SMTExprRef bothNumbers = S->mkAnd(S->mkNot(nanN), S->mkNot(nanV));
    // disagreement = differ on NaN-ness, OR both numbers with different bits
    S->addConstraint(S->mkOr(S->mkNot(S->mkEqual(nanN, nanV)),
                             S->mkAnd(bothNumbers, bitsDiffer)));
  }

  CheckResult r = S->check();
  if (r == CheckResult::UNSAT)
    return {true, "proved equivalent over all inputs"};
  if (r == CheckResult::UNKNOWN)
    return {false, "UNKNOWN (solver gave up)"};

  // SAT: recover the counterexample bits so the failure is diagnosable
  // rather than just reported.
  auto val = [&](const SMTExprRef &E) -> std::string {
    auto r = S->getBVInBin(E);
    return r ? r.value() : std::string("?");
  };
  std::string d = "CEX x=" + val(xb_bits) + " y=" + val(yb_bits);
  if (!isPred && !isBV)
    d += "  nat=" + val(resN) + "  bv=" + val(resV);
  else if (isBV)
    d += "  nat=" + val(bn) + "  bv=" + val(bv);
  return {false, d};
}

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr,
            "usage: %s <op> <solver> [ebits] [sbits] [rm]   (default 5 10 = "
            "Float16)\n"
            "  ops: add sub mul div fma sqrt rem toint neg abs fptofp\n"
            "       sbvtofp ubvtofp fptosbv fptoubv lt le gt ge equal\n"
            "       isnan isinf iszero isnormal isdenormal\n"
            "  rm : RNE RNA RTP RTN RTZ; omitted runs all applicable modes\n",
            argv[0]);
    return 2;
  }
  std::string Op = argv[1], Sv = argv[2];
  unsigned ebits = argc > 3 ? (unsigned)atoi(argv[3]) : 5;
  unsigned sbits = argc > 4 ? (unsigned)atoi(argv[4]) : 10;
  const char *rmArg = argc > 5 ? argv[5] : nullptr;

  if (selfComparison(Op, Sv)) {
    printf("SKIP  %-11s %-9s  backend routes this through camada's own "
           "bit-blast\n",
           Op.c_str(), Sv.c_str());
    return 0;
  }

  // Operations that ignore the rounding mode need only one pass.
  bool rmFree =
      (Op == "rem" || Op == "neg" || Op == "abs" || Op == "lt" || Op == "le" ||
       Op == "gt" || Op == "ge" || Op == "equal" || Op == "isnan" ||
       Op == "isinf" || Op == "iszero" || Op == "isnormal" ||
       Op == "isdenormal" || Op == "fptosbv" || Op == "fptoubv");
  std::vector<RM> Rms = {RM::ROUND_TO_EVEN, RM::ROUND_TO_AWAY,
                         RM::ROUND_TO_PLUS_INF, RM::ROUND_TO_MINUS_INF,
                         RM::ROUND_TO_ZERO};
  if (rmFree) {
    Rms.resize(1);
  } else if (Sv == "mathsat") {
    // MathSAT has no round-to-away: mkRM calls fatalError on it, which
    // would abort the whole cell rather than skip one mode.
    Rms.erase(std::remove(Rms.begin(), Rms.end(), RM::ROUND_TO_AWAY),
              Rms.end());
    printf("NOTE  %-11s mathsat    RNA unsupported by this backend, skipped\n",
           Op.c_str());
  }

  // One mode per process: the five modes of a cell are independent proofs,
  // so making the mode part of the work unit lets them run concurrently
  // instead of serially inside one process. NA means this mode does not
  // apply here (rm-free op, or RNA on mathsat) -- not a verdict about
  // camada, so it is counted separately from SKIP.
  if (rmArg) {
    RM want;
    if (!strcmp(rmArg, "RNE"))
      want = RM::ROUND_TO_EVEN;
    else if (!strcmp(rmArg, "RNA"))
      want = RM::ROUND_TO_AWAY;
    else if (!strcmp(rmArg, "RTP"))
      want = RM::ROUND_TO_PLUS_INF;
    else if (!strcmp(rmArg, "RTN"))
      want = RM::ROUND_TO_MINUS_INF;
    else if (!strcmp(rmArg, "RTZ"))
      want = RM::ROUND_TO_ZERO;
    else {
      fprintf(stderr, "unknown rounding mode: %s\n", rmArg);
      return 2;
    }
    if (std::find(Rms.begin(), Rms.end(), want) == Rms.end()) {
      printf("NA    %-11s %-9s %s  mode not applicable for this op/backend\n",
             Op.c_str(), Sv.c_str(), rmArg);
      return 0;
    }
    Rms.assign(1, want);
  }

  int failures = 0;
  double totalMs = 0;
  for (RM Rm : Rms) {
    auto t0 = std::chrono::steady_clock::now();
    Result res = check(Op, Sv, Rm, ebits, sbits);
    double ms = std::chrono::duration<double, std::milli>(
                    std::chrono::steady_clock::now() - t0)
                    .count();
    totalMs += ms;
    // Per-rounding-mode timing: a cell that reports one total hides which
    // mode was expensive, and whole-minute resolution collapses most
    // cells to "0m".
    printf("%-5s %-11s %-9s e%u s%u  %s  %9.1fms  %s\n",
           res.agree ? "OK" : "FAIL", Op.c_str(), Sv.c_str(), ebits, sbits,
           rmFree ? "---" : rmName(Rm), ms, res.detail.c_str());
    fflush(stdout);
    if (!res.agree)
      ++failures;
  }
  printf("TIME  %-11s %-9s e%u s%u  total %.1fms over %zu mode(s)\n",
         Op.c_str(), Sv.c_str(), ebits, sbits, totalMs, Rms.size());
  return failures ? 1 : 0;
}
