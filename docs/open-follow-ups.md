# Open follow-ups

Work that is neither done nor rejected. Short by design — anything that
gets decided moves to `rejected-experiments.md` or into the code, and
anything that goes stale should be deleted rather than left here.

## Upstream reports we owe

### Z3 `mk_rem`: significand bits dropped with a subnormal divisor

Camada's `fp.rem` inherited this from Z3's `fpa2bv_converter.cpp`
(`mk_rem`) and has since fixed it locally. With a subnormal divisor the
normalized exponent difference reaches `(2^ebits-3) + (sbits-1)`, which
exceeds the `2^ebits-3` bits of shift headroom, so significand bits are
silently dropped.

Reproducer: `fp.rem(3.0e38f, 7.0e-39f)` returns the wrong value. Found by
cross-checking against the host CPU, where `std::remainder` is exact per
IEEE-754.

A second, smaller witness in binary16, found by cross-checking camada's BV
encoding against z3's native FP symbolically:

```
x = 0111100101100010   (44096.0)
y = 0000001111001100   (5.793571472167969e-05, subnormal)

exact (host remainder) -1.9550323486328125e-05   1000000101001000
camada BV              -1.9550323486328125e-05   exact
z3 native              -2.6464462280273438e-05   1000000110111100  (116 ulp out)
```

**The query must be symbolic.** Passing the operands as constants makes
every backend agree, because `propagate-values` folds them before
`fpa2bv` runs and the buggy bit-blaster never executes. Assert the inputs
through symbols, or use an explicit `(then fpa2bv simplify bit-blast smt)`
tactic.

Not yet reported upstream.

### Camada's BV-encoded FMA is wrong on subnormal inputs

**A correctness defect in shipped code**, inherited from Z3's
`fpa2bv_converter` along with the rest of camada's FP bit-blast.

Counterexample, 32-bit IEEE bit patterns:

```
x  10000000011110011011111101100111   (subnormal)
y  11111110111110000000000000000000
z  00111111001001011000111100001011

correct    01000000000111110101010100101111
camada BV  01000000000111110101010100101110   <- one ulp low
```

The correct value is confirmed three ways: exact rational arithmetic on
`x*y + z`, the host CPU's hardware `fmaf()`, and bitwuzla's native FP.

Z3 has the same bug. Running the same query through `z3` with an explicit
`(then fpa2bv simplify bit-blast smt)` tactic reproduces camada's wrong
answer bit-for-bit; Z3's *default* pipeline gets it right only because
`propagate-values` folds the constants and its rewriter evaluates the FMA
exactly, so the bit-blaster never runs on this input. A genuinely
symbolic FMA hits the bug there too.

This is the second subnormal-triggered defect found in that converter —
see the `mk_rem` entry above — which suggests those paths are
systematically under-tested upstream. Both deserve a report.

**Note what did not catch it.** The full 237-test suite passes with FMA's
operand normalization removed *entirely*, which should be impossible. The
suite has no symbolic subnormal FP arithmetic coverage; the bug surfaced
only from cross-checking the BV and native encodings against each other
over symbolic inputs. Extending the conformance fixtures to arithmetic
the way they already cover predicates would likely find siblings in add,
mul, div and the conversions — worth doing before or alongside the fix.

### MathSAT macOS packaging

The 5.6.17 macOS tarball ships `libmathsat.a` as a plain `ar` archive
whose members are fat Mach-O objects, a layout Apple's `ld` rejects.
5.6.16 shipped the correct `lipo` format. Camada pins macOS to 5.6.16
meanwhile — see `CAMADA_MATHSAT_MACOS_VERSION` in
`scripts/cmake/CamadaDependencies.cmake`, where the details live.

Not yet reported to FBK.

## Exploratory, no commitment

### `fp.rem` fast path for small divisors

The square-and-multiply remainder encoding is 30-100x faster than the
classic one overall, but regresses some fixed-divisor cases. A
data-dependent fast path for small `d` would recover those. Worth doing
only if a consumer hits the regression in practice; it adds a branch to
an encoding that is currently uniform.

### Lazy array symbol declaration

Deferring array *declarations* until an index is observed, to avoid
sending `QF_ABV` to a backend when the formula uses almost no array
reasoning.

**Do the cheap discriminator before writing any of it.** The 134s gap
that motivated this is not yet attributed to the declarations: the two
formulas are close in size (391 against 388 asserts), and six
declarations with two stores and no selects is very little array
reasoning. The plausible mechanism is that `QF_ABV` sends bitwuzla down a
different preprocessing path than pure `QF_BV`, not that the arrays are
hard.

Feed both dumped formulas to a standalone `bitwuzla`. If the gap
reproduces from files, the formula is the cause and the work pays off; if
it does not, the cost is in the incremental API path and eliding
declarations will not recover it. There is precedent for the latter from
the same investigation — a Z3 5.0.0 hang reproduced only through
`tactic(...).mk_solver()` and never from a file.

Minutes of work, and it decides whether the rest is worth doing.

### Rounder hints for FP addition

Camada's bit-blasted FP addition is far slower than bitwuzla's native
(SymFPU) one on queries that reason about the operation symbolically. The
technique SymFPU uses to win is worth recording precisely, because the
obvious guess is wrong.

**Not** the dual-path split. `add.h` contains `dualPathArithmeticAdd`,
which splits near and far cases — but bitwuzla never calls it. It calls
`symfpu::add`, reaching the single-path `arithmeticAdd`. Implementing the
dual-path version would be copying dead code.

What `arithmeticAdd` actually does is build a case table over the
exponent difference, predicting where the result exponent can land:

```
Case      A. max(l,r)+1   B. max(l,r)   C. max(l,r)-1   D. max(l,r)-k   E. zero
diff = 0      Y               Y
diff = 1      Y, sticky 0     Y, sticky 0
```

From that it derives five facts and passes them to the rounder as
`customRounderInfo`:

```cpp
prop noOverflow;   prop noUnderflow;   prop exact;
prop subnormalExact;   prop noSignificandOverflow;
```

The rounder then skips work it can prove unnecessary:

```cpp
prop incrementExponent(!known.noSignificandOverflow && incrementExponentNeeded);
prop overflow(!known.noOverflow && ITE(lateOverflow, true, earlyOverflow));
```

Camada's `round()` computes all of it unconditionally, with no channel
for a caller to say a case cannot arise.

**Why this is not being built now.** `round()` is shared by seven call
sites, so adding a hints parameter obliges every caller to derive its own
hints — and a wrong hint silently produces a wrong value rather than
failing loudly. That is the same failure shape as the FMA subnormal bug
found in this file, which argues for fixing correctness before adding a
new way to get it wrong. The measurement motivating it is also
adversarial (proving addition commutative), so the gain on ordinary
queries is unknown.

If it is built, the gate is ESBMC hard instances, and every hint needs a
symbolic cross-check against native FP the way the conformance fixtures
do — deriving a hint incorrectly is indistinguishable from a correct
encoding until it is wrong.

### Term introspection, walkers, translation

Parked until cross-solver term transfer becomes an actual goal. Camada
deliberately has no term introspection API: expressions are opaque
solver-owned handles, which is what keeps the layer thin. Adding walkers
or a term translator would be an architectural change, not a feature, and
should not happen speculatively.

## Where the rest went

Several planning documents were folded away once their work shipped:
the fixed-point plan, the array and tuple plans, the FP-encoding audit,
and the ESBMC correspondence. Decisions from them that outlived the
documents are either in `rejected-experiments.md` or in the API
documentation of the operation they constrain — the padding-bits scope
note on `mkFXPSort`, the domain restriction on `mkFXPExp`, the NaN
contract on `mkIEEEFPToBV`.
