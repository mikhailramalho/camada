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

### Z3 `fpa2bv` FMA: sticky bit dropped, wrong rounding

Camada's copy is fixed (#145); Z3's is not, and we owe the report. It was
originally recorded here as a camada defect, inherited from Z3's
`fpa2bv_converter` along with the rest of the FP bit-blast.

FMA narrows its sum through one of two paths. The wider one discards an
extra bit but reused the narrower path's sticky, so that bit vanished,
the rounder saw a false exact tie and rounded to even — one ulp low on
subnormal operands. Reproduce with an explicit
`(then fpa2bv simplify bit-blast smt)` tactic; Z3's default pipeline
hides it because `propagate-values` folds constants before the
bit-blaster runs.

```
x  10000000011110011011111101100111   (subnormal)
y  11111110111110000000000000000000
z  00111111001001011000111100001011

correct    01000000000111110101010100101111
camada BV  01000000000111110101010100101110   <- one ulp low, BEFORE #145
```

(That camada column is the pre-#145 behaviour, kept because it is the
witness that identified the shared defect. Camada returns the correct
value now; Z3 still returns the wrong one.)

The correct value is confirmed three ways: exact rational arithmetic on
`x*y + z`, the host CPU's hardware `fmaf()`, and bitwuzla's native FP.
Z3 reproduces camada's pre-#145 answer bit-for-bit under the tactic
above.

A second, smaller witness in binary16, from cross-checking camada's BV
encoding against z3's native FP symbolically. This one is *not*
subnormal — it is a plain rounding error, so the defect is wider than the
subnormal path:

```
fma(x, y, x)  with  x = 984.0        0110001110110000
                    y = 3.546875     0100001100011000

exact x*y+x  4474.125
neighbours   4472 and 4476 (spacing 4), midpoint 4474.0
             exact is ABOVE the midpoint, so RNE gives 4476

camada BV    4476   0110110001011111   correct
z3 native    4472   0110110001011110   rounds the wrong way
```

As with `mk_rem`, the query must be symbolic: constant operands are folded
by `propagate-values` before `fpa2bv` runs, and z3 then answers correctly.

This is the second subnormal-triggered defect found in that converter —
see the `mk_rem` entry above — which suggests those paths are
systematically under-tested upstream. Both deserve a report.

Report both together with the `mk_rem` entry above: they are the second
and third defects found in the same converter, which suggests those paths
are systematically under-tested upstream. What did not catch them is
recorded under "Extend the conformance fixtures to arithmetic" below.

### MathSAT macOS packaging

The 5.6.17 macOS tarball ships `libmathsat.a` as a plain `ar` archive
whose members are fat Mach-O objects, a layout Apple's `ld` rejects.
5.6.16 shipped the correct `lipo` format. Camada pins macOS to 5.6.16
meanwhile — see `CAMADA_MATHSAT_MACOS_VERSION` in
`scripts/cmake/CamadaDependencies.cmake`, where the details live.

Not yet reported to FBK.

## Exploratory, no commitment

### Extend the conformance fixtures to arithmetic

The 237-test suite passes with FMA's operand normalization removed
*entirely*, which should be impossible. The fixtures cover predicates
symbolically but not arithmetic, so nothing cross-checks the BV and
native encodings against each other on subnormal inputs — which is the
only thing that caught #145.

Doing the same for add, mul, div and the conversions would likely find
siblings.

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
