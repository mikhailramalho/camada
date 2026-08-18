# FP-over-BV vs native FP: measured cost

Camada bit-blasts floating point through bit-vectors (`FPEncoding::BV`).
Bitwuzla can also solve FP natively (SymFPU). This file records how the
two compare, and — more importantly — how to measure that without
fooling yourself.

## The methodology rule

**Every operation must be given the same query shape.**

An earlier comparison gave each operation whatever query suited it, and
addition alone drew commutativity (`x+y == y+x`). That produced a
reported 1880x slowdown for `add` which was entirely an artifact:
commutativity measures the difficulty of proving two mirror-image
circuits equivalent, not the cost of the encoding. Holding the shape
fixed, add is ordinary.

A second trap: the shape must actually force the operation to be
reasoned about. `res == z && res != z` is UNSAT propositionally, without
the solver ever looking at `res` — visible as a suspiciously flat native
column of ~0.4 ms for every operation.

The two shapes below are uniform across operations and both force real
work:

- **model (SAT)** — the result is constrained to be finite and nonzero
  (or the predicate asserted true), so the solver must invert the
  operation to produce a witness.
- **determinism (UNSAT)** — the operation is built twice over the same
  operands *in the same order*, and the two results asserted to differ.
  Same operand order both times, so no operation receives an
  algebraic-symmetry query the others do not.

## Results

f32, bitwuzla, 10 repetitions per cell, ratio = BV / native. Measured on
master with #144 (mul/div pre-normalisation), #145 (FMA sticky fix) and
#146 (fptoFP pre-normalisation) applied. Two independent runs agreed
within noise.

| op | model | determinism |
|---|---|---|
| `rem` | **0.44x** | **0.49x** |
| `ieeebv-roundtrip` | **0.28x** | **0.17x** |
| `abs` | **0.55x** | 1.33x |
| `neg` | **0.59x** | 1.29x |
| `equal` | **0.54x** | 1.40x |
| `isZero` / `isNormal` / `isDenormal` | **0.48-0.52x** | 1.50x |
| `lt` / `le` / `gt` / `ge` | **0.64-0.89x** | 2.00-2.50x |
| `isNaN` / `isInfinite` | 1.17-1.33x | 1.50x |
| `fptosbv` / `fptoubv` | 1.49x | 5.75-6.00x |
| `add` | 2.03x | 3.74x |
| `sub` | 2.14x | 3.77x |
| `fptofp` (widen) | 2.72x | 2.62x |
| `div` | 2.88x | 3.71x |
| `mul` | 3.15x | 4.82x |
| `toIntegral` | 3.33x | 4.09x |
| `fma` | 2.10x | 5.38x |
| `fptofp` (narrow) | 4.09x | 6.08x |
| `ubvtofp` | 4.60x | 4.52x |
| `sbvtofp` | 4.88x | 5.02x |
| `sqrt` | **12.98x** | **13.02x** |

## What this says

**BV wins outright on `rem` and the IEEE bit round-trip.** `rem` is
2.0-2.3x *faster* than native — camada's square-and-multiply beats
SymFPU's linear chain of ~276 divide steps (f32). ESBMC observed this
independently. The round-trip is 3-6x faster because in the BV encoding
it is the identity: the value is already a bit-vector.

**Predicates and comparisons are at or better than parity** on the model
shape, and only mildly behind on determinism where native gets a cheap
structural refutation.

**The arithmetic core sits at 2-5x.** No operation in that group is an
outlier; add, sub, mul, div, fma and toIntegral are all within a factor
of ~2 of each other. This is the honest cost of bit-blasting.

**`sqrt` at ~13x is the real outlier**, stable across both shapes and
across f32/f64. It was investigated and is **not** cheaply fixable: see
`rejected-experiments.md`. The short version is that native emits ~150
bytes for every operation because it hands the term to bitwuzla whole,
where SymFPU expands it inside the word-blaster; the gap is structural to
being a wrapper. Two attempts to close it (narrowing the loop's add,
adding sqrt rounder hints) both failed, and removing the rounder entirely
made a 30% smaller formula solve 48% *slower*.

The conversions (`sbvtofp`, `ubvtofp`, `fptofp` narrow) at 4-6x are the
second tier. Note their normalisation is *load-bearing* — the
significand is read from fixed bit positions — so the trick that helped
mul/div/fptofp (#144, #146) does not apply; removing it fails the
suite.

## Reproducing

The harness is not checked in; it is ~90 lines against the public API.
Build a case table of `(name, lambda, is_predicate)`, then for each
operation and each encoding run both shapes above. The essentials:

```cpp
for (auto V : {X, Y}) {              // exclude NaN/inf so specials
  S->addConstraint(S->mkNot(S->mkFPIsNaN(V)));       // cannot discharge
  S->addConstraint(S->mkNot(S->mkFPIsInfinite(V)));  // the query trivially
}
// determinism shape:
SMTExprRef a = build(X, Y), b = build(X, Y);
S->addConstraint(S->mkNot(S->mkFPEqual(a, b)));   // mkEqual if BV-valued
```

`mkFPtoSBV`/`mkFPtoUBV` return bit-vectors, so they need `mkEqual`;
passing them to `mkFPEqual` aborts.

Camada has no `mkFPMin`/`mkFPMax`/`mkFPIsNegative`/`mkFPIsPositive` —
earlier "30 operation" counts included operations that do not exist.

**Do not substitute formula size for solve time.** `dump()` makes it
tempting, and emitted size does correlate loosely across operations, but
the sqrt investigation produced a direct counterexample within a single
operation: bypassing the rounder cut the formula from 26112 to 18356
bytes and made it solve 48% slower. This is the same trap as the
node-count gate in `rejected-experiments.md`.
