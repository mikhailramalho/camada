# FP cross-check driver

Proves Camada's FP-over-BV encoding equivalent to a backend's native FP,
symbolically and exhaustively, one operation and rounding mode at a time.

```sh
cmake -S . -B build -DCAMADA_ENABLE_XCHECK=ON
cmake --build build --target camada-xcheck
./build/bin/camada-xcheck fma z3 5 10 RNE
```

`<op> <solver> [ebits] [sbits] [rm]`, defaulting to `5 10` (Float16). Omit
the rounding mode to run every applicable one.

## What it does

For one operation, backend and rounding mode it builds the operation twice
over the *same* symbolic input bits, once on the native FP sort and once on
the BV-encoded sort, and asserts the two results differ:

- **UNSAT** proves the encodings agree on every input. Not a sample.
- **SAT** is a counterexample, and the model prints the exact input bits.

Results are compared as IEEE bit patterns rather than with `fp.eq`, which
would equate `+0` and `-0` and make every NaN unequal, hiding exactly the
sign-of-zero and payload disagreements worth finding. NaN is the one place
bit equality is too strong, since the standard permits any payload, so
those cases are excluded and NaN *production* is checked separately.

## Why it is not a ctest case

A single cell can run for hours: the unpatched-Z3 FMA sweep took 41 minutes
for RNE and 86 for RTN at Float16, and cost grows sharply with format width.
This is a release-time audit, not something the suite can carry. The target
is off by default for the same reason.

Parallelise across cells rather than within them. One process per operation
and rounding mode is close to linear on a multi-core machine; Z3's
`sat.threads` measured *slower* here, since these are single UNSAT queries
where cube-and-conquer splitting costs more than it saves.

## What it has found

- Three Camada defects: the #144 subnormal multiply/divide regression, the
  `toIntegral` narrow-format guard, and an FMA sticky bit (#145).
- Two Z3 defects in `fpa2bv_converter`: the FMA `sticky_h2` reduction
  (Z3Prover/z3#10607, fixed upstream) and `fp.rem` significand truncation
  with a subnormal divisor (Z3Prover/z3#10608).

Both Z3 bugs need an explicit `(then fpa2bv simplify bit-blast smt)` tactic
to reproduce from a file: the default pipeline folds constant operands
before the bit-blaster runs. Driving the API symbolically, as this harness
does, hits them without the tactic.

## Caveats

`cvc5` rejects Float16 natively without `--fp-exp`, and Bitwuzla needs a
`--fpexp` build, so non-standard formats cross-check only against backends
that accept them (see issue #186). MathSAT routes `fp.rem` and `fp.fma`
through Camada's own bit-blast, so those cells would compare the encoding
against itself and are skipped.
