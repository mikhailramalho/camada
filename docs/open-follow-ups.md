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

Not yet reported upstream.

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
