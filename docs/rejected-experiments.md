# Rejected and parked experiments

Work that was built, measured, and deliberately not merged. Each entry
records what was tried, what the evidence said, and why the decision went
the way it did — so the idea is not rediscovered and re-implemented from
scratch, and so a future proposal has to beat the measurement rather than
repeat it.

Where a branch has been deleted its tip commit is given, so the work can
be recovered with `git checkout <sha>` while the object survives in the
repository. The entry is the artifact worth keeping, not the code.

---

## Encoding performance

### Rounder restructuring (A3/A4) — REJECTED on measurement

Branch: `perf/rounder-structure` (deleted; tip was `4f0b5f6`)

Two changes to the floating-point rounder: computing the overflow test
from the pre-increment operands, and folding the rounder's constant
chains while sharing the `Exp - lz` subterm. Both are exact node-count
reductions — strictly less work for the solver on paper.

ESBMC measured them on hard instances and **both regressed**. The
reduction in nodes did not translate into a reduction in solve time,
presumably because the removed structure was doing useful propagation.

The general lesson, which now governs all encoding changes: **node count
is not a proxy for solve time**, and mechanism arguments ("this is
obviously less work") are unreliable in both directions. See the
hard-instance gate below.

### Caching and interning layers — SIX ATTEMPTS, all REVERTED

Benchmarked against a pinned baseline with repeated-run median comparison
(`scripts/compare-bench.py`), and each reverted:

1. Broad hash-based expression interning (unary/binary/ternary caches,
   extract/extend caches)
2. Broad generic bit-vector constant caching
3. Generic `unpack()` caching
4. Solver-level width-keyed exponent constant caches
5. Eager common-singleton initialization
6. FP special-value cache variants beyond the one kept

They failed for one recurring reason: **the lookup and miss overhead
exceeded the construction work avoided.** Camada's expression
construction is already cheap, so a cache has to hit very often to pay
for the hash of every miss. Miss-heavy workloads — varied constants,
array-store chains — paid the cost without the benefit, and FP-heavy
paths measurably worsened even where isolated microcases improved.
Attempt 4 made `unpack()` and its callers *much* slower.

What did work instead was narrower: solver-owned expression and sort
storage, sort interning, conservative (not broad) expression interning,
and dedicated singleton paths for the FP special values. The pattern is
that a targeted cache on a known-hot, high-hit-rate path pays, and a
general one does not.

Do not retry these without a new profiler signal or a materially
different strategy.

### SymFPU techniques that do not transfer — REJECTED on inspection

Camada's FP bit-blast was compared against bitwuzla's native FP (SymFPU)
across all 30 comparable operations. Two changes landed from that
comparison — multiply and divide stopped pre-normalizing their operands,
worth -35% and -28% — and three candidates were examined and dropped.

**One-bit conditional shift in divide.** SymFPU corrects its quotient
with `conditionalLeftShiftOne` instead of a variable-amount shift, which
bit-blasts into a barrel shifter. It can do this *because* it normalizes
its operands first, which bounds the quotient to [0.5, 2) and so its
leading-zero count to 0 or 1. Camada no longer normalizes, so the
quotient can be arbitrarily small — a subnormal dividend over a large
divisor needs up to `sbits` of shift — and the variable shift is
load-bearing.

The two techniques are **alternatives, not complements**: normalize and
get cheap fixed shifts, or skip normalization and pay for one variable
shift. Measurement favours our side of that trade (divide 23.2ms to
16.3ms), but it means the SymFPU shift trick can never be layered on top.

**Folding normalization into the exponent add.** SymFPU's
`expandingAddWithCarryIn(le, re, topBitSet)` looked like a cheaper way to
combine exponents than our subtract-then-adjust. Once operands are
unpacked unnormalized the leading-zero counts are provably zero, so our
subtractions were simply dead — removing them is bookkeeping, not an
optimization, and produced no measurable change. Recorded so the idea is
not revisited expecting a gain.

**Dual-path addition.** `add.h` defines `dualPathArithmeticAdd`, which
splits the near and far cases. Bitwuzla does not call it: `symfpu::add`
reaches the single-path `arithmeticAdd`. Copying it would be copying dead
code. The technique bitwuzla actually uses for addition is a rounder-hint
protocol, recorded below — it was later rejected outright once the
measurement motivating it turned out to be an artifact.

**The architectural difference underneath all of this**, which no
individual technique captures: SymFPU's unpacked float carries `nan`,
`inf` and `zero` as separate boolean fields, so its arithmetic never
rebuilds a value's classification. Camada keeps values packed as IEEE
bit-vectors and re-derives classification at every operation — our
multiply builds 21 special-case terms where SymFPU's builds 5.

That choice is why the measured results split so cleanly: every
classification predicate is *faster* under camada's encoding (`isNaN`
0.39x, `isZero` 0.35x, and the IEEE bit round-trip 0.15x, since under BV
it is the identity), while everything that computes a value is slower.
Adopting SymFPU's representation would be a rewrite of `camadafp.cpp`
that trades those wins away — a different design, not an improvement.

### Relational `bvurem` for `fp.rem` (B2) — REJECTED on anti-foldability

No branch retained; abandoned during development.

The idea was to encode remainder relationally — introduce a fresh
variable `q` and assert `x = q*y + r` with the appropriate bounds —
instead of computing it. Relational encodings are usually smaller.

It made the regression suite go from 56s to over 10 minutes. The cause is
that **camada has no rewriter layer**: a relational encoding introduces a
fresh variable whose identity the solver must derive, so a remainder over
two constants no longer constant-folds. Every concrete `fp.rem` in a
formula turned into real solver work.

This retroactively killed a sketched relational square root for the same
reason. Guess-and-check encodings are a poor fit for a layer that relies
on constant folding for its cheap cases.

### What did survive the gate

For contrast, since the gate is not a blanket "no": the leading-zero
count tree (#127), the FMA sticky-bit fix (#128), and the Ackermann
select memo/fold (#129) all landed. Each improved camada's single
implementation for every consumer, added no option, and won on hard
instances — the LZC tree despite toy benchmarks suggesting otherwise.

---

## Scope: features that belong to the consumer

### Eager read-over-write scalarization (EagerRoW) — REJECTED on scope

Branch: `feat/eager-row-arrays` (deleted; tip was `c35007f`)

Implemented, reviewed, and working. It scalarizes array reads eagerly,
which helps workloads with many symbolic loop iterations over small
arrays (ESBMC's `dict65` case).

It was rejected anyway, and the reasoning is the load-bearing part:
**camada is a lightweight layer implementing the bare minimum for SMT
solvers to work behind one API.** A feature belongs here only if it fills
a *capability gap* — "this backend cannot do X". Ackermann arrays, the
FP-over-BV encoding, lazy constant arrays and tuple lowering all qualify.
EagerRoW does not: every backend can already do it, just slower on some
formulas. Deciding when it pays needs workload knowledge — SSA
discipline, reachability, type bounds — that camada cannot see and the
consumer already has.

It was briefly folded into a `StoreLowering` knob over `{Native,
Ackermann}` before that too was rejected. **Configuration knobs are a
scope smell**: they push a decision onto the user that the layer should
not be making at all.

The same reasoning sent several sibling ideas to the consumer side:
bounded array explosion, lazy array symbol declaration, and address-space
store deferral.

### `SolverConfig` — PARKED for the same reason

Branch: `feat/solver-config`, PR #123 (open)

Consolidates creation-time options into a config object. Parked as a
knob-shaped change; worth closing unless a capability argument appears.

---

## Design alternatives that lost to a specific case

### `mkIEEEFPToBV` without the provenance rewrite — SUPERSEDED

Branch: `experiment/uf-ieeebv-no-shadow` (deleted; tip was `f699078`)

`fp.to_ieee_bv` is underspecified for NaN: the FP sort has one NaN value
while the bit encoding has many NaN patterns, so no function out of the
sort can say which pattern produced a given NaN, and a backend may answer
with any of them. Two mechanisms address different halves of that.

**#125** returns the exact bits where camada can *prove* them — the term
came from `mkBVToIEEEFP`, an FP constant, or a top-level equality tying
it to one. That makes round-trips bit-exact, which is what a byte-level
memory model needs. The cost is that the result depends on the term's
provenance rather than only on the FP value.

**#126** fixed a soundness gap #125 did not reach: two FP terms asserted
*equal* were each given their own unconstrained bit-vector symbol, so a
sound program's assertion became violable on bitwuzla under native FP.
Emulating the primitive as a per-sort uninterpreted function, tied by
`to_fp(fn(x)) == x`, makes functional congruence force value-equal terms
to report equal bits.

This branch was the exploratory version of #126, written the same day.
It differs from what shipped in one respect: it **removes** the #125
provenance rewrite instead of layering on top of it, trading bit-exact
round-trips for functional consistency alone. Master keeps both, so
round-trips stay exact *and* value-equal terms agree. The two mechanisms
answer different questions and the shipped design needs both.

#### The failing case, since it explains why one mechanism is not enough

Found on ESBMC's `camada` branch by `regression/python/github_3719_4-nondet`.
A program writes a float's bytes into a container and reads them back; the
read saw a different pattern than was written, and the assertion failed on
a model that cannot occur in C.

The formula asserted `y == list_elem` *before* either term had any tie to
a bit-vector, then later tied each one separately:

```
(assert (= y list_elem))                          ; line 220
(assert (= list_elem ((_ to_fp 11 53) ieeebv0)))  ; line 248
(assert (= y         ((_ to_fp 11 53) ieeebv1)))  ; line 336
```

Nothing forces `ieeebv0 == ieeebv1` — in the dump they appear in 10 and 12
asserts respectively, and **zero** asserts mention both. For a non-NaN
value that is harmless, since `to_fp` is injective there and equal floats
force equal bits. At NaN `to_fp` is many-to-one, so a model can satisfy
all three constraints with two different payloads for one float value.

#125 could not cover it because its seeding is **forward-only**: a shadow
link is recorded when exactly one side of an equality is already shadowed,
and at line 220 neither side is. Each later `mkIEEEFPToBV` then
legitimately mints its own symbol. Nothing is inconsistent per term — the
memo does return the cached symbol for a repeated call — the gap is that
the equality arrived before either side had provenance.

The alternatives considered were a union-find over asserted FP equalities
(fixes the general case, but more invasive and needs the same scope
discipline the shadow levels already implement) and leaving it documented
with callers using `FPEncoding::BV` when they need bit-exact floats. #126's
uninterpreted function was chosen instead: congruence gives the guarantee
without tracking provenance at all.

Scope note: this only ever affected the fresh-symbol backends — bitwuzla,
cvc5 and the SMT-LIB pipeline. Z3 and MathSAT use native fp->bv
primitives, so repeated reads of one term are the same function
application and agree by construction, even where the NaN result is
unspecified.

### Packed tuple representation — REJECTED on expressiveness

Considered while designing the tuple subsystem (#102): represent a tuple
as a single `Array<Idx, BV>` with the fields bit-concatenated into one
payload, instead of decomposing into a bundle of per-field arrays.

It only works when every leaf is a fixed-width scalar. It cannot
represent tuple fields that are themselves arrays, which camada already
supported and ESBMC's type universe includes. The usage pattern pointed
the same way: ESBMC's hot tuple shape is a two- or three-field pointer
struct under fine-grained field project and update, which decomposition
serves directly and a packed payload would force to extract and reassemble
on every access.

Tuple-typed *index* sorts remain rejected for the same expressiveness
reason, independently of the representation choice.

### Bit-exact FP storage sort — DECLINED, contract delivered instead

ESBMC asked for an FP-typed value whose *storage* is bit-exact — byte
reads and writes recover the pattern written, NaN payloads included —
while its *operations* stay native FP. The motivation was byte-addressable
memory: an FP value written to memory and read back must return the same
bits, which `mkIEEEFPToBV` does not guarantee at NaN.

Two designs were on the table. The first was extending the shadow
mechanism so `mkIEEEFPToBV` returns provenance-exact bits everywhere; it
was declined because it makes the operation stop being a function of the
FP value at NaN, which is a real semantic cost, and because measurements
showed the consumer-side fix was cheap. The second — a dedicated storage
sort camada would represent per backend — was declined as knowledge-holder
territory: only ESBMC knows its own memory model.

What camada owes, and shipped, is the **contract**: `mkIEEEFPToBV`'s
documentation now states plainly that the result is NaN-payload
unspecified, that round-tripping is not the identity, and where the
provenance rewrite does and does not reach — so a caller building
byte-level memory discovers the hazard from the API rather than from a
wrong SV-COMP verdict.

The split follows the boundary rule: bit-exact byte-addressable memory
belongs to the knowledge holder, while the FP-encoding contract is
theory-internal and camada-owned.

---

## Scope: where the razor does *not* cut

Two refinements were needed before the rule above stopped
over-rejecting things.

**Implementation quality is in scope.** The razor cuts *knobs*, not
improvements. "Camada's bit-blast is structurally bad" is a camada bug
and fixing it belongs here, even when the motivation is purely
performance. "The backend's encoding could be swapped for a
workload-dependent alternative" is a consumer feature. #127, #128 and
#129 are all the first kind.

**Inside a camada-owned theory there is no backend.** "It composes from
the public API" only exiles a feature when a backend sits underneath it.
For fixed-point and FP-over-BV, camada *is* the theory, so completeness
of semantics-bearing operations is itself the capability. The decisive
tests are whether correct semantics need encoder internals the
composition cannot reach — single rounding needs the scale folded into
the exponent *before* the rounding step, and composition double-rounds on
subnormal underflow — and whether the composition carries width or
ordering traps that produce almost-right answers.

That is what justified `mkFXPToFP`/`mkFPToFXP`, `roundfx`, and the
correctly-rounded `sqrtfx` and `expfx`, none of which a consumer could
have assembled correctly from the public surface.

---

## Deferred work with a recorded design

### Nested arrays for STP (#119) — SHELVED

The design (flatten the multidimensional array and partition it) is
written up in the issue. Judged too much work for the benefit, since it
serves one backend. Phase 1 alone covers `array_of(array_of(v))`, which
is the shape that actually appears.

### Ackermannized UF for STP — NOTED, not built

Same shape of trade-off as #119: real work, one backend.

### `roundfx` and FXP↔FP conversions — later BUILT

Both were parked as "camada-owned but blocked on demand and on
oracle-pinned semantics", then unblocked when ESBMC asked for them and
the execution oracle could measure the answers. Recorded here because the
*sequencing* is the point: the rulings were made before the work, and the
work waited for evidence rather than starting on recalled semantics.

---

### Rounder hints for FP addition — REJECTED, premise was a measurement artifact

Proposed after camada's bit-blasted FP addition appeared far slower than
bitwuzla's native (SymFPU) one. It is not — see the measurement below.
The SymFPU technique is recorded anyway, because the obvious guess about
what it does is wrong and someone will look again.

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

**Why this is not being built: the motivating number was an artifact.**
The "add is 1880x slower" figure came from a benchmark that gave each
operation a different query shape, and add alone drew commutativity
(`x+y == y+x`). Holding the operation fixed and varying only the shape:

| shape | add | mul |
|---|---|---|
| single op, `isNaN` | 3.8x | 4.6x |
| result equated to a free symbol | 6.8x | 7.0x |
| commutativity | **1720x** | 8.1x |

On ordinary query shapes add is indistinguishable from multiply, and
slightly better. There is no add-specific rounder deficit.

The blowup is the *swap network*, not the rounder. `addCore` orders its
operands by exponent, so `x+y` and `y+x` bit-blast into mirror-image
circuits, and the solver must prove the swap symmetric before anything
downstream cancels. Multiply takes its operands symmetrically and has no
such network. Constraining both operands to one binade — which pins
`exp_delta` to 0 and makes the alignment shift constant — drops the
commutativity query from 9113 ms to 1251 ms, a 7.3x collapse. That is
where the cost lives.

`round()`'s share of a single add is roughly 70% (`toIntegral`, which is
round-dominated with almost no front end, costs 12.4 ms against add's
17.6 ms) — but since add is already at parity with multiply, shrinking
the rounder is a general FP optimisation, not an add fix, and would have
to be justified on its own.

Against that, the cost stays what it was: `round()` is shared by seven
call sites, so a hints parameter obliges every caller to derive its own
hints, and a wrong hint silently produces a wrong value rather than
failing loudly — the same failure shape as the FMA subnormal bug in this
file.

If anyone revisits this, the gate is ESBMC hard instances, every hint
needs a symbolic cross-check against native FP the way the conformance
fixtures do, and the benchmark must hold the query shape fixed across
operations.

Full fixed-shape numbers for every FP operation are in
`docs/fp-bv-vs-native.md`. On that measurement the remaining outlier is
`sqrt` (~13x), not `add`.

### Narrowing the sqrt loop / sqrt rounder hints — REJECTED on measurement

Investigated because `sqrt` is the last FP-over-BV outlier (~13-14x
native, stable across query shapes and across f32/f64).

**SymFPU's sqrt is not the reason it wins.** `core/sqrt.h` calls
`fixedPointSqrt`, whose loop does a full `expandingMultiply(candidate,
candidate)` every iteration — strictly more work per step than camada's
restoring loop (one add, one subtract). Its own comment concedes "the
default algorithm given here isn't a great one". Bitwuzla does not
override it (`symfpu::sqrt` is called directly from `word_blaster.cpp`).

**What actually differs is where the expansion happens.** Dumping one
`fp.sqrt` query:

| encoding | emitted |
|---|---|
| BV | 26112 bytes |
| native | 114 bytes |

Native emits ~150 bytes for *every* FP operation — it hands `fp.sqrt` to
bitwuzla as a single term and SymFPU expands it inside the word-blaster,
subject to bitwuzla's own rewriting before the SAT solver sees it. That
is a structural property of being an external wrapper, not an encoding
defect we can close.

**Two things were tried and both failed:**

1. *Narrowing the per-iteration add.* `S` in the loop is provably
   constant (dumping it shows no symbols) with a single set bit, and `Q`
   accumulates top-down, so `Q`'s low bits are structurally zero.
   Splicing the add down to the live prefix made the formula **larger**
   (26112 -> 29235 bytes): the extract/concat scaffolding costs more than
   the zero bits, which bitwuzla was already folding.

2. *Rounder hints.* SymFPU passes `customRounderInfo(noOverflow=true,
   noUnderflow=true, exact=false, subnormalExact=true, ...)` — for sqrt
   these are unconditional constants, not caller-derived facts, so unlike
   the addition case they carry no wrong-hint risk. The invariant holds
   for camada too: `sqrt(normal)` is never subnormal is UNSAT over all
   inputs, verified symbolically.

   But the headroom is not there. `round()` is only ~13ms of sqrt's
   ~61ms (measured against `toIntegral`, which is round-dominated with
   almost no front end). Replacing the rounder with a raw repack — wrong
   numerically, but an upper bound on the saving — shrank the formula 30%
   (26112 -> 18356 bytes) and made it **slower**, 61ms -> 90ms.

That last result is the useful one: for this operation a 30% smaller
formula solved 48% slower. Formula size is not a proxy for solve time
here, so "emit fewer nodes" is not a strategy for sqrt.

**If anyone retries:** the remaining ~48ms is the restoring loop itself,
and beating it needs a better algorithm, not a tighter encoding of this
one. SymFPU's own comment points at the alternative — assert
`r < 2o+1 && x = o*o + r` over nondeterministic `o`, `r`, letting the
solver search rather than bit-blasting a fixed loop. That is a genuinely
different shape and would have to be gated on ESBMC hard instances.

## The gates these produced

**Hard-instance gate.** Encoding performance changes merge only on ESBMC
hard-instance wins. Toy benchmarks and mechanism arguments have proven
unpredictive in both directions: the LZC tree looked bad on toys and won;
A3/A4 were exact node reductions and lost.

The leading-zero investigation is worth recording in detail, because all
three reasons a toy misses the effect recur:

1. *Small instances solve instantly under either encoding.* The
   difference is visible at term level in a two-line program, but both
   variants finish in milliseconds. Divergence needs an instance where
   the SAT solver actually searches — the benchmark that exposed it had a
   380-assignment VCC over a five-layer neural net's float arithmetic,
   with a baseline solve around six minutes.

2. *Every size metric pointed the wrong way.* The chain encoding was
   smaller by all of them — roughly 3x fewer ITE/bvadd terms per
   operation, half the initial nodes (54,744 against 110,357), fewer
   nodes after preprocessing (405k against 712k), less memory (87 against
   147 MB), fewer lemmas. Screening candidates by "which encoding is
   bigger" discards the culprit. The chain's cost is **sequential
   dependency, not node count**: the tree's subtrees are independent and
   the bit-blaster and SAT solver exploit that; the chain's levels are
   not.

3. *The magnitude was version-sensitive in a misleading way.* On bitwuzla
   0.9.0 the chain cost about 1.4x; on 0.9.1 the same formula went from
   answering in ~500s to not answering within 1200s. That looked like a
   solver regression until the tree encoding showed 0.9.1 is in fact
   *faster* than 0.9.0 — there was no version regression, only an
   encoding newer bitwuzla tolerates worse. A toy attempted on one
   version can land on either side of the question.

The useful probe was not a timing repro but a **term-shape** one:
ESBMC's `--ssa-trace --ssa-smt-trace` prints the SMT term each SSA
assignment encodes to, so the structural difference shows up on a
two-line program even though the timing difference does not.

**Measure, do not recall.** Semantics come from executing the reference
implementation, not from memory or documentation. This caught a
fixed-point division that floors where camada truncated, and stopped
`sqrtfx` and `expfx` being pinned to one library's approximation error.

**A test for a known bug must be shown to catch it.** Every regression
test written for a specific defect here was verified to fail before the
fix and pass after.
