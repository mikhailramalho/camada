# Rejected and parked experiments

Work that was built, measured, and deliberately not merged. Each entry
records what was tried, what the evidence said, and why the decision went
the way it did — so the idea is not rediscovered and re-implemented from
scratch, and so a future proposal has to beat the measurement rather than
repeat it.

The branches named here are kept for reference. Deleting one is fine once
its entry below is accurate; the entry is the artifact worth keeping, not
the code.

---

## Encoding performance

### Rounder restructuring (A3/A4) — REJECTED on measurement

Branch: `perf/rounder-structure`

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

Branch: `feat/eager-row-arrays`

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

### UF emulation without shadow terms — PARKED, incomplete

Branch: `experiment/uf-ieeebv-no-shadow`, local only

An experiment in emulating uninterpreted functions for the IEEE-BV
bridge without the shadow-term machinery. Never finished; kept only as a
starting point if the shadow approach ever becomes a problem.

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

## The gates these produced

**Hard-instance gate.** Encoding performance changes merge only on ESBMC
hard-instance wins. Toy benchmarks and mechanism arguments have proven
unpredictive in both directions: the LZC tree looked bad on toys and won;
A3/A4 were exact node reductions and lost.

**Measure, do not recall.** Semantics come from executing the reference
implementation, not from memory or documentation. This caught a
fixed-point division that floors where camada truncated, and stopped
`sqrtfx` and `expfx` being pinned to one library's approximation error.

**A test for a known bug must be shown to catch it.** Every regression
test written for a specific defect here was verified to fail before the
fix and pass after.
