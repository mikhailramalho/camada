# Fixed-Point Arithmetic Plan (August 2026, v2 after Codex review)

## Goal

Give Camada a fixed-point (FXP) layer whose semantics match C fixed-point
arithmetic — ISO/IEC TR 18037 (`_Fract`/`_Accum`) as implemented by Clang —
so ESBMC can encode fixed-point programs through the public Camada API
instead of hand-rolling BV arithmetic at every call site.

The layer is a **pure common-layer encoding over bit-vectors**. No SMT
solver has a native fixed-point theory and SMT-LIB defines none, so there
is no native-vs-encoded split, no per-backend code, and no
`supports(SolverFeature)` subsetting: every backend (and the SMT-LIB pipe)
gets FXP for free, the same way all backends share one tuple lowering.

## Semantics: what "close to C" means

Facts from TR 18037 (WG14 N1005 / ISO/IEC TR 18037:2008) that drive the
design:

1. **Non-saturating overflow is undefined behavior.** With the
   `FX_FRACT_OVERFLOW`/`FX_ACCUM_OVERFLOW` pragmas in their DEFAULT state
   (the normal case), overflow on `_Fract`/`_Accum` is UB — including the
   unsigned variants. C fixed-point has **no wrap-around guarantee**.
   TR 18037 §4.1.3 permits saturation, wrap, or other behavior varying
   per occurrence, so the BV value our encoding returns on overflow is
   **meaningful only under `!overflow`** — the paired predicate is the
   semantic contract, not the wrapped bits.
2. **Saturation is opt-in** (`_Sat` types or the pragmas in SAT state) and
   is the only standard-defined overflow behavior: clamp to the type's
   minimum or maximum.
3. **Rounding is per-operation, not one blanket policy:**
   - fixed-point → integer conversion is **specified: toward zero**;
   - arithmetic whose exact result falls between representable values may
     round to either neighbor (implementation-defined direction);
   - `roundfx` is round-to-nearest with only the halfway case unspecified;
   - fixed-point → float is unspecified.
   Clang's concrete choices are an implementation detail (LLVM's
   `llvm.smul.fix` LangRef leaves the direction unspecified), so the plan
   **pins the modeled frontend empirically**: the oracle tests fix a Clang
   version, target, flags, and pragma state, and every arithmetic
   encoding is validated against that pinned configuration rather than
   against an assumed LLVM guarantee.
4. `FX_FULL_PRECISION` controls the *precision latitude* of multiply and
   divide (whether intermediate results may be less than full precision),
   not the rounding direction; its default state is implementation-
   defined. Tier 1 models full-precision arithmetic and records the
   pragma state assumed by the oracles.

Consequences for a verifier:

- The deliverable for non-saturating ops is **the computed BV value plus
  UB predicates** (overflow, and division-by-zero as its own predicate).
  That is what lets ESBMC assert "no fixed-point UB" the way it asserts
  integer-overflow checks today.
- Saturating ops are a self-contained tier on top of the same encoding
  (overflow test + clamp ITE) and can ship later.

## Sort representation

A fixed-point sort is a BV sort with format metadata, mirroring how
`BVFP`/`BVRM` sorts carry FP metadata (`SMTSort::FPSortData`):

- `SMTSortKind::FXP`, carried data: total width `w`, fractional bits `n`,
  signedness. Constructor contract (validated, `fatalError` on
  violation): `w > 0`; unsigned formats require `n ≤ w`; signed formats
  require `n < w` (the sign bit is not a fraction bit).
- The underlying solver sort is the plain `w`-bit BV sort — backends never
  see the FXP kind, exactly as with `BVFP`.
- FXP-sorted expressions integrate with the generic machinery the same way
  `BVFP` does: symbols, ITE, arrays with FXP elements, and tuple fields
  carry the FXP sort while the backend sees BV, following `camadafp.cpp`'s
  retagging pattern (`rewrapExprImpl`) and `camadatuple.cpp`'s per-field
  precedent. This is a stated requirement with tests, not an accident.
- Padding bits (TR 18037 permits them; mainstream Clang targets use none)
  are **not** representable in `(w, n, signedness)` — recorded as an open
  question below rather than speculative metadata.
- Hash-consing through `camadacache.h` follows the existing FP-sort
  pattern; no new machinery.

## Public API surface (tier 1)

All in `camada.h` on `SMTSolver`, implemented in a new `src/camadafxp.cpp`:

```
// Sorts and constants
SMTSortRef mkFXPSort(unsigned Width, unsigned FracBits, bool IsSigned);
SMTExprRef mkFXPFromBin(StringRef RawBits, SMTSortRef);  // exact, any width
SMTExprRef mkFXPFromRawBV(SMTExprRef BV, SMTSortRef);    // reinterpret
SMTExprRef mkFXPToRawBV(SMTExprRef FXP);                 // reinterpret

// Arithmetic. Operands may have different FXP formats: following
// TR 18037's usual-arithmetic-conversions rule, the operation is
// computed in the common full-precision format (max integer bits, max
// fraction bits, signed if either operand is signed) and the result
// carries that format; callers convert the result explicitly if they
// need a narrower type. Camada centralizes the widening logic so ESBMC
// does not hand-roll it.
mkFXPAdd, mkFXPSub, mkFXPNeg
mkFXPMul, mkFXPDiv

// Shifts (TR 18037 semantics: raw-BV shifts on the scaled value;
// left shift has an overflow predicate, right shift is exact)
mkFXPShl, mkFXPShr

// Comparisons (scale-aligned in the common format, then BV compare)
mkFXPLt, mkFXPLe, mkFXPGt, mkFXPGe, mkFXPEqual
// NOTE: raw mkEqual is only sound for identical formats; mkFXPEqual is
// the documented comparison entry point.

// UB predicates (tier 1, all of them — ESBMC cannot claim soundness
// without conversion overflow and div-by-zero)
mkFXPAddOverflow, mkFXPSubOverflow, mkFXPMulOverflow, mkFXPDivOverflow,
mkFXPNegOverflow,           // unsigned negation: overflow iff operand != 0
mkFXPShlOverflow,
mkFXPDivByZero,             // separate predicate; distinct violation kind
mkFXPToFXPOverflow, mkFXPToBVOverflow

// Conversions
mkFXPToFXP(Exp, TargetSort)
mkFXPFromBV / mkFXPToBV(...)   // FXP→integer rounds toward zero (specified)

// Model query — exact, no doubles, no int64 limits: raw bits + format,
// reusing the getBVInBin precedent for extraction
struct FXPValue { std::string RawBits; unsigned FracBits; bool IsSigned; };
SMTResult<FXPValue> getFXP(Exp);
```

## Encoding rules (tier 1, all in terms of existing public mk* BV ops)

Common conventions: `w` is the operand format width after the operands are
brought to the common format; every widened intermediate is kept until
both the rounded value **and** the overflow predicate are derived from it.

| Op | Value encoding | UB predicate |
| --- | --- | --- |
| add/sub | BV add/sub in the common format extended by one bit | existing BV overflow predicates on the extended form |
| neg | BV neg | signed: existing `mkBVNegOverflow`; unsigned: `operand != 0` (the BV predicate only detects signed minimum) |
| mul | extend both to `2w` per signedness; `bvmul`; **round from the raw `2w` product** (truncating shift by `n`); take low `w` bits | compare the **unshifted `2w` product** against `min_raw·2^n` / `max_raw·2^n` — never the already-rounded value, or exact results within one rounding step of the boundary escape detection |
| div | extend to `2w`; shift dividend left by `n` (after extension); `bvsdiv`/`bvudiv`; take low `w` bits | div-by-zero: `rhs = 0`, own predicate. Range: sign-aware comparison of the exact rational — `lhs_raw·2^n` against `rhs_raw·max_raw` and `rhs_raw·min_raw` products in the wide width — **before** rounding, for the same boundary reason as mul |
| shl | BV shl in a widened intermediate | shifted-out-high-bits / sign-change check on the wide value |
| shr | BV ashr/lshr | exact (no predicate) |
| compare | scale-align to the common format, then `bvslt`/`bvult` family | — |
| FXP→FXP | **extend first** (per source signedness) to a width that holds both formats, **then** shift by `n_to − n_from`, then truncate to target — never shift-then-extend, which discards high bits on widening conversions | `mkFXPToFXPOverflow` from the wide pre-truncation value |
| FXP→integer | **round toward zero** (specified by TR 18037): signed divide by `2^n`, or bias the negative case before `ashr` — plain `ashr` alone is wrong (floors: `-1.5 → -2`, C requires `-1`) | `mkFXPToBVOverflow` from the wide value |

## Tier 2 (shipped Aug 2026): `_Sat` and rounding control

All of tier 2 has landed: the saturating operations in #133, the
execution oracle and the division-rounding fix in #134, and the
fixed<->float conversions plus `roundfx` in #135. The rulings below are
kept as the record of why each piece was built the way it was; the
"blocked" notes are historical and carry their resolution inline.

**Decided (Aug 2026): saturation is an operation property, not a sort
property.** `_Sat _Fract` shares its representation with `_Fract`
(TR 18037 mandates identical representation/alignment; only overflow
behavior differs), so the sort stays `(width, frac, signed)` and tier 2
adds op variants — `mkFXP{Add,Sub,Neg,Mul,Div,Shl}Sat` plus saturating
`mkFXPToFXPSat`/`mkFXPToBVSat`. This mirrors LLVM (`llvm.smul.fix` vs
`llvm.smul.fix.sat` over plain integers, frontend picks by C type):
sat-ness lives in the frontend's type system, and ESBMC's clang frontend
already computes result types, so Camada never needs TR 18037's
sat-propagation rules for mixed operands, and the sort cache/equality/
conversion machinery stays untouched. Saturating overflow is defined
behavior — the sat variants carry no overflow predicates — but division
by zero remains UB even for `_Sat` types, so `mkFXPDivSat` still pairs
with `mkFXPDivByZero`. The flip case that would justify a sort flag
(Camada computing C result types including sat-ness itself) is explicitly
out: the frontend must know the types anyway.

- Saturating variants of add/sub/mul/div/neg/shl/conversions: tier-1
  overflow test + ITE clamping to format min/max. Roughly +60% on the op
  surface and doubles the arithmetic test matrix.
- Round-to-nearest on narrowing (`roundfx`-style, half-ulp bias before the
  truncating shift). **Ruling (Aug 2026): camada-owned, blocked on the
  oracle. IMPLEMENTED Aug 2026** as `mkFXPRound(Exp, Digits)`. The
  blocker was resolved from the wrong direction: Clang ships no
  `stdfix.h` and no `roundfx` (nor does GCC's, which declares only types,
  `abs` and `bits`), so the generator cannot measure it. **LLVM libc**
  implements all twelve variants, and its source shows round to nearest
  with **ties toward +infinity** (`x + round_bit` then mask) and
  **saturate to MAX** when the bias overflows — exactly the width trap
  this ruling predicted. But the TR leaves the tie direction to the
  implementation and implementations differ (GCC's AVR builtins are the
  other one that ships `roundfx`; glibc, musl, newlib and uClibc have no
  fixed-point support at all), so the **tie direction is a parameter**
  (`FXPRoundTie`: TowardPositive, AwayFromZero, ToEven) rather than one
  library's choice baked in — the `FPNegBehavior` precedent for an
  implementation-defined split. Saturation is not parameterized: every
  implementation surveyed agrees on it.
  Note the operation keeps its format and clears the low fraction bits;
  it is not a narrowing conversion. Verified against 52452 vectors from
  executing libc's algorithm over Clang's fixed-point types. Since it is
  a library function rather than a builtin, a consumer only needs it when
  the program under test links LLVM libc.
- FXP<->FP conversions. **Ruling (Aug 2026): camada-owned, blocked on
  ESBMC Phase 3 demand + the oracle. UNBLOCKED Aug 2026 by
  REPORT-fxp-api-gaps.md: demand live (ESBMC refuses fixed<->float,
  pinned by their conv_float_unsupported test) and semantics measured —
  fixed->float RNE (tie vectors both directions + all-ones carry-out),
  float->fixed toward zero (NOT floor), _Sat clamp with inf->rails and
  NaN->0, non-Sat out-of-range/inf/NaN stays UB behind a predicate.
  Their rows are clang 20.1.8; regenerate under the 22.1.6 pin before
  trusting them (deltas not expected, C-semantics-stable).
  **IMPLEMENTED Aug 2026** (feat/fxp-fp-conversions): mkFXPToFP(Exp, To,
  RM), mkFPToFXP, mkFPToFXPOverflow, mkFPToFXPSat. Regenerated under the
  22.1.6 pin: all of ESBMC's rows reproduce exactly, no deltas from
  20.1.8. Two findings beyond their report: (a) the defined range for the
  plain conversion is the OPEN interval (minRaw-1, maxRaw+1) at scale —
  Clang lowers it as fmul-by-2^n + fptosi, so a value one ulp past a rail
  is still defined because truncation brings it back; (b) the wide
  intermediate cannot always be a native sort (bitwuzla rejects
  nonstandard native formats, cvc5's default build allows only
  Float32/Float64), so the encoder falls back to computing in the BV
  encoder and bit-bridging the result — exact, no second rounding.** Single rounding from the exact
  rational raw/2^N is unattainable by composition — to_fp(raw) then a
  power-of-two scale double-rounds on subnormal underflow; the scale must
  fold into the exponent before the rounding step, inside the encoder.
  Completes the existing conversion family (mkSBVtoFP/mkFPtoSBV/
  mkFPtoFP). The camadafp cost concern governs how freely ESBMC *emits*
  these conversions, not where they are implemented. Semantics (which C
  rounding mode governs fixed->float, the _Sat clamp interaction) come
  from the TR text plus the execution oracle, not recall.

Nothing in tier 1's encoding needs rework for tier 2 — saturation and
rounding both compose on top of the widened intermediates tier 1 already
keeps.

## Testing

- New shared fixture header `regression/fxp.test.h`, instantiated by every
  backend's `.test.cpp` (pattern of `fp.test.h`); the SMT-LIB pipeline
  children exercise it through the existing pipeline macros (FXP emits
  pure BV on the wire, so even stp runs it).
- **Oracles.** Host-compiled fixed-point oracles are pinned to an exact
  configuration recorded in the fixture header: Clang version, target
  triple, flags, and pragma state (overflow pragmas DEFAULT,
  `FX_FULL_PRECISION` state noted). **UB cases are excluded from
  compiler oracles** — compiler output for UB inputs is not an oracle;
  overflow and div-by-zero predicates are validated exclusively against
  an exact rational reference model.
- **Exhaustive small-width sweeps** (4-bit formats, all operand pairs)
  against the rational model, **plus a conversion matrix** that varies
  width, fraction bits, and signedness across conversions — including
  widening conversions (extend-before-shift coverage), signedness
  changes, and ≥64-bit formats whose intermediates are 128-bit (the
  sweeps alone cannot catch those).
- **Boundary-overflow vectors**: exact results just above/below the
  representable range that round back onto a boundary — pinning that the
  predicates test the pre-rounding value.
- **Sign-sensitive rounding vectors**: positive/negative halfway and
  non-halfway cases; signed division toward-zero vs floor; FXP→integer
  toward zero on negatives.
- **UB-predicate fixtures** for every predicate, including unsigned
  negation (`operand != 0`) and both conversion overflows, proven
  equivalent to independent reference encodings (the
  `bv_overflow_semantics` pattern).
- **Per-op backend parity** spot checks for the encodings that stress
  backends differently — signed division, wide shifts, degenerate 1-bit
  and sign-only formats — across the native backends and the pipeline
  children, not just fixture instantiation.
- **Generic-construct fixtures**: FXP symbols, ITE over FXP, arrays with
  FXP elements, FXP tuple fields, behavior across push/pop/reset, and
  raw-BV reinterpretation round trips.
- Model-query fixtures round-trip `getFXP` (exact raw-bits form) through
  solver models on every backend.

## Size and phasing

| Piece | Estimate |
| --- | --- |
| Sort plumbing + generic integration (`camada.h`, `camadasort.{h,cpp}`) | ~150 lines |
| `camadafxp.cpp` tier-1 ops, mixed-format widening, conversions, predicates, model query | ~800–1,100 lines |
| `fxp.test.h` + per-backend instantiation + oracle tables | ~700–900 lines |
| README (feature list, parity table row: all ✔️, encoded) | small |

In the end tier 1 landed as one PR and tier 2 as three (#133 saturating
ops, #134 oracle and division fix, #135 conversions and `roundfx`).

## Risks and open questions

1. **Clang pinning — RESOLVED (Aug 2026)**: pinned to clang 22.1.6,
   `x86_64-unknown-linux`, `-ffixed-point`, seed `0xCA3ADA`, per ESBMC's
   answers in `ANSWERS-fxp-tier2-scope.md`; the generated header records
   the configuration. ESBMC's own measurements on clang 20.1.8 reproduce
   exactly under the pin, so the fixed-point lowering is stable across
   those releases.
2. **Padding bits**: TR 18037 permits padded fixed-point formats; the
   `(w, n, signedness)` metadata cannot express them. No mainstream
   Clang target uses padding; explicitly out of scope until a consumer
   needs it (would become a fourth sort parameter, not a redesign).
3. **Mixed-format rule fidelity — RESOLVED (Aug 2026)**, against both the
   TR text (N1169 §4.1.4 + 6.3.1.8 amendments) and 8,781 executed oracle
   vectors. Findings: the TR states usual arithmetic conversions do NOT
   apply between fixed-point operands — computation happens at full
   precision and only the result converts, to the higher-RANK operand
   type (all accums outrank all fracts; signed wins sign mixes; Clang's
   _Generic-reported result types match the rank rule 8781/8781).
   Camada's common format (max int, max frac, signed-if-either) is a
   correct full-precision container, but the result CARRIES the common
   format, not C's ranked type: consumers implement C semantics as
   mkFXPToFXP[Sat](mixed-op, C-result-sort), which is exact (floor and
   clamp compose across nested scales) and is pinned end-to-end by the
   kMixed oracle fixture. Caveat relayed to ESBMC: since "no conversions
   are needed", Clang's AST may NOT materialize operand casts for
   fixed-by-fixed operators — their frontend should verify whether it
   sees casts or mixed operands, and either path is now covered.
   **Confirmed by ESBMC (Aug 2026)**: AST dump shows no FixedPointCast on
   operands — the BinaryOperator is typed as the higher-rank operand and
   casts appear only where the result converts further. So camada
   receives mixed-format operands from ESBMC directly (their earlier
   scoping answer said otherwise and was retracted); their fxp_align_result
   converts the common-format result once into the operator's C type.
   ESBMC also independently reproduced the division-floor finding (all
   five vectors, clang 20.1.8, -O0 = -O2) and confirmed multiplication
   floors too — camada's mul already floored (arithmetic-shift of the raw
   product) and 3,334 mul/mulsat oracle vectors pin it, so no change.
   Their Phase 2 migration passes end to end against feat/fxp-oracle
   HEAD (all 10 regression/fixedbv tests on bitwuzla and z3).
4. **API naming**: `FXP` chosen to parallel `FP`; bikeshed before the PR.
5. **Which formats ESBMC emits** (Clang defaults: 8/16/32/64-bit) decides
   the constructor conveniences worth adding beyond `mkFXPFromBin`.

## `exp` (Aug 2026): why it is domain-restricted

ESBMC asked for a correctly-rounded fixed-point `exp` so they can check
the error bounds LLVM libc claims for `exphk` and `expk` (relative error
< 2^-8 and < 2^-16 respectively). Camada supplies the ground truth; it
deliberately does NOT reproduce libc's own approximation, which is a
lookup table plus a linear correction and has no bit pattern worth
matching — the same reasoning as `sqrtfx`.

Correct rounding needs an intermediate wide enough to decide every
rounding, which needs the hardest-to-round distance: how close `exp` ever
lands to a halfway point between representable values. For floating-point
formats that is the table maker's dilemma and takes a directed search
(Lefèvre–Muller; CORE-MATH). For the C `_Accum` formats the interesting
band — where `exp` is neither 0 nor saturated — is small enough to sweep
exhaustively, so the bound is measured instead. All six are recorded in
`scripts/fxp_exp_bounds.txt`; the widest needs 75 fractional bits.

**The measurement does not generalise, and cannot be made to.** Each
sweep covers one exact `(width, frac, signedness)` triple: the fraction
width sets the sample spacing and the integer width sets where saturation
cuts the range off, so two formats of the same storage width share
nothing. Nor is the bound monotone in either parameter, so there is no
"widest case dominates" shortcut.

Sweeping the whole format space is not merely undone but infeasible.
Cost grows as 2^frac while the useful range grows only logarithmically,
so the low-integer-bit formats dominate: `s2.61` alone is 1.24e19 inputs
(~6,000 years on 32 threads), and all 64-bit formats together are 1.05e20
inputs — roughly 51,000 years. `mkFXPExp` therefore accepts an allowlist
of swept triples and aborts otherwise, rather than encoding with a width
it cannot justify. Adding a format means running
`scripts/fxp_exp_worstcase.c` for it (minutes, for anything up to ~38
fraction bits) and adding a row.

This makes `exp` the one FXP operation with a restricted domain: every
other one is exact algebra and works at any width. Lifting the
restriction needs an analytic bound — effective Baker-type bounds on
linear forms in logarithms — not more compute.
