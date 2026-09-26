# Design notes

## Handle Lifetime

Expression and sort handles are solver-owned. Any `SMTExprRef` or `SMTSortRef`
obtained from a solver becomes invalid after:

- `solver->reset()`
- solver destruction

Handles must not be reused across those boundaries. Misuse is detected rather
than silently corrupted: each handle carries a generation tag from the owning
solver, and dereferencing a stale, null, or moved-from handle aborts via
`fatalError()` with a diagnostic message instead of reading freed memory.

The liveness check is race-free: a handle held by one thread can be safely
dereferenced or queried with `isValid()` while the owning solver is reset or
destroyed on another thread, and the stale handle will deterministically
abort. This does not make the solver itself thread-safe — see *Threading* below.

## Threading

Treat each solver instance as thread-confined. Camada does not support
concurrent use of a single solver object from multiple threads. Handles
(`SMTExprRef`, `SMTSortRef`) are safe to read from any thread as long as
the owning solver outlives the read.

## Solver configuration

Every `create*Solver()` factory takes a `SolverConfig` holding the options that
are frozen at construction: the array encoding, the tuple lowering (Camada's
per-field lowering can be forced even on backends with datatypes),
unsat-assumption production, a caller-chosen logic (SMT-LIB, Yices, MathSAT),
and the SMT-LIB one-shot ack deadline.

`SolverConfig::Arrays = ArrayEncoding::Ackermann` keeps arrays away from the
backend entirely: every select becomes a fresh element variable tied by
congruence axioms, stores and ites are lowered structurally, and equality uses
a witness-index encoding. It is for quantifier-free formulas only, forces the
Camada tuple encoding, and rejects nested arrays and array-sorted UF
signatures. Use it where a backend's array solver is the bottleneck; its cost
is quadratic in the reads per array, so it can be much worse elsewhere.

## Formula dumps

`dump()` emits an SMT-LIB script on most backends: declarations for every
symbol the assertions mention, each assertion wrapped in `(assert ...)`, and a
trailing `(check-sat)`. No `(set-logic ...)` is emitted, since Camada does not
track the fragment a formula ended up in; prepend one if the consumer needs it.
Yices prints Yices syntax and STP prints the CVC language, as neither API has
an SMT-LIB writer. Use the SMT-LIB backend for a portable script.

## Floating-Point Fallback

If a backend lacks native floating-point support, Camada can encode FP
operations through bit-vectors in the common layer.

This behavior can also be forced on supported solvers by constructing FP/RM
sorts and constants with `FPEncoding::BV` instead of `FPEncoding::Native`.

For example:

```cpp
auto fp64sort = solver->mkFPSort(11, 52, camada::FPEncoding::BV);
auto roundingMode =
    solver->mkRM(camada::RM::ROUND_TO_MINUS_INF, camada::FPEncoding::BV);
```

This is useful for:

- backend parity testing
- benchmarking the common FP encoding layer
- working around backend-specific native-FP gaps

## Tuples

Tuples use native datatypes on `CVC5`, `Z3`, and the SMT-LIB pipe; every
other backend routes tuple operations through Camada's per-field lowering.

For example:

```cpp
auto tupleSort = solver->mkTupleSort({solver->mkBoolSort(), solver->mkBVSort(8)});
auto tupleValue = solver->mkTuple({solver->mkBool(true), solver->mkBVFromDec(5, 8)});
auto second = solver->mkTupleSelect(tupleValue, 1);
```

## Caching Philosophy

Camada does some solver-local caching, but it is intentionally narrow.

The goal is to keep the wrapper lightweight, not to implement a full-blown
global expression cache for every sort and node shape. The built-in caching is
focused on cases where reuse is very frequent and the cache overhead is low,
such as:

- canonical sorts per solver generation
- common symbols
- boolean constants
- a small set of high-hit-rate bit-vector and floating-point helper constants

This means Camada does not try to intern every generated expression or sort.
If a client needs broader structural caching, it is expected to build that at a
higher layer on top of Camada, with the application owning the larger
expression cache while Camada stays focused on backend adaptation and
common-layer encodings.

Symbols are cached by `(name, sort)` for the solver's lifetime, so `mkSymbol`
returns the same handle even across `push`/`pop`. This matches every supported
backend's actual C/C++ API behavior — terms outlive the assertion-stack scope
that introduced them — but it diverges from strict SMT-LIB semantics where a
`(declare-const)` inside a pushed scope is removed on pop. Code that relies on
fresh-symbol-per-scope should call `solver->reset()` between scopes instead.

## Floating-point NaN handling

Camada is based on the backend written for [ESBMC](https://github.com/esbmc/esbmc) so some of the implementation decisions were geared towards the verification of C programs. In particular:
- `mkFPNeg` now accepts `FPNegBehavior`.
- The default, `FPNegBehavior::FlipSignBit`, preserves the full IEEE payload and only toggles the sign bit, including on `NaN`s.
- `FPNegBehavior::PreserveNaNPayload` follows the SMT floating-point standard and leaves `NaN`s unchanged.
- The distinction is only observable under `FPEncoding::BV`, where an FP value is its bit pattern. On a native FP sort both behaviors give that solver's canonical `NaN`, losing the operand's payload and sign; use `FPEncoding::BV` when the `NaN` bit pattern matters.

Camada's own FP-over-BV encoding also follows IEEE-754's recommended `NaN` handling rather than SMT-LIB's, which matters when a formula reads the bits of a `NaN` result:
- An operation with a `NaN` operand returns *that operand's* payload, with the significand's leading bit forced to 1: propagated per IEEE-754 6.2, quieted per 6.2.3. With two `NaN` operands the first one wins. This is what every hardware FPU does; SMT-LIB has a single abstract `NaN` and says nothing about payloads.
- `fp.abs` keeps the payload and clears the sign without quieting, since IEEE-754 treats it as a non-computational bit manipulation.
- Invalid operations on non-`NaN` operands (`0/0`, `inf - inf`, `sqrt` of a negative) build a fresh `NaN`, as there is no input payload to carry.
- `fp.to_fp` is the exception: it currently builds a fresh `NaN` rather than repositioning the payload into the target format's significand (see issue #195).
- All of this is only observable through raw bits under `FPEncoding::BV`; a native FP sort has one abstract `NaN`, so no `check()` result depends on it.
