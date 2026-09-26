# Backend notes

## Native floating-point

<sup>1</sup> |
| [CVC5](https://cvc5.github.io/)            |  1.0.8          | ✔️<sup>1</sup> |
| [MathSAT](https://mathsat.fbk.eu/)         |  5.6.3          | ✔️<sup>2</sup> |
| [STP](https://stp.github.io/)              |  2.4.0          |   |
| [Yices](https://yices.csl.sri.com/)        |  2.6.1          |   |
| [Z3](https://github.com/Z3Prover/z3)       |  4.13.3         | ✔️ |
| SMT-LIB (any external solver) | n/a | depends on child |

<sup>1</sup> Bitwuzla and CVC5 restrict which *formats* native FP accepts,
because both word-blast through SymFPU, whose algorithms assume
`exponentWidth <= significandWidth`. Bitwuzla takes the four IEEE-754
interchange formats (binary16, binary32, binary64, binary128); CVC5 takes
only binary32 and binary64. Everything else needs an experimental flag
(`--fp-exp` on CVC5, a `--fpexp` build option on Bitwuzla), which Camada
does not enable — see the format table below. Z3 and MathSAT accept any
format natively.

<sup>2</sup> `fp.fma` and `fp.rem` are bit-blasted when using MathSAT because
it does not support these operations natively. `ROUND_TO_AWAY` is also not
supported by the native MathSAT floating-point API and aborts with an error if
requested (query `SolverFeature::NativeRoundToAway` before building the mode,
or use `FPEncoding::BV`).

### Formats

`FPEncoding::Native` support by format, measured against the minimum
versions in the README. `FPEncoding::BV` works for every format on every backend,
including STP and Yices, and is what Camada's own tests use for anything
outside binary32/binary64.

| Format               | Z3 | CVC5 | Bitwuzla | MathSAT |
| -------------------- | :-: | :-: | :-: | :-: |
| binary16 (5, 10)     | ✔️ |    | ✔️ | ✔️ |
| binary32 (8, 23)     | ✔️ | ✔️ | ✔️ | ✔️ |
| binary64 (11, 52)    | ✔️ | ✔️ | ✔️ | ✔️ |
| binary128 (15, 112)  | ✔️ |    | ✔️ | ✔️ |
| bfloat16 (8, 7)      | ✔️ |    |    | ✔️ |
| anything else        | ✔️ |    |    | ✔️ |

## Timeouts and unsat assumptions

- Yices has no native time limit, so `setTimeout` uses a process-global
  SIGALRM timer plus `yices_stop_search`. It is POSIX only, and at most one
  timed Yices check may run at a time process-wide.
- STP's time budget is whole seconds for the entire query; millisecond limits
  round up to the next second.
- Unsat assumptions are opt-in at creation on Bitwuzla and CVC5, because
  producing them slows every check and the option is frozen with the context.
  Set `SolverConfig::UseUnsatAssumptions = true` to extract cores.
  `supports()` reports the capability either way, since it describes the
  backend rather than the context; `produceUnsatAssumptions()` says whether a
  given solver has it on.
- `checkSatAssuming` works on every backend, through a push/assert/check/pop
  fallback where there is no native one.
- On STP, `getArrayValues` still answers for lazily lowered constant arrays,
  which the common layer handles.

## Arrays

- `Array<Idx, Bool>` is lowered through `Array<Idx, BV1>` on MathSAT and STP.
- Arrays with tuple elements work everywhere, decomposed into one array per
  field on backends without datatypes. Arrays indexed by a tuple sort are not
  yet supported there (issue #17).
- `ConstArrayLowering::Lazy` forces Camada's lazy constant-array lowering on
  any backend: a fresh array symbol whose default-value axiom is instantiated
  at each index the formula observes.

## Caveats

Camada tries to hide backend differences where practical, but a few solver
limitations still matter in day-to-day use.

- `MathSAT`
  - `reset()` recreates the solver environment internally so symbol names can
    be reused safely across resets.
  - quantified solving is not supported by MathSAT, so Camada treats
    quantifiers as unsupported on this backend.
  - native floating-point support has gaps: `fp.fma` and `fp.rem` are lowered
    through the common bit-vector path, and `ROUND_TO_AWAY` is not supported by
    the native MathSAT FP API.
- `STP`
  - only the bit-vector / array fragment is a natural fit. Integer, real,
    quantifier, and native floating-point support are not available.
  - constant arrays and boolean arrays are adapted internally by the wrapper,
    so some behavior is implemented through backend-specific lowering.
  - constant arrays use Camada's lazy lowering (the default-value axiom is
    instantiated at each index the formula observes), so they work at any
    index width.
- `Yices`
  - there is no native floating-point support, so FP always goes through
    Camada's bit-vector encoding.
  - constant arrays use Camada's lazy lowering: the Yices lambda encoding
    was found unsound (context reasoning over lambda terms is incomplete —
    a symbolic-index read of the default could satisfy formulas it should
    refute), a limitation smt-switch independently refuses to support.
  - global Yices initialization/teardown is hardened for multiple wrappers, but
    simultaneously live Yices solver instances can still collide on shared
    symbol names.
- `Bitwuzla`
  - integers and reals are not supported.
  - quantifiers are available, but the strongest coverage in Camada is still in
    the quantifier-free fragments.
  - constant arrays are native. Bitwuzla 0.9.1's array solver cannot reason
    about a constant array itself and answers UNKNOWN ("Equality over
    constant arrays not fully supported yet") when one reaches it; it works
    because preprocessing usually substitutes the constant array away, which
    covers `symbol = array_of(v)` and reads through it. Comparing two constant
    arrays with different defaults, a constant array behind a case split, or
    a constant array used as an array element (`array_of(array_of(v))`)
    returns UNKNOWN. Pass `ConstArrayLowering::Lazy` for those; it is always
    correct but asserts one axiom per observed index, which is slow in
    incremental use.
- `CVC5` and `Z3`
  - these are currently the most complete backends for the public Camada API.

## Choosing a backend

- Prefer `CVC5` or `Z3` if you want the broadest feature coverage with the
  fewest backend-specific caveats.
- Prefer `Bitwuzla` or `STP` for bit-vector-heavy workloads.
- Prefer `Bitwuzla` when you also need native floating-point.
- Prefer `STP` when you only need the bit-vector/array fragment.
- Use `MathSAT` when you need its quantifier-free feature set, but not
  quantifiers, and be cautious with native floating-point edge cases.
- Use explicit `FPEncoding` when creating floating-point and rounding-mode
  sorts/constants so the chosen native-vs-BV representation is obvious at the
  call site.

## SMT-LIB backend

In addition to the six native backends, Camada also ships an SMT-LIB
backend that drives any external solver speaking standard SMT-LIB on
stdin/stdout — z3, cvc5, or anything else that honors the
`(set-option :print-success true)` contract. The child is spawned with
`execvp(argv[0], argv)` — no shell is involved, so individual argv entries
can contain spaces or other characters without escaping concerns. Use it via:

```cpp
// The factory reports an SMTError when the child cannot be started -- the
// host is out of descriptors or process slots -- rather than aborting.
auto created = camada::createSMTLIBSolver({"z3", "-in"});
if (!created)
  return handle(created.error());
const auto &solver = created.value();
// ... build a problem with the usual mk*/addConstraint API ...
auto result = solver->check();          // sat / unsat / unknown
auto value = solver->getBV(symbol);     // round-trips through (get-value ...)
```

A fourth, **one-shot** mode serves solvers that read a complete formula
file and print a verdict instead of speaking interactive SMT-LIB
(Mallob-style distributed solvers, ML-based solvers):

```cpp
auto solver = std::make_unique<camada::SMTLIBSolver>(
    camada::SMTLIBOneShotTag{}, "/tmp/formula.smt2",
    "mallob -mono=%f -mono-app=SMT",   // %f = shell-quoted formula path
    {"z3", "-in"});                    // optional model solver for get-value
```

The script (including `(check-sat)`) is written to the formula file, the
shell command runs on it once, and stdout is scanned with a strict
per-line verdict parser (`sat`/`unsat`/`unknown` and the SAT-competition
`s ...` forms; the last verdict wins; a verdict from a signal-killed
command is discarded). Because the one-shot process cannot answer
`(get-value)`, an optional interactive model solver receives the same
script in parallel and serves models after a `sat` verdict — its own
verdict is exposed via `oneShotModelVerdict()` so callers can detect a
diverging model solver. The command runs in its own process group and a
spawn-time callback hands out the pgid for the caller's signal/timeout
teardown paths. One `check()` per solver; no-verdict runs return UNKNOWN
with the command, exit status, and output tail retrievable via
`oneShotDiagnostics()`. Unlike every other mode, the command template is
executed **via a shell** — do not build it from untrusted input.

A two-argument form also tees the emitted SMT-LIB script to a file, useful
when you want both an interactive answer and a reproducer to share:

```cpp
auto created = camada::createSMTLIBSolver(
    {"cvc5", "--lang", "smt2", "--incremental"}, "session.smt2");
// Also reports rather than aborts when the script file cannot be opened.
```

Verified child solvers (the regression suite drives each one through the
shared fixtures from `tests.h`):

| Solver       | Argv                                                            | Notes |
| ------------ | --------------------------------------------------------------- | ----- |
| z3           | `{"z3", "-in"}`                                                 | default |
| cvc5         | `{"cvc5", "--lang", "smt2", "--incremental", "--arrays-exp"}`   | `--incremental` is required for `(push)` / `(pop)`. `--arrays-exp` enables `((as const ...))` const-array literals. |
| bitwuzla     | `{"bitwuzla"}`                                                  | speaks SMT-LIB on stdin without extra flags |
| yices-smt2   | `{"yices-smt2", "--incremental"}`                               | `--incremental` is required for `(push)` / `(pop)`. No floating-point support — callers using native FP get an `unsupported` from the child. Use `FPEncoding::BV` to route every FP op through the common-layer bit-blast path, which works against yices. |
| mathsat      | `{"mathsat"}`                                                   | the CLI binary, not the C library; staged under `<build>/deps/src/mathsat-<version>-linux-x86_64/bin/mathsat` |
| stp          | `{"stp"}`                                                       | STP ≥ 2.4.0 only (older releases die on SMT-LIB2 commands they do not implement). BV/Bool/plain-array fragment: rejects `(set-logic ALL)` (Camada falls back to `QF_AUFBV`), answers `unsupported` to `:global-declarations` (symbols declared inside a `(push)` die with their scope), `:produce-unsat-assumptions`, and `(check-sat-assuming ...)` (Camada routes through the push/assert/check/pop fallback), rejects `((as const ...))`, and only supports `(get-value ...)` on declared symbols. Use `FPEncoding::BV` for FP. |

The Camada preamble unconditionally sends `(set-option :print-success true)`,
`(set-option :produce-models true)`,
`(set-option :produce-unsat-assumptions true)` (a child answering
`unsupported` still solves normally; only `getUnsatAssumptions` degrades,
and `supports(SolverFeature::UnsatAssumptions)` reflects the child's
answer),
`(set-option :global-declarations true)` (`unsupported` is tolerated, with
the scope caveat above), `(set-info :status unknown)`, and
`(set-logic ALL)` (with one fallback attempt at `QF_AUFBV` for children
that only accept concrete logic names) at startup, so any solver that
honors the SMT-LIB option contract should work. Every `SMTLIBSolver`
constructor also accepts an optional `Logic` string: when non-empty it is
emitted verbatim in place of `ALL`, with no negotiation — a child that
rejects a caller-chosen logic is a fatal error rather than a silent
downgrade. The choice survives `reset()`. Other solvers should be
straightforward to plug in via the `createSMTLIBSolver(argv)` factory.

Caveats:

- SMT-LIB has no `fp→bv` operation, so `mkIEEEFPToBV` is emulated with an
  uninterpreted function tied to its operand by `(= ((_ to_fp e s) (f x)) x)`,
  as on the Bitwuzla and CVC5 native backends. The tie is re-asserted after
  `(pop)`, so the bits outlive the scope they were built in. It is correct but
  much slower than a native operation.
- The child is spawned with `execvp`, so argv strings are interpreted
  verbatim by the kernel — not by a shell. Spaces, quotes, and `$` in
  individual argv entries are safe, but you cannot rely on shell
  redirection or environment expansion.

The backend covers the full Camada surface: BV/Bool, arrays, native
floating-point (FP arithmetic, predicates, conversions, and `(_ +oo …)` /
`(_ NaN …)` / `(fp …)` model parsing), Int/Real, uninterpreted functions,
quantifiers, and tuples (via `(declare-datatypes ...)`). Capability subsetting
is per-solver — for example yices-smt2 doesn't speak native FP and bitwuzla
doesn't speak Int/Real or tuples — and the regression matrix exercises only
the operations each child supports. Callers that need FP against a child
solver that doesn't speak it should ask Camada for `FPEncoding::BV` at
sort-construction time — that routes every FP op through the common-layer
bit-blast path and emits BV-only SMT-LIB.
