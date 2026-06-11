[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg)](https://www.apache.org/licenses/LICENSE-2.0)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/7eef16a1313d4ba8801a21e767a0fb25)](https://app.codacy.com/manual/mikhail-ramalho/camada?utm_source=github.com&utm_medium=referral&utm_content=mikhailramalho/camada&utm_campaign=Badge_Grade_Dashboard) [![Linux Build](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml) [![MacOS Build](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml)

# Camada

Camada ("layer" in Portuguese) is a permissively licensed C++17 wrapper for
multiple SMT solvers. It exposes a unified API across:

- Bitwuzla
- CVC5
- MathSAT
- STP
- Yices
- Z3
- SMT-LIB (any external solver speaking SMT-LIB v2 on stdin/stdout)

The library is designed to make solver switching cheap while still filling
feature gaps in backends that are missing parts of the SMT-LIB surface.

Current encoded/common-layer features:

- floating-point fallback via bit-vector encoding
- array support, including lazily lowered constant arrays for backends
  without a native `((as const ...))` operator
- tuple lowering for backends without native datatype support (native
  datatypes on CVC5, Z3, and the SMT-LIB pipe; per-field decomposition
  elsewhere, with some remaining gaps such as arrays of tuples)
- bit-vector overflow predicates, assumption-based solving with unsat
  assumptions, per-check wall-clock timeouts, sparse array model
  extraction, and a queryable capability API (`supports(SolverFeature)`)

## What Camada Is

Camada is intentionally a thin common layer:

- solver-specific wrappers live in the backend classes
- common behavior and missing-feature encodings live in the shared layer
- expressions and sorts are solver-owned handles

This makes it practical to:

- switch solvers without rewriting the calling code
- route unsupported features through common-layer encodings
- keep backend-specific quirks contained in one place

## Building and Installing

Camada uses CMake as its build system. Follow these steps to build and install the library:

### Prerequisites

- CMake (Version 3.15 or higher)
- C++ Compiler (Supporting C++17)
- Any of the supported solvers

### Build and Install
```bash
# Clone the Camada repository
git clone https://github.com/mikhailramalho/camada.git
cd camada

# Run CMake to configure the project
cmake -S . -B build

# Build the library
cmake --build build

# Install Camada
cmake --install build
```

Useful configure options:

- `-DCMAKE_BUILD_TYPE=Release`
- `-DBUILD_SHARED_LIBS=ON/OFF`
- `-DENABLE_WARNINGS=ON/OFF` (default: ON; adds `-Wall -Wextra -pedantic`)
- `-DENABLE_WERROR=ON/OFF` (default: OFF; treat warnings as errors — used by CI)
- `-DCAMADA_ENABLE_REGRESSION=ON/OFF`
- `-DCAMADA_DOWNLOAD_DEPENDENCIES=ALL`
- `-DCAMADA_SOLVER_<NAME>_ENABLE=IFAVAILABLE/ON/OFF` to control enabled
  backends

### Downloading Supported Solvers

Camada can now download and build missing solver dependencies during CMake
configure, following the same general approach used in ESBMC:
```bash
cmake -S . -B build -DCAMADA_DOWNLOAD_DEPENDENCIES=ALL
cmake --build build
```

`CAMADA_DOWNLOAD_DEPENDENCIES` accepts three modes:
- `OFF`: do not download dependencies.
- `ALL`: download all supported solver dependencies.
- `PERMISSIVE`: download only solvers with permissive licenses
  (`Bitwuzla`, `CVC5`, `STP`, and `Z3`).

Downloaded sources and locally installed solver artifacts are stored under
`<build-dir>/deps/src` and `<build-dir>/deps/install`.

When CMake downloads dependencies itself:
- `Bitwuzla` uses the prebuilt static release archive from `0.9.1`.
- `Z3` uses the prebuilt release archive from `z3-4.16.0`.
- `CVC5` uses the prebuilt static release archive from `cvc5-1.3.4`.
- `Yices` uses a source build.
- `GMP` uses a source build when it is needed by downloaded dependencies and no
  suitable staged copy is already available.
- `MathSAT` uses the vendor-provided prebuilt archive from `5.6.17` on
  Linux. macOS stays pinned to `5.6.16`: the `5.6.17` macOS tarball ships
  `libmathsat.a` as a plain `ar` archive of fat Mach-O objects, a layout
  Apple's `ld` rejects.
- `STP` still falls back to a source build. The `2.3.4_cadical` GitHub release
  only ships a standalone `stp` executable, not the headers and libraries that
  Camada needs to link against the STP C++ API.
- `CryptoMiniSat` and `Minisat` still build from source as part of the STP
  dependency chain.

The `<build-dir>/deps/install` directory will contain the staged solver headers,
libraries, and auxiliary artifacts, and Camada will use them from this
location during the build.

## Supported backends

| Backend    | Minimum version | Native floating-point support |
| ---------- | :-------------: | :-------------: |
| [Bitwuzla](https://bitwuzla.github.io/)    |  0.9.1          | ✔️ |
| [CVC5](https://cvc5.github.io/)            |  1.0.8          | ✔️ |
| [MathSAT](https://mathsat.fbk.eu/)         |  5.6.3          | ✔️<sup>1</sup> |
| [STP](https://stp.github.io/)              |  2.3.4          |   |
| [Yices](https://yices.csl.sri.com/)        |  2.6.1          |   |
| [Z3](https://github.com/Z3Prover/z3)       |  4.16.0         | ✔️ |
| SMT-LIB (any external solver) | n/a | depends on child |

<sup>1</sup> `fp.fma` and `fp.rem` are bit-blasted when using MathSAT because
it does not support these operations natively. `ROUND_TO_AWAY` is also not
supported by the native MathSAT floating-point API and aborts with an error if
requested.

### SMT-LIB backend

In addition to the six native bindings above, Camada also ships an SMT-LIB
backend that drives any external solver speaking standard SMT-LIB on
stdin/stdout — z3, cvc5, or anything else that honors the
`(set-option :print-success true)` contract. The child is spawned with
`execvp(argv[0], argv)` — no shell is involved, so individual argv entries
can contain spaces or other characters without escaping concerns. Use it via:

```cpp
auto solver = camada::createSMTLIBSolver({"z3", "-in"});
// ... build a problem with the usual mk*/addConstraint API ...
auto result = solver->check();          // sat / unsat / unknown
auto value = solver->getBV(symbol);     // round-trips through (get-value ...)
```

A two-argument form also tees the emitted SMT-LIB script to a file, useful
when you want both an interactive answer and a reproducer to share:

```cpp
auto solver = camada::createSMTLIBSolver(
    {"cvc5", "--lang", "smt2", "--incremental"}, "session.smt2");
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

The Camada preamble unconditionally sends `(set-option :print-success true)`,
`(set-option :produce-models true)`,
`(set-option :produce-unsat-assumptions true)` (a child answering
`unsupported` still solves normally; only `getUnsatAssumptions` degrades,
and `supports(SolverFeature::UnsatAssumptions)` reflects the child's
answer),
`(set-option :global-declarations true)`, `(set-info :status unknown)`, and
`(set-logic ALL)` at startup, so any solver that honors the SMT-LIB option
contract should work. Other solvers should be
straightforward to plug in via the `createSMTLIBSolver(argv)` factory.

Caveats:

- `mkIEEEFPToBV` is scoped to the current `(push)`/`(pop)` level. SMT-LIB
  has no portable same-encoding `fp→bv` op, so the backend materializes a
  fresh BV symbol and constrains it via the inverse direction — the
  constraint is unwound by `(pop)`, same as the cvc5 and bitwuzla native
  backends.
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

## API Overview

Camada currently provides public APIs for:

- booleans
- bit-vectors
- integers and reals
- floating-point
- rounding modes
- arrays
- uninterpreted functions
- quantifiers on supporting backends
- incremental solving (`push`/`pop`)
- assumption-based solving (`checkSatAssuming`) with unsat-assumption
  extraction (`getUnsatAssumptions`)
- per-check wall-clock timeouts (`setTimeout`; checks that hit the limit
  return `UNKNOWN`)
- bit-vector overflow predicates (`mkBVSAddOverflow`/`mkBVUAddOverflow`,
  `mkBVSSubOverflow`/`mkBVUSubOverflow`, `mkBVSMulOverflow`/`mkBVUMulOverflow`,
  `mkBVSDivOverflow`, `mkBVNegOverflow`)
- model queries for supported value kinds, including sparse array models
  (`getArrayValues`)
- a queryable capability API (`supports(SolverFeature)`) so callers can
  select backends without discovering gaps through errors

Array support is currently partial in the larger structured-data sense:

- plain SMT arrays are supported
- backend-specific array gaps such as `Array<Idx, Bool>` are handled
- arrays of tuples remain part of the unfinished tuple work

## Backend Feature Parity

The table below summarizes the current public-API coverage at a glance.
`BV FP` means the backend can use Camada's bit-vector floating-point encoding
even if it lacks native floating-point support.

| Feature | Bitwuzla | CVC5 | MathSAT | STP | Yices | Z3 |
| ------- | :------: | :--: | :-----: | :-: | :---: | :-: |
| Booleans | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ |
| Bit-vectors | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ |
| Integers / reals |   | ✔️ | ✔️ |   | ✔️ | ✔️ |
| Native FP | ✔️ | ✔️ | ✔️<sup>1</sup> |   |   | ✔️ |
| BV FP encoding | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ |
| Arrays | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ |
| Uninterpreted functions | ✔️ | ✔️ | ✔️ |   | ✔️ | ✔️ |
| Tuples | ✔️<sup>2</sup> | ✔️ | ✔️<sup>2</sup> | ✔️<sup>2</sup> | ✔️<sup>2</sup> | ✔️ |
| Quantifiers | ✔️ | ✔️ |   |   |   | ✔️ |
| Overflow predicates | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ |
| Unsat assumptions | ✔️ | ✔️ | ✔️ |   | ✔️ | ✔️ |
| Timeouts (`setTimeout`) | ✔️ | ✔️ | ✔️ |   | ✔️<sup>3</sup> | ✔️ |
| Array models (`getArrayValues`) | ✔️ | ✔️ | ✔️ |   | ✔️ | ✔️ |

<sup>1</sup> On `MathSAT`, `fp.fma` and `fp.rem` are lowered through the
common BV path, and native `ROUND_TO_AWAY` is unsupported.

<sup>2</sup> Via Camada's per-field tuple lowering rather than native
datatypes; some gaps remain (e.g. arrays of tuples). Query
`supports(SolverFeature::NativeTuples)` to tell the two apart.

<sup>3</sup> POSIX only, enforced through a process-global SIGALRM timer —
at most one timed Yices check may run at a time process-wide.

The last four rows (and any platform splits) are queryable at runtime via
`supports(SolverFeature)`; `checkSatAssuming` itself works on every
backend through a push/assert/check/pop fallback — the unsat-assumptions
row covers `getUnsatAssumptions`. On STP, `getArrayValues` still answers
for lazily lowered constant arrays, which the common layer handles.

## Backend Caveats

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
  - `setTimeout` is enforced with a process-global SIGALRM timer plus
    `yices_stop_search` (Yices has no native time limit), so it is POSIX-only
    and at most one timed Yices check may run at a time process-wide.
- `Bitwuzla`
  - integers and reals are not supported.
  - quantifiers are available, but the strongest coverage in Camada is still in
    the quantifier-free fragments.
  - constant arrays use Camada's lazy lowering: Bitwuzla 0.9.x answers
    UNKNOWN for formulas that equate a native constant array with another
    array (it warns "Equality over constant arrays not fully supported
    yet"), which breaks the common `symbol = array_of(v)` pattern.
- `CVC5` and `Z3`
  - these are currently the most complete backends for the public Camada API.

## Recommended Usage

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
- Treat each solver instance as thread-confined. Camada does not support
  concurrent use of a single solver object from multiple threads. Handles
  (`SMTExprRef`, `SMTSortRef`) are safe to read from any thread as long as
  the owning solver outlives the read — see *Handle Lifetime* below.

## Design Notes

### Handle Lifetime

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
abort. This does not make the solver itself thread-safe — see *Recommended
Usage* for the threading contract.

### Floating-Point Fallback

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

### Tuples

Tuples use native datatypes on `CVC5`, `Z3`, and the SMT-LIB pipe; every
other backend routes tuple operations through Camada's per-field lowering.

For example:

```cpp
auto tupleSort = solver->mkTupleSort({solver->mkBoolSort(), solver->mkBVSort(8)});
auto tupleValue = solver->mkTuple({solver->mkBool(true), solver->mkBVFromDec(5, 8)});
auto second = solver->mkTupleSelect(tupleValue, 1);
```

### Backend-Specific Adaptation

Camada also smooths over backend quirks where practical. For example:

- MathSAT and STP now lower `Array<Idx, Bool>` through backend `Array<Idx, BV1>`
  representations internally
- STP, Yices, and Bitwuzla constant arrays use Camada's lazy lowering (a fresh array
  symbol whose default-value axiom is instantiated at each observed index);
  `ConstArrayLowering::Lazy` forces the same lowering on any backend
- MathSAT native FP still falls back for unsupported operations such as
  `fp.rem`

### Caching Philosophy

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

## Implementation Details

Camada is designed as a wrapper library to simplify the usage of multiple SMT solvers. It provides a common interface for interacting with these solvers, allowing developers to switch between them seamlessly without changing their codebase.

Camada is based on the backend written for [ESBMC](https://github.com/esbmc/esbmc) so some of the implementation decisions were geared towards the verification of C programs. In particular:
- `mkFPNeg` now accepts `FPNegBehavior`.
- The default, `FPNegBehavior::FlipSignBit`, preserves the full IEEE payload and only toggles the sign bit, including on `NaN`s.
- `FPNegBehavior::PreserveNaNPayload` follows the SMT floating-point standard and leaves `NaN`s unchanged.
- `FlipSignBit` is fully honored under BV encoding and via the SMTLIB pipeline. On native FP backends (Bitwuzla, CVC5, Z3) it is best-effort: these solvers treat all `NaN`s as a single equivalence class, so when the operand is a `NaN` the resulting `NaN`'s bit pattern is not guaranteed to match a literal sign-bit flip of the input bits.

## Usage Example

```cpp
#include <camada/camada.h>

int main() {
  // Create a solver instance (example using Z3)
  auto solver = camada::createZ3Solver();

  // Choose the floating-point encoding explicitly.
  camada::SMTSortRef fp64sort =
      solver->mkFPSort(11, 52, camada::FPEncoding::Native);
  camada::SMTExprRef roundingMode =
      solver->mkRM(camada::RM::ROUND_TO_MINUS_INF,
                   camada::FPEncoding::Native);

  camada::SMTExprRef x = solver->mkSymbol("x", fp64sort);
  camada::SMTExprRef y = solver->mkSymbol("y", fp64sort);
  camada::SMTExprRef r = solver->mkSymbol("r", fp64sort);

  camada::SMTExprRef xV = solver->mkFPFromBin(
      "0111011101100100111000010001001010111000010010111000100101001010", 11,
      camada::FPEncoding::Native);
  camada::SMTExprRef yV = solver->mkFPFromBin(
      "0100100101001110001001011011001100110001111010011101010010000001", 11,
      camada::FPEncoding::Native);
  camada::SMTExprRef rV = solver->mkFPFromBin(
      "0111111111101111111111111111111111111111111111111111111111111111", 11,
      camada::FPEncoding::Native);

  camada::SMTExprRef xE = solver->mkEqual(x, xV);
  camada::SMTExprRef yE = solver->mkEqual(y, yV);
  camada::SMTExprRef rE = solver->mkEqual(r, rV);

  solver->addConstraint(xE);
  solver->addConstraint(yE);
  solver->addConstraint(rE);

  camada::SMTExprRef mul = solver->mkFPMul(x, y, roundingMode);
  camada::SMTExprRef eq = solver->mkEqual(mul, r);
  camada::SMTExprRef notEq = solver->mkNot(eq);

  solver->addConstraint(notEq);
  camada::checkResult result = solver->check();

  if (result == camada::checkResult::SAT) {
    /* Query the model for the value of the exprs */

    /* Dump the model */
    solver->dumpModel();

  } else if (result == camada::checkResult::UNSAT) {
    /* The formula is unsatisfiable */
  } else if (result == camada::checkResult::UNKNOWN) {
    /* Timeout (see setTimeout) or the solver gave up on the formula */
  }
}
```

## More Examples

The regression tests are also a good source of small usage examples:

- [`regression/simple.test.h`](regression/simple.test.h)
- [`regression/array.test.h`](regression/array.test.h)
- [`regression/fp.test.h`](regression/fp.test.h)
- [`regression/tuple.test.h`](regression/tuple.test.h)

Backend-specific feature coverage is also demonstrated in:

- [`regression/cvc5.test.cpp`](regression/cvc5.test.cpp)
- [`regression/mathsat.test.cpp`](regression/mathsat.test.cpp)
- [`regression/yices.test.cpp`](regression/yices.test.cpp)
- [`regression/z3.test.cpp`](regression/z3.test.cpp)

## Benchmarking

Camada includes a standalone benchmark driver:

- [`regression/bench/main.cpp`](regression/bench/main.cpp)
- [`scripts/compare-bench.py`](scripts/compare-bench.py)

Typical local workflow:

```bash
schedtool -a 5 -n 20 -e ./build/bin/camada-bench bitwuzla 200
python3 scripts/compare-bench.py ./build/bin/camada-bench 200
```

This runs repeated pinned benchmark samples, computes medians, and compares the
result against [`scripts/baseline.txt`](scripts/baseline.txt).
The benchmark output also records retained RSS (`rss_after_kb` and
`rss_delta_kb`) alongside timing data.
