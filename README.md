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

The library is designed to make solver switching cheap while still filling
feature gaps in backends that are missing parts of the SMT-LIB surface.

Current encoded/common-layer features:

- floating-point fallback via bit-vector encoding
- array support, with some remaining tuple-related gaps
- tuple encoding layer: planned for backends without native tuple support

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
- `-DCAMADA_DOWNLOAD_DEPENDENCIES=ALL`
- `-DCAMADA_SOLVER_<NAME>_ENABLE=ON/OFF` to control enabled backends

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
- `Bitwuzla` uses the prebuilt static release archive from `0.9.0`.
- `Z3` uses the prebuilt release archive from `z3-4.16.0`.
- `CVC5` uses the prebuilt static release archive from `cvc5-1.3.3`.
- `Yices` uses a source build.
- `GMP` uses a source build when it is needed by downloaded dependencies and no
  suitable staged copy is already available.
- `MathSAT` uses the vendor-provided prebuilt archive from `5.6.15`.
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
| [Bitwuzla](https://bitwuzla.github.io/)    |  0.9.0          | ✔️ |
| [CVC5](https://cvc5.github.io/)            |  1.0.8          | ✔️ |
| [MathSAT](https://mathsat.fbk.eu/)         |  5.6.3          | ✔️<sup>1</sup> |
| [STP](https://stp.github.io/)              |  2.3.4          |   |
| [Yices](https://yices.csl.sri.com/)        |  2.6.1          |   |
| [Z3](https://github.com/Z3Prover/z3)       |  4.16.0         | ✔️ |

<sup>1</sup> `fp.fma` and `fp.rem` are bit-blasted when using MathSAT because
it does not support these operations natively. `ROUND_TO_AWAY` is also not
supported by the native MathSAT floating-point API and aborts with an error if
requested.

## API Overview

Camada currently provides public APIs for:

- booleans
- bit-vectors
- integers and reals on supporting backends
- floating-point
- rounding modes
- arrays
- uninterpreted functions on supporting backends
- incremental solving (`push`/`pop`)
- model queries for supported value kinds

Partially backend-dependent:

- tuples
  - supported natively on `CVC5` and `Z3`
  - unsupported on `Bitwuzla`, `MathSAT`, `STP`, and `Yices`

- quantifiers
  - supported on `Bitwuzla`, `CVC5`, and `Z3`
  - implemented but still unreliable on `MathSAT` in the current setup
  - unsupported on `STP` and `Yices`
- integers/reals
  - supported on `CVC5`, `MathSAT`, `Yices`, and `Z3`
  - unsupported on `Bitwuzla` and `STP`
- uninterpreted functions
  - supported on `Bitwuzla`, `CVC5`, `MathSAT`, `Yices`, and `Z3`
  - unsupported on `STP`

Array support is currently partial in the larger structured-data sense:

- plain SMT arrays are supported
- backend-specific array gaps such as `Array<Idx, Bool>` are handled
- arrays of tuples remain part of the unfinished tuple work

## Backend Caveats

Camada tries to hide backend differences where practical, but a few solver
limitations still matter in day-to-day use.

- `MathSAT`
  - `reset()` is currently weaker than on the other backends. Reusing the same
    symbol names with different sorts after a reset is still unreliable.
  - quantifiers are implemented in the wrapper, but the current backend setup
    is still unreliable for them.
  - native floating-point support has gaps: `fp.fma` and `fp.rem` are lowered
    through the common bit-vector path, and `ROUND_TO_AWAY` is not supported by
    the native MathSAT FP API.
- `STP`
  - only the bit-vector / array fragment is a natural fit. Integer, real,
    quantifier, and native floating-point support are not available.
  - constant arrays and boolean arrays are adapted internally by the wrapper,
    so some behavior is implemented through backend-specific lowering.
- `Yices`
  - there is no native floating-point support, so FP always goes through
    Camada's bit-vector encoding.
  - constant arrays are implemented with a backend-native lambda encoding.
- `Bitwuzla`
  - integers and reals are not supported.
  - quantifiers are available, but the strongest coverage in Camada is still in
    the quantifier-free fragments.
- `CVC5` and `Z3`
  - these are currently the most complete backends for the public Camada API.

## Recommended Usage

- Prefer `CVC5` or `Z3` if you want the broadest feature coverage with the
  fewest backend-specific caveats.
- Prefer `Bitwuzla` or `STP` for bit-vector-heavy workloads.
- Prefer `Bitwuzla` when you also need native floating-point.
- Prefer `STP` when you only need the bit-vector/array fragment.
- Treat `MathSAT` as usable, but be cautious with `reset()`, quantifiers, and
  native floating-point edge cases.
- Use explicit `FPEncoding` when creating floating-point and rounding-mode
  sorts/constants so the chosen native-vs-BV representation is obvious at the
  call site.

## Design Notes

### Handle Lifetime

Expression and sort handles are solver-owned. Any `SMTExprRef` or `SMTSortRef`
obtained from a solver becomes invalid after:

- `solver->reset()`
- solver destruction

Handles must not be reused across those boundaries.

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

### Backend-Specific Adaptation

Camada also smooths over backend quirks where practical. For example:

- MathSAT and STP now lower `Array<Idx, Bool>` through backend `Array<Idx, BV1>`
  representations internally
- Yices constant arrays use a backend-native lambda encoding instead of a full
  store chain
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

## Implementation Details

Camada is designed as a wrapper library to simplify the usage of multiple SMT solvers. It provides a common interface for interacting with these solvers, allowing developers to switch between them seamlessly without changing their codebase.

Camada is based on the backend written for [ESBMC](https://github.com/esbmc/esbmc) so some of the implementation decisions were geared towards the verification of C programs, in particular, camada diverges from the SMT standard in:
- `fp.neg` supports negative `NaN`s. See https://github.com/Z3Prover/z3/issues/4466 for a more detailed discussion.

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
    /* Something went wrong when checking the formula, timeouts, etc. */
  }
}
```

## More Examples

The regression tests are also a good source of small usage examples:

- [`regression/simple.test.h`](/home/mgadelha/tools/camada/regression/simple.test.h)
- [`regression/array.test.h`](/home/mgadelha/tools/camada/regression/array.test.h)
- [`regression/fp.test.h`](/home/mgadelha/tools/camada/regression/fp.test.h)

Backend-specific feature coverage is also demonstrated in:

- [`regression/cvc5.test.cpp`](/home/mgadelha/tools/camada/regression/cvc5.test.cpp)
- [`regression/mathsat.test.cpp`](/home/mgadelha/tools/camada/regression/mathsat.test.cpp)
- [`regression/yices.test.cpp`](/home/mgadelha/tools/camada/regression/yices.test.cpp)
- [`regression/z3.test.cpp`](/home/mgadelha/tools/camada/regression/z3.test.cpp)

## Benchmarking

Camada includes a standalone benchmark driver:

- [`regression/bench/main.cpp`](/home/mgadelha/tools/camada/regression/bench/main.cpp)
- [`scripts/compare-bench.py`](/home/mgadelha/tools/camada/scripts/compare-bench.py)

Typical local workflow:

```bash
python3 scripts/compare-bench.py ./build/bin/camada-bench 200
```

This runs repeated pinned benchmark samples, computes medians, and compares the
result against [`scripts/baseline.txt`](/home/mgadelha/tools/camada/scripts/baseline.txt).
