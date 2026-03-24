[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg)](https://www.apache.org/licenses/LICENSE-2.0)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/7eef16a1313d4ba8801a21e767a0fb25)](https://app.codacy.com/manual/mikhail-ramalho/camada?utm_source=github.com&utm_medium=referral&utm_content=mikhailramalho/camada&utm_campaign=Badge_Grade_Dashboard) [![Linux Build](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml) [![MacOS Build](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml)

# Camada

Camada (“layer” in Portuguese) is a permissively licensed open-source C++11 library that serves as a wrapper for six popular SMT (Satisfiability Modulo Theories) solvers: Bitwuzla, STP, Yices, MathSAT, CVC5, and Z3. It provides a unified interface for interacting with these solvers, making it easier for developers to work with SMT in their projects.

Camada aims to provide a unified API for several SMT solvers while also adding some missing features to all supported solvers:
- [x] A floating-point encoding layer using bit-vectors.
- [ ] A tuple encoding layer.
- [ ] A array encoding layer.

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

# Create a build directory and navigate into it
mkdir build && cd build

# Run CMake to configure the project
cmake ..

# Build the library
make

# Install Camada
make install
```

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
- `PERMISSIVE-ONLY`: download only solvers with permissive licenses
  (`Bitwuzla`, `CVC5`, `STP`, and `Z3`).

Downloaded sources and locally installed solver artifacts are stored under
`<build-dir>/deps/src` and `<build-dir>/deps/install`.

When CMake downloads dependencies itself:
- `Bitwuzla` uses the prebuilt static release archive from `0.9.0`.
- `Z3` uses the prebuilt release archive from `z3-4.16.0`.
- `CVC5` uses the prebuilt static release archive from `cvc5-1.3.3`.
- `Yices` uses a source build.
- `MathSAT` uses the vendor-provided prebuilt archive from `5.6.15`.
- `STP` still falls back to a source build. The `2.3.4_cadical` GitHub release
  only ships a standalone `stp` executable, not the headers and libraries that
  Camada needs to link against the STP C++ API.
- `STP`, `CryptoMiniSat`, `GMP`, and `Minisat` still build from
  source.

The `<build-dir>/deps/install` directory will contain the binaries for the supported solvers, and Camada will use them from this location during execution.

## Supported backends

| Backend    | Minimum version | Native floating-point support |
| ---------- | :-------------: | :-------------: |
| [Bitwuzla](https://bitwuzla.github.io/)    |  0.9.0          |   |
| [CVC5](https://cvc5.github.io/)            |  1.0.8          | ✔️ |
| [MathSAT](https://mathsat.fbk.eu/)         |  5.6.3          | ✔️<sup>2</sup> |
| [STP](https://stp.github.io/)              |  2.3.4          |   |
| [Yices](https://yices.csl.sri.com/)        |  2.6.1          |   |
| [Z3](https://github.com/Z3Prover/z3)       |  4.8.9          | ✔️ |

<sup>1</sup> At least commit [9a59a72e](https://github.com/stp/stp/commit/9a59a72e82d67cefeb88d8baa34965f70acb5d1c)

<sup>2</sup> `fp.fma` and `fp.rem` are bit-blast when using MathSAT and it doesn't support these operations natively. 

## Implementation Details

Camada is designed as a wrapper library to simplify the usage of multiple SMT solvers. It provides a common interface for interacting with these solvers, allowing developers to switch between them seamlessly without changing their codebase.

Camada is based on the backend written for [ESBMC](https://github.com/esbmc/esbmc) so some of the implementation decisions were geared towards the verification of C programs, in particular, camada diverges from the SMT standard in:
- `fp.neg` supports negative `NaN`s. See https://github.com/Z3Prover/z3/issues/4466 for a more detailed discussion.

### Usage Example

```cpp
#include <camada/camada.h>

int main() {
  // Create a solver instance (example using Z3)
  auto solver = camada::createZ3Solver();

  // This flag controls if you want to bit-blast floating-point, using Camada's internal bit-vector encoding
  // Floating-point bitblast is always enabled for solvers that don't support floating-point natively.
  /* solver->useCamadaFP = true; */

  // Add assertions, check satisfiability, etc.
  camada::SMTSortRef fp64sort = solver->mkFPSort(11, 52);
  camada::SMTExprRef roundingMode =
      solver->mkRM(camada::RM::ROUND_TO_MINUS_INF);

  camada::SMTExprRef x = solver->mkSymbol("x", fp64sort);
  camada::SMTExprRef y = solver->mkSymbol("y", fp64sort);
  camada::SMTExprRef r = solver->mkSymbol("r", fp64sort);

  camada::SMTExprRef xV = solver->mkFPFromBin(
      "0111011101100100111000010001001010111000010010111000100101001010", 11);
  camada::SMTExprRef yV = solver->mkFPFromBin(
      "0100100101001110001001011011001100110001111010011101010010000001", 11);
  camada::SMTExprRef rV = solver->mkFPFromBin(
      "0111111111101111111111111111111111111111111111111111111111111111", 11);

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
