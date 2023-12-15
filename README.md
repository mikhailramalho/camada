[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg)](https://www.apache.org/licenses/LICENSE-2.0)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/7eef16a1313d4ba8801a21e767a0fb25)](https://app.codacy.com/manual/mikhail-ramalho/camada?utm_source=github.com&utm_medium=referral&utm_content=mikhailramalho/camada&utm_campaign=Badge_Grade_Dashboard) [![Linux Build](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml) [![MacOS Build](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml)

# Camada

Camada (“layer” in Portuguese) is a permissively licensed open-source C++11 library that serves as a wrapper for six popular SMT (Satisfiability Modulo Theories) solvers: Boolector, STP, Yices, MathSAT, CVC5, and Z3. It provides a unified interface for interacting with these solvers, making it easier for developers to work with SMT in their projects.

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

You can use the provided script in the tools directory to download and build the supported solvers. Run the following commands from the root of the repository:
```bash
./scripts/get-deps.py
```
By default, the script will only download and build permissively licensed solvers (Boolector, CVC5, STP, and Z3); if you want to download all solvers, use:
```bash
./scripts/get-deps.py -a
```
The script also offers the option to download and build individual solvers, `./scripts/get-deps.py -h` for more detailed options.

This script will download and set up the necessary solver binaries within a directory named `deps/install` inside the Camada codebase. You won't be making any changes to your system configuration.

The `deps/install` directory will contain the binaries for the supported solvers, and Camada will use them from this location during execution.

## Supported backends

| Backend    | Minimum version | Native floating-point support |
| ---------- | :-------------: | :-------------: |
| [Boolector](https://boolector.github.io/)  |  3.2.1          |   |
| [CVC5](https://cvc5.github.io/)            |  1.8            | ✔️ |
| [MathSAT](https://mathsat.fbk.eu/)         |  5.6.3          | ✔️<sup>2</sup> |
| [STP](https://stp.github.io/)              |  > 2.3.3<sup>1</sup>      |   |
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
