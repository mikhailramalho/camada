[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg)](https://www.apache.org/licenses/LICENSE-2.0)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/7eef16a1313d4ba8801a21e767a0fb25)](https://app.codacy.com/manual/mikhail-ramalho/camada?utm_source=github.com&utm_medium=referral&utm_content=mikhailramalho/camada&utm_campaign=Badge_Grade_Dashboard)

# Camada

Camada (“layer” in Portuguese) is a permissively licensed open-source C++ library written in modern C++11 for SMT solving.

Camada aims to provide a unified API for several SMT solvers while also adding some missing features to all supported solvers:
* A floating-point encoding layer using bit-vectors.
* A tuple encoding layer.
* A array encoding layer.

## Supported backends

| Backend    | Minimum version | Build Linux | Build MacOS |
| ---------- | --------------- | ----------- | ----------- |
| [Boolector](https://boolector.github.io/)  |  3.2.1          | ![Linux Boolector Build](https://github.com/mikhailramalho/camada/workflows/Linux%20Boolector%20Build/badge.svg)| ![MacOS Boolector Build](https://github.com/mikhailramalho/camada/workflows/MacOS%20Boolector%20Build/badge.svg) |
| [CVC4](https://cvc4.github.io/)       |  1.8            | ![Linux CVC4 Build](https://github.com/mikhailramalho/camada/workflows/Linux%20CVC4%20Build/badge.svg) | ![MacOS CVC4 Build](https://github.com/mikhailramalho/camada/workflows/MacOS%20CVC4%20Build/badge.svg) |
| [MathSAT](https://mathsat.fbk.eu/)    |  5.6.3          | ![Linux MathSAT Build](https://github.com/mikhailramalho/camada/workflows/Linux%20MathSAT%20Build/badge.svg) | ![MacOS MathSAT Build](https://github.com/mikhailramalho/camada/workflows/MacOS%20MathSAT%20Build/badge.svg) |
| [STP](https://stp.github.io/)        |  > 2.3.3 *      | ![Linux STP Build](https://github.com/mikhailramalho/camada/workflows/Linux%20STP%20Build/badge.svg) | ![MacOS STP Build](https://github.com/mikhailramalho/camada/workflows/MacOS%20STP%20Build/badge.svg) |
| [Yices](https://yices.csl.sri.com/)      |  2.6.1          | ![Linux Yices Build](https://github.com/mikhailramalho/camada/workflows/Linux%20Yices%20Build/badge.svg) | ![MacOS Yices Build](https://github.com/mikhailramalho/camada/workflows/MacOS%20Yices%20Build/badge.svg) |
| [Z3](https://github.com/Z3Prover/z3)         |  4.8.9          | ![Linux Z3 Build](https://github.com/mikhailramalho/camada/workflows/Linux%20Z3%20Build/badge.svg) | ![MacOS Z3 Build](https://github.com/mikhailramalho/camada/workflows/MacOS%20Z3%20Build/badge.svg) |

\* At least commit [9a59a72e](https://github.com/stp/stp/commit/9a59a72e82d67cefeb88d8baa34965f70acb5d1c)
