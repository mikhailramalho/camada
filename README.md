[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg)](https://www.apache.org/licenses/LICENSE-2.0)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/7eef16a1313d4ba8801a21e767a0fb25)](https://app.codacy.com/manual/mikhail-ramalho/camada?utm_source=github.com&utm_medium=referral&utm_content=mikhailramalho/camada&utm_campaign=Badge_Grade_Dashboard) [![Linux Build](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml) [![MacOS Build](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml)

# Camada

Camada (“layer” in Portuguese) is a permissively licensed open-source C++ library written in modern C++11 for SMT solving.

Camada aims to provide a unified API for several SMT solvers while also adding some missing features to all supported solvers:
- [x] A floating-point encoding layer using bit-vectors.
- [ ] A tuple encoding layer.
- [ ] A array encoding layer.

## Supported backends

| Backend    | Minimum version |
| ---------- | :-------------: |
| [Boolector](https://boolector.github.io/)  |  3.2.1          |
| [CVC5](https://cvc5.github.io/)            |  1.8            |
| [MathSAT](https://mathsat.fbk.eu/)         |  5.6.3          |
| [STP](https://stp.github.io/)              |  > 2.3.3 *      |
| [Yices](https://yices.csl.sri.com/)        |  2.6.1          |
| [Z3](https://github.com/Z3Prover/z3)       |  4.8.9          |

\* At least commit [9a59a72e](https://github.com/stp/stp/commit/9a59a72e82d67cefeb88d8baa34965f70acb5d1c)
