[![Apache 2.0 License](https://img.shields.io/badge/license-Apache--2-brightgreen.svg)](https://www.apache.org/licenses/LICENSE-2.0)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/7eef16a1313d4ba8801a21e767a0fb25)](https://app.codacy.com/manual/mikhail-ramalho/camada?utm_source=github.com&utm_medium=referral&utm_content=mikhailramalho/camada&utm_campaign=Badge_Grade_Dashboard) [![Linux Build](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-linux.yml) [![MacOS Build](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml/badge.svg)](https://github.com/mikhailramalho/camada/actions/workflows/build-macos.yml)

# Camada

Camada ("layer" in Portuguese) is a permissively licensed C++17 wrapper that
exposes one API over several SMT solvers: Bitwuzla, CVC5, MathSAT, STP, Yices,
Z3, and any external solver speaking SMT-LIB v2 on stdin/stdout.

It makes switching solvers cheap, and fills gaps where a backend is missing
part of the SMT-LIB surface:

- floating-point encoded over bit-vectors, for backends without native FP or
  on request (`FPEncoding::BV`)
- constant arrays lowered lazily where a backend has no usable native one
- tuples lowered per field where a backend has no datatypes
- fixed-point arithmetic, overflow predicates, assumption-based solving,
  timeouts, and sparse array models on every backend
- an opt-in Ackermann array encoding, for when a backend's array solver is
  the bottleneck
- `supports(SolverFeature)` to ask what a backend can do, and
  `getSolverKind()` to ask which backend it is

Camada grew out of [ESBMC](https://github.com/esbmc/esbmc)'s solver backend, so
some choices, such as IEEE-754 NaN payload handling, favour verifying C code.

## Building

Requires CMake 3.24 and a C++17 compiler.

```bash
git clone https://github.com/mikhailramalho/camada.git
cd camada
cmake -S . -B build -DCAMADA_DOWNLOAD_DEPENDENCIES=ALL
cmake --build build
cmake --install build
```

`CAMADA_DOWNLOAD_DEPENDENCIES=ALL` downloads and builds the solvers it cannot
find (`PERMISSIVE` limits that to permissively licensed ones, `OFF` uses only
what is installed). Backends are toggled with
`-DCAMADA_SOLVER_<NAME>_ENABLE=IFAVAILABLE/ON/OFF`.

Building the solvers from source needs extra tools (meson, autotools, flex,
bison and more). See [docs/building.md](docs/building.md) for those, the full
list of options, and how each dependency is fetched.

## Backend support

| Feature | Bitwuzla | CVC5 | MathSAT | STP | Yices | Z3 |
| ------- | :------: | :--: | :-----: | :-: | :---: | :-: |
| Minimum version | 0.9.1 | 1.0.8 | 5.6.3 | 2.4.0 | 2.6.1 | 4.13.3 |
| Bit-vectors, booleans, arrays | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ |
| Integers / reals |   | ✔️ | ✔️ |   | ✔️ | ✔️ |
| Native FP | ✔️<sup>1</sup> | ✔️<sup>1</sup> | ✔️<sup>2</sup> |   |   | ✔️ |
| FP over bit-vectors | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ | ✔️ |
| Uninterpreted functions | ✔️ | ✔️ | ✔️ |   | ✔️ | ✔️ |
| Native tuples |   | ✔️ |   |   |   | ✔️ |
| Native constant arrays | ✔️<sup>3</sup> | ✔️ | ✔️ |   |   | ✔️ |
| Quantifiers | ✔️ | ✔️ |   |   |   | ✔️ |
| Unsat assumptions | ✔️<sup>4</sup> | ✔️<sup>4</sup> | ✔️ |   | ✔️ | ✔️ |
| Array models | ✔️ | ✔️ | ✔️ |   | ✔️ | ✔️ |

Everything not native is still available through Camada's own lowering, so
tuples and constant arrays work on every backend.

<sup>1</sup> Only some formats: SymFPU underneath assumes
`exponentWidth <= significandWidth`.
<sup>2</sup> `fp.fma` and `fp.rem` go through the bit-vector path;
`ROUND_TO_AWAY` is unsupported.
<sup>3</sup> Returns UNKNOWN when a constant array survives Bitwuzla's
preprocessing; `ConstArrayLowering::Lazy` avoids it.
<sup>4</sup> Opt-in at creation (`SolverConfig::UseUnsatAssumptions`).

Per-backend caveats, the FP format table, and the SMT-LIB pipe backend are in
[docs/backends.md](docs/backends.md).

## Example

```cpp
#include <camada/camada.h>

int main() {
  auto solver = camada::createZ3Solver();

  auto bv8 = solver->mkBVSort(8);
  auto x = solver->mkSymbol("x", bv8);
  auto y = solver->mkSymbol("y", bv8);

  // x + y == 7 and x > y (unsigned)
  solver->addConstraint(
      solver->mkEqual(solver->mkBVAdd(x, y), solver->mkBVFromDec(7, 8)));
  solver->addConstraint(solver->mkBVUgt(x, y));

  if (solver->check() == camada::CheckResult::SAT) {
    auto xv = solver->getBV(x); // SMTResult<...>: reports, never aborts
    solver->dumpModel();
  }
}
```

Expressions and sorts belong to the solver that made them and die on
`reset()` or destruction; using a stale handle aborts with a diagnostic rather
than reading freed memory. A solver is not safe to share between threads. See
[docs/design.md](docs/design.md) for these contracts, the FP fallback, caching,
and NaN handling.

The regression tests are the best source of further examples, starting with
[`regression/simple.test.h`](regression/simple.test.h),
[`array.test.h`](regression/array.test.h),
[`fp.test.h`](regression/fp.test.h) and
[`tuple.test.h`](regression/tuple.test.h).

## Benchmarking

`build/bin/camada-bench <solver> <iterations>` runs the benchmark driver
([`regression/bench/main.cpp`](regression/bench/main.cpp)).
[`scripts/compare-bench.py`](scripts/compare-bench.py) compares medians
against a baseline, which `--write-baseline` records first (to
`scripts/baseline.txt` by default).
