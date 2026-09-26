# Building Camada

## Prerequisites

- CMake (Version 3.24 or higher)
- C++ Compiler (Supporting C++17)
- Any of the supported solvers, or the tools below to let Camada build them

Building dependencies from source (`CAMADA_DOWNLOAD_DEPENDENCIES`) also needs:

- `meson` and `ninja` (Bitwuzla)
- `make` and `python3` with the `venv` module (CVC5, which installs its Python
  build dependencies into a venv under its own build tree)
- `autoconf`, `automake`, `libtool`, `m4` and `texinfo` (GMP, Yices)
- `gperf` (Yices), `flex` and `bison` (STP)
- MPFR, as a system library (CVC5 and Bitwuzla link it)

## Configure options

Useful configure options:

- `-DCMAKE_BUILD_TYPE=Release`
- `-DBUILD_SHARED_LIBS=ON/OFF`
- `-DENABLE_WARNINGS=ON/OFF` (default: ON; adds `-Wall -Wextra -pedantic`)
- `-DENABLE_WERROR=ON/OFF` (default: OFF; treat warnings as errors — used by CI)
- `-DCAMADA_ENABLE_REGRESSION=ON/OFF`
- `-DCAMADA_DOWNLOAD_DEPENDENCIES=ALL`
- `-DCAMADA_SOLVER_<NAME>_ENABLE=IFAVAILABLE/ON/OFF` to control enabled
  backends

A shared `libcamada` statically absorbs the backends that ship only static
archives, along with their GMP and CaDiCaL. On Linux a version script keeps
those private, so the library exports Camada's API and nothing else, and a
process that also loads its own `libgmp.so` gets no competing definitions.
macOS still exports them (issue #224).

## Downloading and building the solvers

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
- `Bitwuzla` uses a source build from `0.9.1`.
- `Z3` uses the prebuilt release archive from `z3-4.13.3`.
- `CVC5` uses a source build from `cvc5-1.4.0`.
- `CaDiCaL` uses a source build, shared by every backend that needs it:
  Bitwuzla, CVC5 and STP link one copy, because two copies built with
  different flags disagree on `CaDiCaL::Internal`'s layout.
- `Yices` uses a source build.
- `GMP` uses a source build, and every backend links that one copy (STP and
  MathSAT by path, Yices through `--with-static-gmp`, CVC5 and Bitwuzla through
  their exported link interfaces). With `CAMADA_DOWNLOAD_DEPENDENCIES=OFF`
  the host's GMP is used instead.
- `MathSAT` uses the vendor-provided prebuilt archive from `5.6.17` on
  Linux. macOS stays pinned to `5.6.16`: the `5.6.17` macOS tarball ships
  `libmathsat.a` as a plain `ar` archive of fat Mach-O objects, a layout
  Apple's `ld` rejects.
- `STP` still falls back to a source build of `2.4.1`. The `2.4.1` GitHub
  release only ships a standalone `stp` executable, not the headers and
  libraries that Camada needs to link against the STP C++ API.
- `CryptoMiniSat`, `Minisat`, and `CadiBack` build from source as part of the
  STP dependency chain. CryptoMiniSat links the shared `CaDiCaL` rather than a
  fork of its own.
- `CVC5` is not built on Windows; configuring with it enabled there stops with
  an error.

Sources are fetched as release tarballs rather than git clones. Those named by
a tag are pinned by SHA256; those named by a commit are content-addressed by
the commit itself.

The `<build-dir>/deps/install` directory will contain the staged solver headers,
libraries, and auxiliary artifacts, and Camada will use them from this
location during the build.
