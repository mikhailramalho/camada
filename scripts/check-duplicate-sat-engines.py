#!/usr/bin/env python3
"""Fail when two copies of one SAT engine reach a single static link.

Backends ship their SAT solver differently: CVC5 keeps CaDiCaL in its own
libcadical.a, Bitwuzla's upstream prebuilt compiles CaDiCaL *into*
libbitwuzla.a. Linking both statically keeps one definition of each shared
symbol, but each library's code still computes member offsets from the
headers it was built against. CVC5 builds CaDiCaL with -DQUIET, which drops
two members from the middle of CaDiCaL::Internal, so the survivor reads every
later field at the wrong offset -- Bitwuzla sized a Walker allocation from
garbage and asked for 8 GB while solving one VCC.

Nothing about that is visible at link time: no duplicate-symbol error, no
warning, and a test suite that never reaches the affected path still passes.
So this checks the archives directly, for the shape of the bug rather than
this one instance of it, and reports which engine and which archives.

Usage:
    check-duplicate-sat-engines.py <dir-or-archive> [...]
"""

import argparse
import hashlib
import pathlib
import re
import subprocess
import sys

# Namespace or symbol prefixes that identify a bundled SAT engine. A second
# archive defining the same engine's *strong* symbols is the failure.
SAT_ENGINES = {
    "CaDiCaL": re.compile(r"^_ZN7CaDiCaL"),
    "CryptoMiniSat": re.compile(r"^_ZN5CMSat"),
    "Kissat": re.compile(r"^kissat_"),
    "MiniSat": re.compile(r"^_ZN7Minisat"),
    "Glucose": re.compile(r"^_ZN7Glucose"),
}


def _nm(archive, globals_only):
    args = ["nm", "--defined-only"] + (["-g"] if globals_only else [])
    try:
        return subprocess.run(args + [str(archive)],
                              capture_output=True, text=True,
                              check=False).stdout
    except FileNotFoundError:
        sys.exit("error: nm not found; this check needs binutils")


def strong_symbols(archive, globals_only=True):
    """Defined, non-weak symbols. Weak ones are inline/template definitions
    that the linker is meant to merge, so they are not a conflict.

    globals_only=False also returns file-local symbols, which is how a
    deliberately localized copy of an engine is detected: objcopy demotes
    T to t, and the whole point of doing that is that the linker can no
    longer confuse it with anyone else's copy."""
    symbols = set()
    for line in _nm(archive, globals_only).splitlines():
        fields = line.split()
        # "<addr> <type> <name>"; weak/vague linkage is V, W, u, v. Local
        # definitions are the lowercase forms of the same letters.
        if len(fields) >= 3 and fields[-2] in ("T", "D", "B", "R",
                                               "t", "d", "b", "r"):
            symbols.add(fields[-1])
    return symbols


def engines_in(archive):
    """Which SAT engines this archive defines, how many symbols each, and
    whether those symbols are exported or localized.

    A localized copy is not a conflict: the linker cannot substitute it for
    anyone else's, which is the whole reason a build localizes one. Camada
    does exactly this for CryptoMiniSat's CaDiCaL fork, which would otherwise
    collide with the one Bitwuzla and CVC5 share."""
    exported = strong_symbols(archive)
    everything = strong_symbols(archive, globals_only=False)
    found = {}
    for engine, pattern in SAT_ENGINES.items():
        total = sum(1 for s in everything if pattern.match(s))
        if not total:
            continue
        shown = sum(1 for s in exported if pattern.match(s))
        found[engine] = (total, shown > 0)
    return found


def _digest(archive):
    """Content hash, to tell one engine staged twice from two builds of it."""
    return hashlib.sha256(archive.read_bytes()).hexdigest()


# Intermediate build trees hold the same archive again under its source
# directory -- deps/src/<pkg>/build/, _deps/<pkg>-src/build/ -- and those
# copies are never linked, only their staged results are. Counting them
# reports a conflict for every dependency Camada builds from source.
_BUILD_SCRATCH = ("/deps/src/", "/_deps/")


def collect(paths):
    """Expand directories to the archives under them; keep files as given.

    Archives under an intermediate build tree are skipped: a directory
    explicitly named on the command line is always searched, so an
    intermediate can still be inspected deliberately."""
    archives = []
    for path in paths:
        p = pathlib.Path(path)
        if p.is_dir():
            root = str(p.resolve())
            for found in sorted(p.rglob("*.a")):
                rest = str(found.resolve())[len(root):]
                if any(marker in rest for marker in _BUILD_SCRATCH):
                    continue
                archives.append(found)
        elif p.is_file():
            archives.append(p)
        else:
            sys.exit(f"error: no such file or directory: {p}")
    return archives


def main():
    """Entry point."""
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paths", nargs="+",
                        help="static archives, or directories to search for *.a")
    parser.add_argument("--verbose", action="store_true",
                        help="list every archive that provides a SAT engine")
    args = parser.parse_args()

    archives = collect(args.paths)
    if not archives:
        sys.exit("error: no static archives found")

    # engine -> [(archive, symbol count, exported?)]
    providers = {}
    for archive in archives:
        for engine, (count, exported) in engines_in(archive).items():
            providers.setdefault(engine, []).append((archive, count, exported))

    if args.verbose:
        for engine in sorted(providers):
            print(f"{engine}:")
            for archive, count, exported in providers[engine]:
                note = "" if exported else "  [localized, cannot collide]"
                print(f"  {archive}  ({count} symbols){note}")

    sys.stdout.flush()

    # Only exported copies can collide. A localized one is invisible to the
    # linker's symbol resolution, so it cannot be substituted for another
    # library's copy however much its layout differs.
    #
    # Byte-identical archives are one engine staged twice rather than two
    # implementations: the link picks one and every offset still agrees.
    conflicts = {}
    for engine, found in providers.items():
        exported = [(a, c) for a, c, is_exported in found if is_exported]
        digests = {_digest(a) for a, _ in exported}
        if len(digests) > 1:
            conflicts[engine] = exported
    if not conflicts:
        localized = sum(1 for f in providers.values()
                        for _, _, is_exported in f if not is_exported)
        extra = (f", {localized} localized copy/copies ignored"
                 if localized else "")
        print(f"OK: {len(archives)} archive(s) checked, "
              f"no SAT engine exported more than once{extra}")
        return 0

    for engine, found in sorted(conflicts.items()):
        print(f"\nERROR: {engine} is exported by {len(found)} archives:",
              file=sys.stderr)
        for archive, count in found:
            print(f"  {archive}  ({count} strong symbols)", file=sys.stderr)
    print("\nA link keeps one definition of each shared symbol while every "
          "library\nkeeps the field offsets it was compiled with. Build the "
          "backends against\none copy of the engine; Camada does this for "
          "CaDiCaL whenever the Bitwuzla\nand CVC5 backends are both enabled.",
          file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
