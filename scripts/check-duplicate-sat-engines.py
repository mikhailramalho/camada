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


def strong_symbols(archive):
    """Defined, non-weak symbols. Weak ones are inline/template definitions
    that the linker is meant to merge, so they are not a conflict."""
    try:
        out = subprocess.run(
            ["nm", "-g", "--defined-only", str(archive)],
            capture_output=True, text=True, check=False).stdout
    except FileNotFoundError:
        sys.exit("error: nm not found; this check needs binutils")

    symbols = set()
    for line in out.splitlines():
        fields = line.split()
        # "<addr> <type> <name>"; weak/vague linkage is V, W, u, or v.
        if len(fields) >= 3 and fields[-2] in ("T", "D", "B", "R"):
            symbols.add(fields[-1])
    return symbols


def engines_in(archive):
    """Which SAT engines this archive defines, and how many symbols each."""
    symbols = strong_symbols(archive)
    found = {}
    for engine, pattern in SAT_ENGINES.items():
        count = sum(1 for s in symbols if pattern.match(s))
        if count:
            found[engine] = count
    return found


def _digest(archive):
    """Content hash, to tell one engine staged twice from two builds of it."""
    return hashlib.sha256(archive.read_bytes()).hexdigest()


def collect(paths):
    """Expand directories to the archives under them; keep files as given."""
    archives = []
    for path in paths:
        p = pathlib.Path(path)
        if p.is_dir():
            archives.extend(sorted(p.rglob("*.a")))
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

    # engine -> [(archive, symbol count)]
    providers = {}
    for archive in archives:
        for engine, count in engines_in(archive).items():
            providers.setdefault(engine, []).append((archive, count))

    if args.verbose:
        for engine in sorted(providers):
            print(f"{engine}:")
            for archive, count in providers[engine]:
                print(f"  {archive}  ({count} symbols)")

    sys.stdout.flush()

    # Byte-identical archives are one engine staged twice, not two
    # implementations: the link picks one and every offset still agrees.
    # Only distinct content can corrupt a layout.
    conflicts = {}
    for engine, found in providers.items():
        digests = {_digest(a) for a, _ in found}
        if len(digests) > 1:
            conflicts[engine] = found
    if not conflicts:
        print(f"OK: {len(archives)} archive(s) checked, "
              f"no SAT engine provided more than once")
        return 0

    for engine, found in sorted(conflicts.items()):
        print(f"\nERROR: {engine} is defined by {len(found)} archives:",
              file=sys.stderr)
        for archive, count in found:
            print(f"  {archive}  ({count} strong symbols)", file=sys.stderr)
    print("\nA static link keeps one definition of each shared symbol while "
          "every\nlibrary keeps the field offsets it was compiled with. Build "
          "the backends\nagainst one copy of the engine -- for CaDiCaL, "
          "configure with\n-DCAMADA_SHARED_CADICAL=ON.", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
