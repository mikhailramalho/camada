#!/usr/bin/env python3

import argparse
import re
import sys
from pathlib import Path


LINE_RE = re.compile(
    r"^benchmark=(?P<name>\S+)\s+backend=(?P<backend>\S+)\s+iterations="
    r"(?P<iterations>\d+)\s+total_ns=(?P<total_ns>\d+)\s+ns_per_iter="
    r"(?P<ns_per_iter>\d+(?:\.\d+)?)$"
)


def parse_file(path: Path) -> dict[str, dict[str, object]]:
    results: dict[str, dict[str, object]] = {}
    for lineno, raw_line in enumerate(path.read_text().splitlines(), start=1):
        line = raw_line.strip()
        if not line:
            continue
        match = LINE_RE.match(line)
        if not match:
            continue
        data = match.groupdict()
        results[data["name"]] = {
            "backend": data["backend"],
            "iterations": int(data["iterations"]),
            "total_ns": int(data["total_ns"]),
            "ns_per_iter": float(data["ns_per_iter"]),
            "lineno": lineno,
        }
    return results


def pct_change(old: float, new: float) -> float:
    return ((new - old) / old) * 100.0


def format_change(name: str, baseline: float, new: float) -> str:
    delta = pct_change(baseline, new)
    word = "improved" if new < baseline else "regressed" if new > baseline else "unchanged"
    return (
        f"{name}: {word} "
        f"({baseline:.2f} -> {new:.2f} ns/iter, {delta:+.2f}%)"
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compare two camada-bench output files."
    )
    parser.add_argument("baseline", type=Path, help="Baseline benchmark output file")
    parser.add_argument("new", type=Path, help="New benchmark output file")
    args = parser.parse_args()

    baseline = parse_file(args.baseline)
    new = parse_file(args.new)

    if not baseline:
        print(f"No benchmark lines found in {args.baseline}", file=sys.stderr)
        return 1
    if not new:
        print(f"No benchmark lines found in {args.new}", file=sys.stderr)
        return 1

    common_names = sorted(set(baseline) & set(new))
    baseline_only = sorted(set(baseline) - set(new))
    new_only = sorted(set(new) - set(baseline))

    improved: list[str] = []
    regressed: list[str] = []
    unchanged: list[str] = []

    for name in common_names:
        old = float(baseline[name]["ns_per_iter"])
        cur = float(new[name]["ns_per_iter"])
        if cur < old:
            improved.append(format_change(name, old, cur))
        elif cur > old:
            regressed.append(format_change(name, old, cur))
        else:
            unchanged.append(format_change(name, old, cur))

    if regressed:
        print("Regressed:")
        for line in regressed:
            print(f"  {line}")

    if improved:
        if regressed:
            print()
        print("Improved:")
        for line in improved:
            print(f"  {line}")

    if unchanged:
        if regressed or improved:
            print()
        print("Unchanged:")
        for line in unchanged:
            print(f"  {line}")

    if baseline_only:
        print()
        print("Only in baseline:")
        for name in baseline_only:
            print(f"  {name}")

    if new_only:
        print()
        print("Only in new:")
        for name in new_only:
            print(f"  {name}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
