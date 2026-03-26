#!/usr/bin/env python3

import argparse
import math
import os
import re
import statistics
import subprocess
import sys
from pathlib import Path


LINE_RE = re.compile(
    r"^benchmark=(?P<name>\S+)\s+backend=(?P<backend>\S+)\s+iterations="
    r"(?P<iterations>\d+)\s+total_ns=(?P<total_ns>\d+)\s+ns_per_iter="
    r"(?P<ns_per_iter>\d+(?:\.\d+)?)$"
)

DEFAULT_MIN_RUNS = 10
RUNS_PER_CPU = 5


def parse_lines(lines: list[str], source: str) -> dict[str, dict[str, object]]:
    results: dict[str, dict[str, object]] = {}
    for lineno, raw_line in enumerate(lines, start=1):
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
            "source": source,
            "lineno": lineno,
        }
    return results


def parse_file(path: Path) -> dict[str, dict[str, object]]:
    return parse_lines(path.read_text().splitlines(), str(path))


def run_benchmark(
    binary: Path, iterations: int, cpu: int
) -> dict[str, dict[str, object]]:
    cmd = [
        "schedtool",
        "-a",
        str(cpu),
        "-n",
        "20",
        "-e",
        str(binary),
        "bitwuzla",
        str(iterations),
    ]
    proc = subprocess.run(cmd, check=True, capture_output=True, text=True)
    return parse_lines(proc.stdout.splitlines(), f"cpu{cpu}")


def run_benchmarks(
    binary: Path, iterations: int, runs: int
) -> list[dict[str, dict[str, object]]]:
    cpu_count = os.cpu_count() or 1
    results: list[dict[str, dict[str, object]]] = []
    launched = 0

    while launched < runs:
        batch_size = min(cpu_count, runs - launched)
        procs: list[tuple[int, subprocess.Popen[str]]] = []
        for cpu in range(batch_size):
            cmd = [
                "schedtool",
                "-a",
                str(cpu),
                "-n",
                "20",
                "-e",
                str(binary),
                "bitwuzla",
                str(iterations),
            ]
            procs.append(
                (
                    cpu,
                    subprocess.Popen(
                        cmd,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                    ),
                )
            )

        for cpu, proc in procs:
            stdout, stderr = proc.communicate()
            if proc.returncode != 0:
                raise subprocess.CalledProcessError(
                    proc.returncode, proc.args, output=stdout, stderr=stderr
                )
            results.append(parse_lines(stdout.splitlines(), f"cpu{cpu}"))
            launched += 1
            print(f"Completed benchmark {launched}/{runs} on cpu {cpu}", file=sys.stderr)

    return results


def compute_medians(
    runs: list[dict[str, dict[str, object]]],
) -> dict[str, dict[str, object]]:
    names = sorted(set().union(*(run.keys() for run in runs)))
    medians: dict[str, dict[str, object]] = {}

    for name in names:
        samples = [run[name] for run in runs if name in run]
        if not samples:
            continue
        ns_values = [float(sample["ns_per_iter"]) for sample in samples]
        total_values = [int(sample["total_ns"]) for sample in samples]
        iterations = int(samples[0]["iterations"])
        backend = str(samples[0]["backend"])
        medians[name] = {
            "backend": backend,
            "iterations": iterations,
            "total_ns": int(statistics.median(total_values)),
            "ns_per_iter": statistics.median(ns_values),
            "runs": len(samples),
        }

    return medians


def format_benchmark_line(name: str, data: dict[str, object]) -> str:
    return (
        f"benchmark={name} "
        f"backend={data['backend']} "
        f"iterations={data['iterations']} "
        f"total_ns={data['total_ns']} "
        f"ns_per_iter={float(data['ns_per_iter']):.2f}"
    )


def write_baseline(path: Path, medians: dict[str, dict[str, object]]) -> None:
    lines = [
        format_benchmark_line(name, medians[name]) for name in sorted(medians)
    ]
    path.write_text("\n".join(lines) + "\n")


def sign_test_p_value(samples: list[float], baseline: float) -> float:
    gt = sum(1 for sample in samples if sample > baseline)
    lt = sum(1 for sample in samples if sample < baseline)
    n = gt + lt
    if n == 0:
      return 1.0

    k = min(gt, lt)
    tail = sum(math.comb(n, i) for i in range(0, k + 1)) / (2**n)
    return min(1.0, 2.0 * tail)


def pct_change(old: float, new: float) -> float:
    return ((new - old) / old) * 100.0


def format_change(name: str, baseline: float, new: float, p_value: float) -> str:
    delta = pct_change(baseline, new)
    word = "improved" if new < baseline else "regressed" if new > baseline else "unchanged"
    return (
        f"{name}: {word} "
        f"({baseline:.2f} -> {new:.2f} ns/iter, {delta:+.2f}%, p={p_value:.4f})"
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run camada-bench with schedtool in parallel across available "
            "CPUs, compute median per benchmark, and compare against "
            "scripts/baseline.txt."
        )
    )
    parser.add_argument("binary", type=Path, help="Path to camada-bench binary")
    parser.add_argument("iterations", type=int, help="Benchmark iteration count")
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="Write the 10-run medians to scripts/baseline.txt instead of comparing",
    )
    args = parser.parse_args()

    baseline_path = Path(__file__).with_name("baseline.txt")

    cpu_count = os.cpu_count() or 1
    runs_to_execute = max(DEFAULT_MIN_RUNS, cpu_count * RUNS_PER_CPU)
    print(
        f"Running {runs_to_execute} benchmarks across up to {cpu_count} CPUs...",
        file=sys.stderr,
    )
    runs = run_benchmarks(args.binary, args.iterations, runs_to_execute)

    medians = compute_medians(runs)
    if not medians:
        print("No benchmark lines found in benchmark output", file=sys.stderr)
        return 1

    if args.write_baseline:
        write_baseline(baseline_path, medians)
        print(
            f"Wrote baseline medians from {runs_to_execute} runs to {baseline_path}"
        )
        return 0

    baseline = parse_file(baseline_path)
    if not baseline:
        print(f"No benchmark lines found in {baseline_path}", file=sys.stderr)
        return 1

    common_names = sorted(set(baseline) & set(medians))
    baseline_only = sorted(set(baseline) - set(medians))
    median_only = sorted(set(medians) - set(baseline))

    improved: list[str] = []
    regressed: list[str] = []
    unchanged: list[str] = []

    for name in common_names:
        old = float(baseline[name]["ns_per_iter"])
        cur = float(medians[name]["ns_per_iter"])
        samples = [
            float(run[name]["ns_per_iter"]) for run in runs if name in run
        ]
        p_value = sign_test_p_value(samples, old)
        if cur < old:
            improved.append(format_change(name, old, cur, p_value))
        elif cur > old:
            regressed.append(format_change(name, old, cur, p_value))
        else:
            unchanged.append(format_change(name, old, cur, p_value))

    print(
        f"Compared baseline against medians from {runs_to_execute} runs "
        f"(two-sided sign-test p-values)."
    )

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

    if median_only:
        print()
        print("Only in current medians:")
        for name in median_only:
            print(f"  {name}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
