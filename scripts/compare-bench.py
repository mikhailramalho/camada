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
    r"(?P<ns_per_iter>\d+(?:\.\d+)?)"
    r"(?:\s+rss_after_kb=(?P<rss_after_kb>\d+)\s+"
    r"rss_delta_kb=(?P<rss_delta_kb>-?\d+))?$"
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
            "rss_after_kb": int(data["rss_after_kb"] or 0),
            "rss_delta_kb": int(data["rss_delta_kb"] or 0),
            "source": source,
            "lineno": lineno,
        }
    return results


def parse_file(path: Path) -> dict[str, dict[str, object]]:
    return parse_lines(path.read_text().splitlines(), str(path))


def bench_cmd(binary: Path, iterations: int, cpu: int, case_filter: str) -> list[str]:
    cmd = ["schedtool", "-a", str(cpu), "-n", "20", "-e", str(binary)]
    cmd += ["bitwuzla", str(iterations)]
    return cmd + [case_filter] if case_filter else cmd


def run_benchmark(
    binary: Path, iterations: int, cpu: int, case_filter: str = ""
) -> dict[str, dict[str, object]]:
    cmd = bench_cmd(binary, iterations, cpu, case_filter)
    proc = subprocess.run(cmd, check=True, capture_output=True, text=True)
    return parse_lines(proc.stdout.splitlines(), f"cpu{cpu}")


def run_benchmarks(
    binary: Path, iterations: int, runs: int, case_filter: str = ""
) -> list[dict[str, dict[str, object]]]:
    cpu_count = os.cpu_count() or 1
    results: list[dict[str, dict[str, object]]] = []
    launched = 0

    while launched < runs:
        batch_size = min(cpu_count, runs - launched)
        procs: list[tuple[int, subprocess.Popen[str]]] = []
        for cpu in range(batch_size):
            cmd = bench_cmd(binary, iterations, cpu, case_filter)
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
        rss_after_values = [int(sample["rss_after_kb"]) for sample in samples]
        rss_delta_values = [int(sample["rss_delta_kb"]) for sample in samples]
        iterations = int(samples[0]["iterations"])
        backend = str(samples[0]["backend"])
        medians[name] = {
            "backend": backend,
            "iterations": iterations,
            "total_ns": int(statistics.median(total_values)),
            "ns_per_iter": statistics.median(ns_values),
            "rss_after_kb": int(statistics.median(rss_after_values)),
            "rss_delta_kb": int(statistics.median(rss_delta_values)),
            "runs": len(samples),
        }

    return medians


def format_benchmark_line(name: str, data: dict[str, object]) -> str:
    return (
        f"benchmark={name} "
        f"backend={data['backend']} "
        f"iterations={data['iterations']} "
        f"total_ns={data['total_ns']} "
        f"ns_per_iter={float(data['ns_per_iter']):.2f} "
        f"rss_after_kb={data['rss_after_kb']} "
        f"rss_delta_kb={data['rss_delta_kb']}"
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
    return ((new - old) / old) * 100.0 if old != 0 else 0.0


def verdict(old: float, new: float) -> str:
    return "improved" if new < old else "regressed" if new > old else "unchanged"


def format_change(name: str, baseline: float, new: float, p_value: float) -> str:
    delta = pct_change(baseline, new)
    word = verdict(baseline, new)
    return (
        f"{name}: {word} "
        f"({baseline:.2f} -> {new:.2f} ns/iter, {delta:+.2f}%, p={p_value:.4f})"
    )


def format_overall_change(
    baseline_total: float, current_total: float, p_value: float
) -> str:
    delta = pct_change(baseline_total, current_total)
    word = verdict(baseline_total, current_total)
    return (
        f"Overall: {word} "
        f"({baseline_total:.2f} -> {current_total:.2f} total ns/iter, "
        f"{delta:+.2f}%, p={p_value:.4f})"
    )


def format_memory_change(name: str, baseline: float, new: float) -> str:
    delta = pct_change(baseline, new)
    word = verdict(baseline, new)
    return (
        f"{name}: {word} "
        f"({baseline:.0f} -> {new:.0f} KiB retained RSS, {delta:+.2f}%)"
    )


def format_overall_memory_change(
    baseline_total: float, current_total: float
) -> str:
    delta = pct_change(baseline_total, current_total)
    word = verdict(baseline_total, current_total)
    return (
        f"Overall retained RSS: {word} "
        f"({baseline_total:.0f} -> {current_total:.0f} KiB, {delta:+.2f}%)"
    )


def compare_and_print(
    baseline: dict[str, dict[str, object]],
    current: dict[str, dict[str, object]],
    current_runs: list[dict[str, dict[str, object]]],
    baseline_runs: list[dict[str, dict[str, object]]] | None = None,
) -> None:
    common_names = sorted(set(baseline) & set(current))
    baseline_only = sorted(set(baseline) - set(current))
    current_only = sorted(set(current) - set(baseline))

    improved: list[str] = []
    regressed: list[str] = []
    unchanged: list[str] = []
    memory_improved: list[str] = []
    memory_regressed: list[str] = []
    memory_unchanged: list[str] = []
    baseline_total = 0.0
    current_total = 0.0
    baseline_rss_total = 0.0
    current_rss_total = 0.0
    base_runs = (
        baseline_runs if baseline_runs is not None else [None] * len(current_runs)
    )

    for name in common_names:
        old = float(baseline[name]["ns_per_iter"])
        cur = float(current[name]["ns_per_iter"])
        baseline_total += old
        current_total += cur
        # Unpaired runs compare against the baseline's mean; paired runs
        # against the baseline run made alongside each.
        diffs = [
            float(cur_run[name]["ns_per_iter"])
            - (float(base_run[name]["ns_per_iter"]) if base_run is not None else old)
            for base_run, cur_run in zip(base_runs, current_runs)
            if name in cur_run and (base_run is None or name in base_run)
        ]
        p_value = sign_test_p_value(diffs, 0.0)
        if cur < old:
            improved.append(format_change(name, old, cur, p_value))
        elif cur > old:
            regressed.append(format_change(name, old, cur, p_value))
        else:
            unchanged.append(format_change(name, old, cur, p_value))

        old_rss = float(baseline[name]["rss_delta_kb"])
        cur_rss = float(current[name]["rss_delta_kb"])
        baseline_rss_total += old_rss
        current_rss_total += cur_rss
        if cur_rss < old_rss:
            memory_improved.append(format_memory_change(name, old_rss, cur_rss))
        elif cur_rss > old_rss:
            memory_regressed.append(format_memory_change(name, old_rss, cur_rss))
        else:
            memory_unchanged.append(format_memory_change(name, old_rss, cur_rss))

    def run_total(run: dict[str, dict[str, object]]) -> float:
        return sum(
            float(run[name]["ns_per_iter"]) for name in common_names if name in run
        )

    total_diffs = [
        run_total(cur_run) - (
            run_total(base_run) if base_run is not None else baseline_total
        )
        for base_run, cur_run in zip(base_runs, current_runs)
    ]
    overall_p_value = sign_test_p_value(total_diffs, 0.0)

    print(format_overall_change(baseline_total, current_total, overall_p_value))

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

    if memory_regressed or memory_improved or memory_unchanged:
        print()
        print("Retained RSS delta:")
        print(
            f"  {format_overall_memory_change(baseline_rss_total, current_rss_total)}"
        )
        if memory_regressed:
            print("  Regressed:")
            for line in memory_regressed:
                print(f"    {line}")
        if memory_improved:
            print("  Improved:")
            for line in memory_improved:
                print(f"    {line}")
        if memory_unchanged:
            print("  Unchanged:")
            for line in memory_unchanged:
                print(f"    {line}")

    if baseline_only:
        print()
        print("Only in baseline:")
        for name in baseline_only:
            print(f"  {name}")

    if current_only:
        print()
        print("Only in current medians:")
        for name in current_only:
            print(f"  {name}")


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
        "--baseline",
        type=Path,
        default=Path(__file__).with_name("baseline.txt"),
        help="Path to the baseline benchmark file",
    )
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="Write the 10-run medians to scripts/baseline.txt instead of comparing",
    )
    parser.add_argument(
        "--baseline-binary",
        type=Path,
        help=(
            "Run paired A/B samples against this baseline binary instead of "
            "comparing current samples to a median-only baseline file"
        ),
    )
    parser.add_argument(
        "--runs",
        type=int,
        help="Number of measured runs to execute",
    )
    parser.add_argument(
        "--cpu",
        type=int,
        default=0,
        help="CPU to pin paired A/B runs to when --baseline-binary is used",
    )
    parser.add_argument(
        "--warmups",
        type=int,
        default=1,
        help="Warmup pairs to discard before paired A/B measurement",
    )
    parser.add_argument(
        "--case-filter",
        default="",
        help="Optional benchmark case substring passed to camada-bench",
    )
    args = parser.parse_args()

    baseline_path = args.baseline

    cpu_count = os.cpu_count() or 1
    runs_to_execute = args.runs or max(DEFAULT_MIN_RUNS, cpu_count * RUNS_PER_CPU)

    if args.baseline_binary:
        if args.runs is None:
            runs_to_execute = DEFAULT_MIN_RUNS
        def run(binary: Path) -> dict[str, dict[str, object]]:
            return run_benchmark(
                binary, args.iterations, args.cpu, args.case_filter
            )

        for _ in range(args.warmups):
            run(args.baseline_binary)
            run(args.binary)

        print(
            f"Running {runs_to_execute} paired A/B benchmarks on CPU {args.cpu}...",
            file=sys.stderr,
        )
        baseline_runs: list[dict[str, dict[str, object]]] = []
        current_runs: list[dict[str, dict[str, object]]] = []
        for i in range(runs_to_execute):
            # Alternate which binary runs first, so neither always gets the
            # warmer cache.
            if i % 2 == 0:
                baseline_runs.append(run(args.baseline_binary))
                current_runs.append(run(args.binary))
            else:
                current_runs.append(run(args.binary))
                baseline_runs.append(run(args.baseline_binary))

        baseline_medians = compute_medians(baseline_runs)
        current_medians = compute_medians(current_runs)
        print(
            f"Compared paired medians from {runs_to_execute} baseline/current "
            "run pairs (two-sided paired sign-test p-values)."
        )
        compare_and_print(
            baseline_medians, current_medians, current_runs, baseline_runs
        )
        return 0

    print(
        f"Running {runs_to_execute} benchmarks across up to {cpu_count} CPUs...",
        file=sys.stderr,
    )
    runs = run_benchmarks(
        args.binary, args.iterations, runs_to_execute, args.case_filter
    )

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

    print(
        f"Compared baseline against medians from {runs_to_execute} runs "
        f"(two-sided sign-test p-values)."
    )
    compare_and_print(baseline, medians, runs)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
