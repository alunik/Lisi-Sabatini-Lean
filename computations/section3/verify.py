#!/usr/bin/env python3
"""Run the standalone Magma computation and require complete PASS coverage.

Magma can return exit status zero after an error, so this wrapper also checks
the complete output. Python supplies no group-theoretic computations.
"""
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
SOURCES = ("run.m", "profiles.m", "exceptions.m", "witnesses.m", "verify.py")


def source_hashes():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in SOURCES}


def check_output(output):
    if re.search(r"(?im)(runtime error|user error|syntax error|assertion failed|fatal error)", output):
        raise ValueError("Magma reported an error")
    summary = re.findall(
        r"^SECTION3_PASS symmetric=36 alternating=36 nilpotent_pairs=64 "
        r"anchors=5 cpu_seconds=([0-9.]+)$", output, re.M)
    if len(summary) != 1:
        raise ValueError("missing or duplicate final SECTION3_PASS marker")
    results = {}
    for label in ("SYMMETRIC", "ALTERNATING"):
        rows = re.findall(rf"^{label}_PASS n=(\d+) method=(\w+) bad_bound=(\S+)$",
                          output, re.M)
        if [int(n) for n, _, _ in rows] != list(range(5, 41)):
            raise ValueError(f"incomplete {label} degree coverage")
        for n, method, bound in rows:
            if not 0 <= Fraction(bound) < 1:
                raise ValueError(f"non-strict bound for {label} degree {n}")
        results[label.lower()] = [dict(degree=int(n), method=method, bad_bound=bound)
                                  for n, method, bound in rows]
    mixed = re.findall(r"^NILPOTENT_PAIR_PASS n=(\d+) groups=S,A$", output, re.M)
    if list(map(int, mixed)) != list(range(9, 41)):
        raise ValueError("incomplete nilpotent-pair coverage")
    anchors = re.findall(r"^ANCHOR_PASS n=(\d+) p=(\d+) value=(\S+) upper=(\S+)$",
                         output, re.M)
    if [(int(n), int(p)) for n, p, _, _ in anchors] != [(40, 2), (39, 3), (40, 5), (35, 7)]:
        raise ValueError("incomplete numerical anchors")
    even = re.findall(r"^EVEN_ANCHOR_PASS n=40 value=(\S+) upper=(\S+)$", output, re.M)
    if len(even) != 1 or any(not Fraction(v) < Fraction(u)
                             for v, u in [(v, u) for _, _, v, u in anchors] + even):
        raise ValueError("failed numerical anchor")
    budgets = re.findall(r"^TAIL_BUDGETS_PASS symmetric=(\S+) alternating=(\S+)$", output, re.M)
    if len(budgets) != 1 or any(not Fraction(x) < 1 for x in budgets[0]):
        raise ValueError("missing or failed tail budgets")
    if "PROFILE_VALIDATION degrees=5..12 prime_cases=32 status=PASS" not in output:
        raise ValueError("missing comparison with actual Sylow class data")
    versions = re.findall(r"^MAGMA_VERSION (\S+)$", output, re.M)
    if len(versions) != 1:
        raise ValueError("missing Magma version")
    return dict(status="PASS", magma_version=versions[0], cpu_seconds=float(summary[0]),
                symmetric_groups=36, alternating_groups=36, nilpotent_pair_groups=64,
                numerical_anchors=5, actual_profile_prime_cases=32, bounds=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--magma", default="magma", help="Magma executable (default: magma)")
    parser.add_argument("--output", type=Path, help="write magma.log and receipt.json here")
    args = parser.parse_args()
    executable = shutil.which(args.magma)
    if executable is None:
        parser.error(f"Magma executable not found: {args.magma}")
    before = source_hashes()
    started_at = datetime.now(timezone.utc).isoformat()
    started = time.perf_counter()
    result = subprocess.run([executable, "-b", "run.m"], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.perf_counter() - started
    output = result.stdout.decode("utf-8", errors="replace")
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / "magma.log").write_bytes(result.stdout)
        # A failed rerun must not leave a previous successful receipt in place.
        (args.output / "receipt.json").unlink(missing_ok=True)
    try:
        if result.returncode:
            raise ValueError(f"Magma exited with status {result.returncode}")
        report = check_output(output)
        if source_hashes() != before:
            raise ValueError("source files changed during verification")
    except ValueError as error:
        print(output, end="", file=sys.stderr)
        print(f"SECTION3_FAIL: {error}", file=sys.stderr)
        return 1
    report.update(started_at_utc=started_at, wall_seconds=elapsed,
                  platform=dict(system=platform.system(), architecture=platform.machine()),
                  source_sha256=before, log_sha256=hashlib.sha256(result.stdout).hexdigest(),
                  draft_commit="e7896fe09f180baba9298732eb9c92be0464b64c")
    if args.output:
        (args.output / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: S_n and A_n for every 5 <= n <= 40 (72 groups).")
    print("PASS: every pair of nilpotent subgroups for 9 <= n <= 40 (64 groups).")
    print("PASS: five numerical anchors, both tail budgets, and 32 actual Sylow-profile comparisons.")
    print(f"Magma {report['magma_version']}; {report['cpu_seconds']:.3f}s CPU; {elapsed:.3f}s wall.")
    if args.output:
        print(f"Evidence: {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
