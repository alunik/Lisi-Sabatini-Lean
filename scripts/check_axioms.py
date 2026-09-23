#!/usr/bin/env python3
"""Re-run named audit leaves and enforce exact declarations and standard axioms.

The default profile covers the paper endpoints and deliberately excludes the
separate, expensive Feit--Thompson applications. Build the requested audit
modules before running this script; --include-feit-thompson adds their six
reports to the default profile (or to explicitly selected modules).
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DEFAULT_AUDITS = ["PaperAlignmentAxiomAudit"]
FEIT_THOMPSON_AUDIT = "FeitThompsonApplicationsAxiomAudit"
IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
REPORT = re.compile(
    r"^'([^'\r\n]+)' (?:depends on axioms:\s*\[([^]]*)\]"
    r"|(does not depend on any axioms))[ \t]*\r?$",
    re.DOTALL | re.MULTILINE,
)


def strip_comments(source: str) -> str:
    """Remove nested Lean block and line comments, preserving line numbers.

    Audit leaves contain only imports, scope commands, and #print axioms;
    string literals and other executable commands are intentionally unsupported.
    """
    result: list[str] = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result.append("  ")
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0:
                break
            result.append(" " * (end - i))
            i = end
        else:
            result.append(source[i] if not depth or source[i] == "\n" else " ")
            i += 1
    if depth:
        raise ValueError("unterminated Lean block comment")
    return "".join(result)


def expected_declarations(source: str) -> list[str]:
    """Read exact names from the deliberately narrow syntax of audit leaves.

    Namespace-relative names are qualified using their lexical namespace.
    Use `_root_.Name` for an absolute reference from a different namespace;
    `open`-based name resolution is deliberately rejected instead of guessed.
    """
    scopes: list[tuple[str, str]] = []
    expected: list[str] = []
    pending_print = False

    def add_name(name: str) -> None:
        namespace = ".".join(value for kind, value in scopes if kind == "namespace")
        if name.startswith("_root_."):
            qualified = name.removeprefix("_root_.")
        elif namespace and not name.startswith(namespace.split(".")[0] + "."):
            qualified = namespace + "." + name
        else:
            qualified = name
        if qualified in expected:
            raise ValueError(f"duplicate requested declaration: {qualified}")
        expected.append(qualified)

    for lineno, raw in enumerate(strip_comments(source).splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        if pending_print:
            if not re.fullmatch(IDENTIFIER, line):
                raise ValueError(f"line {lineno}: expected a declaration after #print axioms")
            add_name(line)
            pending_print = False
            continue
        match = re.fullmatch(r"#print\s+axioms(?:\s+(" + IDENTIFIER + r"))?", line)
        if match:
            if match[1]:
                add_name(match[1])
            else:
                pending_print = True
            continue
        match = re.fullmatch(r"namespace\s+(" + IDENTIFIER + r")", line)
        if match:
            if match[1] == "_root_" or match[1].startswith("_root_."):
                raise ValueError(f"line {lineno}: absolute namespace commands are unsupported")
            scopes.append(("namespace", match[1]))
            continue
        match = re.fullmatch(r"section(?:\s+(" + IDENTIFIER + r"))?", line)
        if match:
            scopes.append(("section", match[1] or ""))
            continue
        match = re.fullmatch(r"end(?:\s+(" + IDENTIFIER + r"))?", line)
        if match:
            if not scopes or (match[1] is not None and match[1] != scopes[-1][1]):
                raise ValueError(f"line {lineno}: unmatched end command")
            scopes.pop()
            continue
        if line in {"module", "set_option linter.hashCommand false"} or re.fullmatch(
            r"(?:public\s+)?import\s+" + IDENTIFIER, line
        ):
            continue
        raise ValueError(f"line {lineno}: unsupported audit command: {line}")
    if pending_print:
        raise ValueError("missing declaration after #print axioms")
    if scopes:
        raise ValueError("unclosed namespace or section in audit leaf")
    if not expected:
        raise ValueError("audit leaf requests no declarations")
    return expected


def validate_output(output: str, expected: list[str]) -> int:
    """Fail closed on missing, substituted, duplicate or nonstandard reports."""
    if not expected or len(set(expected)) != len(expected):
        raise ValueError("expected declarations must be nonempty and distinct")
    reports = REPORT.findall(output)
    names = [name for name, _, _ in reports]
    if len(set(names)) != len(names):
        raise ValueError("duplicate declaration reports")
    missing = set(expected) - set(names)
    unexpected = set(names) - set(expected)
    if missing or unexpected:
        raise ValueError(
            f"declaration reports differ: missing {sorted(missing)}, "
            f"unexpected {sorted(unexpected)}"
        )
    for name, raw_axioms, _ in reports:
        axioms = {axiom.strip() for axiom in raw_axioms.split(",") if axiom.strip()}
        if axioms - ALLOWED:
            raise ValueError(f"{name}: disallowed axioms {sorted(axioms - ALLOWED)}")
    return len(reports)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("audits", nargs="*", help="audit module basenames (default: paper only)")
    parser.add_argument(
        "--include-feit-thompson", action="store_true",
        help="also check the separate six-endpoint Feit--Thompson audit (must be built first)",
    )
    args = parser.parse_args()
    audits = list(args.audits or DEFAULT_AUDITS)
    if args.include_feit_thompson and FEIT_THOMPSON_AUDIT not in audits:
        audits.append(FEIT_THOMPSON_AUDIT)
    if len(set(audits)) != len(audits):
        parser.error("duplicate audit modules")
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", audit) for audit in audits):
        parser.error("audits must be module basenames, without paths or extensions")
    ft_scope = "included" if FEIT_THOMPSON_AUDIT in audits else "excluded"
    print(f"Audit modules: {', '.join(audits)}; Feit--Thompson {ft_scope}", flush=True)
    root = Path(__file__).resolve().parents[1]
    env = {**os.environ, "LEAN_NUM_THREADS": "1"}
    total = 0
    for audit in audits:
        source = root / "LisiSabatini" / f"{audit}.lean"
        expected = expected_declarations(source.read_text())
        run = subprocess.run(
            ["lake", "env", "lean", "-j1", "-DwarningAsError=true", str(source)],
            cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        if run.returncode:
            print(run.stdout, file=sys.stderr)
            raise RuntimeError(f"{audit}: Lean exited {run.returncode}")
        try:
            count = validate_output(run.stdout, expected)
        except ValueError:
            print(run.stdout, file=sys.stderr)
            raise
        print(f"PASS {audit}: {count} exact declarations, standard axioms only", flush=True)
        total += count
    print(f"PASS: {total} audited declaration reports (Feit--Thompson {ft_scope})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
