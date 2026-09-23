#!/usr/bin/env python3
"""Check the paper's deterministic certificate sources without modifying them."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
GENERATORS = [
    "LisiSabatini/FiniteCertificates/generate_a8.py",
    "LisiSabatini/FiniteCertificates/generate_a8_rows.py",
    "LisiSabatini/FiniteCertificates/generate_a8_fingerprints.py",
    "LisiSabatini/SymmetricEightCertificates/generate.py",
    "LisiSabatini/SymmetricEightCertificates/generate_fast.py",
    "LisiSabatini/SymmetricFiniteCertificates/generate.py",
    "scripts/certificates/generate_double_cosets.py",
]


def main():
    if not __debug__:
        raise SystemExit("Run without Python's -O option: generators use assertions.")
    manifest = json.loads((ROOT / "data/certificates/manifest.json").read_text())
    failures = []
    for name, expected in manifest["files"].items():
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            failures.append(name)
    if failures:
        raise SystemExit("Certificate manifest mismatch: " + ", ".join(failures))
    for name in GENERATORS:
        print(f"Checking {name}", flush=True)
        subprocess.run([sys.executable, str(ROOT / name), "--check"], cwd=ROOT, check=True)
    print("PASS: 201 generated Lean modules and all certificate inputs reproduced.")
    print("Run the Lean build separately to check the proofs.")


if __name__ == "__main__":
    main()
