#!/usr/bin/env python3
"""Verify every exported OddOrder source byte against the delivered manifest."""

import hashlib
import json
from pathlib import Path


def main() -> None:
    metadata = Path(__file__).resolve().parent
    package = metadata.parent
    record = json.loads((metadata / "export.json").read_text())
    checksums = (metadata / "source-files.sha256").read_bytes()
    if hashlib.sha256(checksums).hexdigest() != record["source_files_sha256"]:
        raise SystemExit("The exported-source checksum manifest has changed.")
    entries = checksums.decode().splitlines()
    if len(entries) != record["exported_file_count"]:
        raise SystemExit("The exported-source file count does not match.")
    expected_paths = set()
    for line in entries:
        expected, name = line.split("  ", 1)
        path = package / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit(f"Exported source missing or changed: {name}")
        expected_paths.add(name)
    # Reject extra mathematical source files, while permitting Lake build products.
    actual_lean = {str(path.relative_to(package)) for path in (package / "OddOrder").rglob("*.lean")}
    actual_lean.add("OddOrder.lean")
    expected_lean = {name for name in expected_paths if name.endswith(".lean")}
    if actual_lean != expected_lean:
        raise SystemExit("Unexpected mathematical source files in the exported package.")
    print(f"SOURCE_EXPORT_PASS: {len(entries)} files from {record['compatibility_commit']}")


if __name__ == "__main__":
    main()
