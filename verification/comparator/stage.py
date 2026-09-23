#!/usr/bin/env python3
"""Stage the paper sources under Comparator's writable .lake boundary.

No package resolution or download is performed. Existing dependency/build
caches can be copied into .lake after this command; see README.md.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    source = args.source.resolve()
    project = Path(__file__).resolve().parent
    target = project / ".lake/packages/LisiSabatini"
    if target.is_symlink():
        parser.error("the staged paper package must not be a symlink")

    source_toolchain = (source / "lean-toolchain").read_text().strip()
    if source_toolchain != (project / "lean-toolchain").read_text().strip():
        parser.error("paper and Comparator-project toolchains differ")

    root_files = ["LisiSabatini.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]
    files = [source / name for name in root_files]
    files += sorted((source / "LisiSabatini").rglob("*.lean"))
    files += sorted(path for path in (source / "vendor/odd-order").rglob("*")
                    if path.is_file() and not any(part in {".lake", ".git", "__pycache__"}
                                                  for part in path.relative_to(source).parts))
    hashes = []
    for path in files:
        relative = path.relative_to(source)
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, destination)
        hashes.append(f"{hashlib.sha256(destination.read_bytes()).hexdigest()}  {relative.as_posix()}")

    manifest = json.loads((source / "lake-manifest.json").read_text())
    manifest["name"] = "PaperComparator"
    for package in manifest["packages"]:
        package["inherited"] = True
        if package["type"] == "path":
            package["dir"] = ".lake/packages/LisiSabatini/" + package["dir"]
    manifest["packages"].insert(0, {
        "type": "path", "scope": "", "name": "LisiSabatini",
        "manifestFile": "lake-manifest.json", "inherited": False,
        "dir": ".lake/packages/LisiSabatini", "configFile": "lakefile.toml"
    })
    (project / "lake-manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
    (project / ".lake/staged-source-files.sha256").write_text("\n".join(hashes) + "\n")
    print(f"Staged {len(files)} paper source/configuration/vendor files.")
    print("Dependency pins were copied without resolution; no build was run.")


if __name__ == "__main__":
    main()
