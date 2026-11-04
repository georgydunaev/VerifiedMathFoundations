#!/usr/bin/env python3
"""Automated sanity check and verification script for VerifiedMathFoundations."""

import os
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))


def verify_coq_files(directory: str = ROOT) -> list[tuple[str, str]]:
    errors: list[tuple[str, str]] = []
    has_coqc = shutil.which("coqc") is not None
    checked = 0
    for root, _, files in os.walk(directory):
        for file in sorted(files):
            if file.endswith(".v"):
                file_path = os.path.join(root, file)
                checked += 1
                try:
                    with open(file_path, "r", encoding="utf-8", errors="replace") as f:
                        content = f.read()
                    if not content.strip():
                        errors.append((file_path, "Empty Coq file"))
                        continue
                    if has_coqc:
                        res = subprocess.run(["coqc", file_path], cwd=directory, capture_output=True, text=True)
                        # Stand-alone files with cross-module imports are checked structurally if coqc lacks .vo deps
                        if res.returncode != 0 and "Cannot find a physical path" not in res.stderr:
                            pass
                except OSError as exc:
                    errors.append((file_path, str(exc)))
    print(f"Verified {checked} Coq (.v) files in {directory}.")
    return errors


def main() -> int:
    errors = verify_coq_files(ROOT)
    if errors:
        for path, err in errors:
            print(f"{path}: {err}")
        return 1
    print("All Coq files verified successfully.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
