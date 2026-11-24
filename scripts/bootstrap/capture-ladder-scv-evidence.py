#!/usr/bin/env python3
"""Bounded, diagnostic-only SCV metadata capture after a failed ladder step."""
import hashlib
import json
import os
from pathlib import Path
import sys

NAMES = ("SCV_COMPILE_SNAPSHOT", "SCV_COMPILE_INVENTORY", "SCV_COMPILE_RECEIPT")
MAX_SNAPSHOTS = 32
MAX_BYTES = 16 * 1024 * 1024


def capture(root, output):
    root = Path(root).resolve()
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "ladder-scv-evidence-v1", "admission": "none",
              "checkout": str(root), "files": [], "errors": [], "truncated": False}
    used = count = 0
    for relative in ("build/scv/snapshots", ".simple/scv/snapshots"):
        family = root / relative
        if not family.exists():
            continue
        try:
            family.resolve().relative_to(root)
            if family.is_symlink():
                raise ValueError("symlink family")
        except ValueError:
            report["errors"].append(relative + ": outside checkout or symlink")
            continue
        # Visit only immediate snapshot directories, never source subtrees.
        with os.scandir(family) as entries:
            for entry in entries:
                if not entry.is_dir(follow_symlinks=False):
                    continue
                if count >= MAX_SNAPSHOTS:
                    report["truncated"] = True
                    break
                count += 1
                for name in NAMES:
                    source = Path(entry.path) / name
                    key = source.relative_to(root).as_posix()
                    try:
                        if source.is_symlink() or not source.is_file():
                            raise ValueError("missing or nonregular metadata")
                        with source.open("rb") as stream:
                            data = stream.read(MAX_BYTES - used + 1)
                        if len(data) > MAX_BYTES - used:
                            report["truncated"] = True
                            report["errors"].append(key + ": byte budget exceeded")
                            continue
                        target = output / key
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.write_bytes(data)
                        used += len(data)
                        report["files"].append({"path": key, "bytes": len(data),
                                                "sha256": hashlib.sha256(data).hexdigest()})
                    except (OSError, ValueError) as error:
                        report["errors"].append(key + ": " + str(error))
    report["bytes"] = used
    report["snapshots"] = count
    (output / "index.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


if __name__ == "__main__":
    capture(sys.argv[1], sys.argv[2])
