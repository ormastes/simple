#!/usr/bin/env python3
"""Validate release payload contents for basic licensing hygiene."""

from __future__ import annotations

import argparse
import pathlib
import sys
import tarfile


REQUIRED_BASENAMES = {"LICENSE", "THIRD_PARTY_NOTICES.md"}

FORBIDDEN_FRAGMENTS = [
    "/src/app/vscode_extension/node_modules/",
    "/src/app/vscode_extension/.vscode-test/",
    "/src/compiler_rust/target/",
    "/config/t32/libXp.so.6",
    "/config/t32/libjpeg.so.62.0.0",
]


def normalize_members(paths: list[str]) -> list[str]:
    normalized: list[str] = []
    for raw in paths:
        entry = raw.replace("\\", "/").strip("./")
        if entry:
            normalized.append(entry)
    return normalized


def collect_from_directory(root: pathlib.Path) -> list[str]:
    return normalize_members(
        [str(path.relative_to(root)) for path in root.rglob("*") if path.is_file()]
    )


def collect_from_tarball(tar_path: pathlib.Path) -> list[str]:
    with tarfile.open(tar_path, "r:*") as tar:
        return normalize_members([member.name for member in tar.getmembers() if member.isfile()])


def validate(entries: list[str]) -> list[str]:
    errors: list[str] = []
    basenames = {pathlib.PurePosixPath(entry).name for entry in entries}

    for required in sorted(REQUIRED_BASENAMES):
        if required not in basenames:
            errors.append(f"missing required file: {required}")

    padded = [f"/{entry}" for entry in entries]
    for fragment in FORBIDDEN_FRAGMENTS:
        matches = [entry[1:] for entry in padded if fragment in entry]
        for match in matches:
            errors.append(f"forbidden payload entry present: {match}")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--dir", dest="directory", help="Directory tree to validate")
    group.add_argument("--tar", dest="tarball", help="Tar/tgz archive to validate")
    args = parser.parse_args()

    if args.directory:
        target = pathlib.Path(args.directory)
        entries = collect_from_directory(target)
    else:
        target = pathlib.Path(args.tarball)
        entries = collect_from_tarball(target)

    errors = validate(entries)
    if errors:
        print(f"[FAIL] release payload validation failed for {target}", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print(f"[OK] release payload validation passed for {target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
