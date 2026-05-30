#!/usr/bin/env python3
"""Repository hygiene gate for generated clutter and stale structure.

The script is intentionally conservative: it reports problems and exits nonzero
when unignored generated files or known dirty-structure markers are present. It
does not delete files.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
POLICY_PATH = ROOT / "scripts/audit/repo_hygiene_policy.json"


def load_policy() -> dict[str, object]:
    with POLICY_PATH.open(encoding="utf-8") as fh:
        return json.load(fh)


POLICY = load_policy()
DIRTY_DIR_NAMES = set(POLICY.get("dirty_dir_names", []))
DIRTY_SUFFIXES = set(POLICY.get("dirty_suffixes", []))
SKIP_DIR_NAMES = set(POLICY.get("skip_dir_names", []))
SKIP_PREFIXES = tuple(POLICY.get("skip_prefixes", []))
SOURCE_ROOTS = tuple(POLICY.get("source_roots", []))


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def git_ignored(path: Path) -> bool:
    result = subprocess.run(
        ["git", "check-ignore", "-q", path.as_posix()],
        cwd=ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def is_external(path: Path) -> bool:
    text = rel(path)
    return any(text.startswith(prefix) for prefix in SKIP_PREFIXES)


def walk_repo() -> list[Path]:
    paths: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        current = Path(dirpath)
        if current != ROOT and is_external(current):
            dirnames[:] = []
            continue
        dirnames[:] = [
            name
            for name in dirnames
            if name not in SKIP_DIR_NAMES and not is_external(current / name)
        ]
        for name in dirnames:
            paths.append(current / name)
        for name in filenames:
            paths.append(current / name)
    return paths


def find_dirty_dirs(paths: list[Path]) -> list[str]:
    hits: list[str] = []
    for path in paths:
        if not path.is_dir():
            continue
        if path.name not in DIRTY_DIR_NAMES:
            continue
        if is_external(path):
            continue
        if not git_ignored(path):
            hits.append(rel(path))
    return sorted(hits)


def find_dirty_files(paths: list[Path]) -> list[str]:
    hits: list[str] = []
    for path in paths:
        if not path.is_file():
            continue
        if is_external(path):
            continue
        if path.name == ".DS_Store" or path.suffix in DIRTY_SUFFIXES:
            if not git_ignored(path):
                hits.append(rel(path))
    return sorted(hits)


def find_empty_source_dirs() -> list[str]:
    hits: list[str] = []
    for source_root in SOURCE_ROOTS:
        base = ROOT / source_root
        if not base.exists():
            continue
        for dirpath, dirnames, _filenames in os.walk(base):
            current = Path(dirpath)
            if current != base and is_external(current):
                dirnames[:] = []
                continue
            dirnames[:] = [
                name
                for name in dirnames
                if name not in SKIP_DIR_NAMES
                and not is_external(current / name)
            ]
            for name in dirnames:
                path = current / name
                try:
                    children = [child for child in path.iterdir() if not is_external(child)]
                except OSError:
                    continue
                if not children:
                    hits.append(rel(path))
    return sorted(hits)


def print_group(title: str, items: list[str]) -> None:
    print(title)
    if not items:
        print("  OK")
        return
    for item in items:
        print(f"  - {item}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--allow-empty-source-dirs",
        action="store_true",
        help="Report empty source dirs without failing.",
    )
    args = parser.parse_args()

    paths = walk_repo()
    dirty_dirs = find_dirty_dirs(paths)
    dirty_files = find_dirty_files(paths)
    empty_source_dirs = find_empty_source_dirs()

    print("Repository Hygiene Audit")
    print("========================")
    print_group("Unignored generated/cache directories", dirty_dirs)
    print_group("Unignored temporary files", dirty_files)
    print_group("Empty source directories", empty_source_dirs)

    failed = bool(dirty_dirs or dirty_files)
    if empty_source_dirs and not args.allow_empty_source_dirs:
        failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
