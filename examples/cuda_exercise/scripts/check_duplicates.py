#!/usr/bin/env python3
"""
Simple duplicate-code detector for the CUDA NVMe exercises.

Scans the provided directories, tokenizes C/C++/CUDA sources, and reports
ranges of identical line windows that appear in more than one location.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


DEFAULT_EXTENSIONS = {
    ".c",
    ".cc",
    ".cpp",
    ".cxx",
    ".cu",
    ".cuh",
    ".h",
    ".hh",
    ".hpp",
    ".hxx",
    ".inl",
    ".ipp",
}


def normalize_line(line: str) -> str:
    """Strip whitespace and inline comments to make comparisons stable."""
    stripped = line.strip()
    if not stripped:
        return ""
    if stripped.startswith("//"):
        return ""
    if stripped.startswith("/*") or stripped.startswith("*") or stripped.startswith("*/"):
        return ""
    # Remove trailing // comments
    if "//" in stripped:
        parts = stripped.split("//", 1)
        stripped = parts[0].rstrip()
    return " ".join(stripped.split())


def gather_files(paths: Sequence[str], extensions: Sequence[str]) -> List[Path]:
    exts = {ext if ext.startswith(".") else f".{ext}" for ext in extensions}
    all_files: List[Path] = []
    for base in paths:
        root = Path(base)
        if not root.exists():
            continue
        if root.is_file():
            if root.suffix in exts:
                all_files.append(root)
            continue
        for file in root.rglob("*"):
            if file.is_file() and file.suffix in exts:
                all_files.append(file)
    return all_files


def sliding_windows(lines: List[str], min_lines: int) -> Iterable[Tuple[int, str]]:
    if len(lines) < min_lines:
        return []
    windows: List[Tuple[int, str]] = []
    for idx in range(len(lines) - min_lines + 1):
        window = lines[idx : idx + min_lines]
        if all(not w for w in window):
            continue
        digest = hashlib.sha1("\n".join(window).encode("utf-8"), usedforsecurity=False).hexdigest()
        windows.append((idx + 1, digest))
    return windows


def find_duplicates(files: Sequence[Path], min_lines: int) -> Dict[str, List[Tuple[Path, int]]]:
    matches: Dict[str, List[Tuple[Path, int]]] = {}
    for path in files:
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        norm_lines = [normalize_line(line) for line in text.splitlines()]
        for start_line, digest in sliding_windows(norm_lines, min_lines):
            matches.setdefault(digest, []).append((path, start_line))
    filtered: Dict[str, List[Tuple[Path, int]]] = {}
    for digest, occ in matches.items():
        unique_files = {occurrence[0] for occurrence in occ}
        if len(unique_files) > 1:
            filtered[digest] = occ
    return filtered


def format_report(matches: Dict[str, List[Tuple[Path, int]]], limit: int | None = None) -> str:
    lines: List[str] = []
    count = 0
    for digest, occurrences in sorted(matches.items(), key=lambda item: len(item[1]), reverse=True):
        count += 1
        if limit is not None and count > limit:
            break
        lines.append(f"Duplicate block hash {digest}:")
        for path, line_no in occurrences:
            lines.append(f"  - {path}#L{line_no}")
    if not lines:
        return "No duplicate blocks found."
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Detect duplicated code blocks.")
    parser.add_argument(
        "--paths",
        nargs="+",
        required=True,
        help="Directories or files to scan for duplicate code.",
    )
    parser.add_argument(
        "--extensions",
        nargs="+",
        default=sorted(DEFAULT_EXTENSIONS),
        help="File extensions to include (default: common C/C++/CUDA).",
    )
    parser.add_argument(
        "--min-lines",
        type=int,
        default=25,
        help="Minimum number of consecutive lines to consider a duplicate block.",
    )
    parser.add_argument(
        "--max-results",
        type=int,
        default=None,
        help="Limit duplicate entries in the report.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output the report as JSON.",
    )
    parser.add_argument(
        "--fail-on-duplicates",
        action="store_true",
        help="Exit with code 1 if duplicates are found.",
    )
    args = parser.parse_args()

    files = gather_files(args.paths, args.extensions)
    if not files:
        print("No source files matched the provided paths/extensions.")
        return 0

    duplicates = find_duplicates(files, args.min_lines)
    if args.json:
        json_output = {
            "min_lines": args.min_lines,
            "duplicates": [
                {
                    "hash": digest,
                    "occurrences": [{"path": str(path), "line": line} for path, line in occurrences],
                }
                for digest, occurrences in duplicates.items()
            ],
        }
        print(json.dumps(json_output, indent=2))
    else:
        print(format_report(duplicates, limit=args.max_results))

    if duplicates and args.fail_on_duplicates:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
