#!/usr/bin/env python3
"""Fast exact line-window duplicate gate for large Simple source trees."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def iter_spl_files(root: Path, excludes: list[str]) -> list[Path]:
    if root.is_file():
        return [root] if root.suffix == ".spl" and not excluded(root, excludes) else []
    files: list[Path] = []
    for path in root.rglob("*.spl"):
        if not excluded(path, excludes):
            files.append(path)
    return sorted(files)


def excluded(path: Path, excludes: list[str]) -> bool:
    text = path.as_posix()
    name = path.name
    for pattern in excludes:
        if not pattern:
            continue
        if pattern.endswith("/") and f"/{pattern}" in text:
            return True
        if pattern.startswith("**/*") and name.endswith(pattern[4:]):
            return True
        if pattern in text:
            return True
    return False


def has_signal(window: str) -> bool:
    stripped = window.strip()
    if not stripped:
        return False
    markers = ("fn ", "if ", "while ", "for ", "match", "return", "val ", "var ")
    return any(marker in stripped for marker in markers)


def find_duplicates(files: list[Path], min_lines: int) -> list[dict[str, object]]:
    buckets: dict[str, list[dict[str, object]]] = {}
    for path in files:
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            lines = path.read_text(errors="ignore").splitlines()
        if len(lines) < min_lines:
            continue
        for start in range(0, len(lines) - min_lines + 1):
            window_lines = [line.strip() for line in lines[start : start + min_lines]]
            key = "\n".join(window_lines)
            if not has_signal(key):
                continue
            buckets.setdefault(key, []).append(
                {
                    "file": path.as_posix(),
                    "line_start": start + 1,
                    "line_end": start + min_lines,
                }
            )

    groups: list[dict[str, object]] = []
    for key, blocks in buckets.items():
        if len(blocks) < 2:
            continue
        groups.append(
            {
                "occurrences": len(blocks),
                "lines_each": min_lines,
                "total_lines": len(blocks) * min_lines,
                "impact_score": len(blocks) * len(blocks) * min_lines,
                "blocks": blocks,
                "code": key,
            }
        )
    groups.sort(key=lambda group: int(group["impact_score"]), reverse=True)
    return groups


def print_text(groups: list[dict[str, object]], file_count: int) -> None:
    total_lines = sum(int(group["total_lines"]) for group in groups)
    print("Token Duplicate Report")
    print("======================")
    print("")
    print(f"Scanned {file_count} files")
    print(f"Found {len(groups)} duplicate groups ({total_lines} total lines duplicated)")
    print("")
    for idx, group in enumerate(groups[:20], 1):
        print(
            f"{idx}. Impact Score: {group['impact_score']} "
            f"({group['occurrences']} occurrences, {group['lines_each']} lines each)"
        )
        print("   Files:")
        for block in group["blocks"]:
            print(f"   - {block['file']}:{block['line_start']}-{block['line_end']}")
        print("")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("path")
    parser.add_argument("--min-lines", type=int, default=5)
    parser.add_argument("--format", choices=("text", "json"), default="text")
    parser.add_argument("--max-allowed", type=int, default=0)
    parser.add_argument("--exclude", action="append", default=[])
    args = parser.parse_args()

    excludes = args.exclude or ["test/", "doc/", "_spec.spl", "_test.spl"]
    files = iter_spl_files(Path(args.path), excludes)
    groups = find_duplicates(files, max(args.min_lines, 1))
    if args.format == "json":
        print(json.dumps({"files": len(files), "duplicates": groups}, indent=2))
    else:
        print_text(groups, len(files))
    return 1 if len(groups) > args.max_allowed else 0


if __name__ == "__main__":
    raise SystemExit(main())
