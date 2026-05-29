#!/usr/bin/env python3
"""Audit reachable imports from the noalloc runtime family.

The baremetal/noalloc preset may use only `nogc_async_mut_noalloc` plus safe
`common` helpers. This script follows imports starting from every noalloc
source file and reports any reachable import that crosses into allocating,
OS/app/example, POSIX, or Linux surfaces.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path("src/lib/nogc_async_mut_noalloc")
COMMON = Path("src/lib/common")

FORBIDDEN_PREFIXES = (
    "std.nogc_sync_mut.",
    "std.nogc_async_mut.",
    "std.nogc_async_immut.",
    "std.gc_async_mut.",
    "std.posix.",
    "std.linux.",
    "posix.",
    "linux.",
    "os.",
    "app.",
    "examples.",
)

IMPORT_RE = re.compile(
    r"^\s*(?:use|from|import)(?:\s+lazy)?\s+([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)"
)

HOST_ALLOC_RE = re.compile(r"\b(malloc|calloc|free)\s*\(|\brt_alloc\b|extern\s+fn\s+\w*realloc\b")
ALLOC_ATTR_RE = re.compile(r"^\s*(?:#\s*)?@alloc\b", re.MULTILINE)


def module_candidates(path: Path) -> list[Path]:
    if path.suffix == ".spl":
        return [path]
    return [path.with_suffix(".spl"), path / "__init__.spl"]


def existing_candidate(path: Path) -> Path | None:
    for candidate in module_candidates(path):
        if candidate.exists():
            return candidate
    return None


def resolve_import(module: str, current: Path) -> Path | None:
    parts = module.split(".")
    if not parts:
        return None

    if module.startswith("lib.nogc_async_mut_noalloc."):
        return existing_candidate(ROOT.joinpath(*parts[2:]))

    if module.startswith("std.nogc_async_mut_noalloc."):
        return existing_candidate(ROOT.joinpath(*parts[2:]))

    if module.startswith("std.common."):
        return existing_candidate(COMMON.joinpath(*parts[2:]))

    if module.startswith("common."):
        return existing_candidate(COMMON.joinpath(*parts[1:]))

    if module.startswith("std."):
        short_parts = parts[1:]
        return existing_candidate(ROOT.joinpath(*short_parts)) or existing_candidate(COMMON.joinpath(*short_parts))

    relative = existing_candidate(current.parent.joinpath(*parts))
    if relative is not None:
        return relative

    return None


def import_modules(path: Path) -> list[tuple[int, str]]:
    modules: list[tuple[int, str]] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        match = IMPORT_RE.match(line)
        if match:
            modules.append((line_no, match.group(1)))
    return modules


def is_within(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except ValueError:
        return False


def audit() -> list[str]:
    errors: list[str] = []
    queue = sorted(ROOT.rglob("*.spl"))
    seen: set[Path] = set()

    while queue:
        path = queue.pop(0)
        if path in seen:
            continue
        seen.add(path)

        text = path.read_text(encoding="utf-8")
        if ALLOC_ATTR_RE.search(text):
            errors.append(f"{path}: allocation annotation reachable from noalloc closure")
        if HOST_ALLOC_RE.search(text):
            errors.append(f"{path}: host allocation API reachable from noalloc closure")

        for line_no, module in import_modules(path):
            if module.startswith(FORBIDDEN_PREFIXES):
                errors.append(f"{path}:{line_no}: forbidden reachable import {module}")
                continue

            resolved = resolve_import(module, path)
            if resolved is None:
                continue

            if not is_within(resolved, ROOT) and not is_within(resolved, COMMON):
                errors.append(f"{path}:{line_no}: import {module} resolves outside allowed noalloc/common roots: {resolved}")
                continue

            if resolved not in seen:
                queue.append(resolved)

    return sorted(errors)


def main() -> int:
    errors = audit()
    if errors:
        print("\n".join(errors))
        return 1
    print("noalloc reachable import closure is restricted to nogc_async_mut_noalloc/common")
    return 0


if __name__ == "__main__":
    sys.exit(main())
