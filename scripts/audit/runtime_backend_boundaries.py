#!/usr/bin/env python3
"""Audit runtime-family backend ownership and SimpleOS POSIX boundaries.

The checks are intentionally narrow and evidence-oriented:

* GC/no-GC async compatibility families must not own direct `rt_*` hooks.
* Async compatibility families must not contain byte-identical copies of
  no-GC sync backend files that declare direct `rt_*` hooks.
* Sync/immutable compatibility families must not own direct `rt_*` hooks.
* Sync/GC and immutable compatibility families must have matching backing
  modules and facade exports into their documented backend family.
* GC async compatibility modules must not be one-line self-facades back into
  `gc_async_mut`; route to a no-GC backend or own real implementation instead.
* GC async compatibility facades must not wildcard-export no-GC sync backend
  owners that declare runtime hooks; route them through no-GC async facades
  first when an API-preserving async/no-GC facade exists.
* No-GC async compatibility facades must not wildcard-export no-GC sync
  backend owners that declare runtime hooks.
* No-GC runtime families must not import GC compatibility families.
* SimpleOS native lower layers must not import POSIX/libc compatibility layers.
* Portable stdlib/library files must not import POSIX/Linux modules; platform
  and compatibility directories are allowed to do so explicitly.
* The architecture support matrix must not claim runtime-family root
  `__init__.spl` coverage that does not match the tracked stdlib tree.

This script is a guardrail, not a full behavioral test suite.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

ASYNC_COMPAT_ROOTS = (
    "src/lib/gc_async_mut",
    "src/lib/nogc_async_mut",
)

SYNC_COMPAT_ROOTS = (
    "src/lib/gc_sync_mut",
    "src/lib/gc_async_immut",
    "src/lib/gc_sync_immut",
    "src/lib/nogc_sync_immut",
)

FACADE_MIRRORS = (
    ("src/lib/gc_sync_mut", "src/lib/gc_async_mut", "std.gc_async_mut"),
    ("src/lib/gc_async_immut", "src/lib/nogc_async_immut", "std.nogc_async_immut"),
    ("src/lib/gc_sync_immut", "src/lib/gc_async_immut", "std.gc_async_immut"),
    ("src/lib/nogc_sync_immut", "src/lib/nogc_async_immut", "std.nogc_async_immut"),
)

SIMPLEOS_NATIVE_ROOTS = (
    "src/os/kernel",
    "src/os/drivers",
    "src/os/services",
    "src/os/sosix",
    "src/os/userlib",
    "src/os/async",
)

PORTABLE_LIB_ROOTS = (
    "src/lib/common",
    "src/lib/gc_async_mut",
    "src/lib/gc_sync_mut",
    "src/lib/gc_async_immut",
    "src/lib/gc_sync_immut",
    "src/lib/nogc_async_mut",
    "src/lib/nogc_sync_mut",
    "src/lib/nogc_async_immut",
    "src/lib/nogc_sync_immut",
)

NOGC_RUNTIME_ROOTS = (
    "src/lib/common",
    "src/lib/nogc_async_mut",
    "src/lib/nogc_sync_mut",
    "src/lib/nogc_async_immut",
    "src/lib/nogc_sync_immut",
    "src/lib/nogc_async_mut_noalloc",
)

RUNTIME_FAMILIES = (
    "common",
    "nogc_sync_mut",
    "nogc_async_mut",
    "gc_async_mut",
    "nogc_async_immut",
    "nogc_async_mut_noalloc",
    "gc_sync_mut",
    "gc_async_immut",
    "gc_sync_immut",
    "nogc_sync_immut",
)

SUPPORT_MATRIX = ROOT / "doc/04_architecture/runtime_family_support_matrix.md"

PORTABLE_PLATFORM_ALLOW_PARTS = (
    "/posix/",
    "/nvfs_posix/",
    "/platform/",
    "/linux/",
    "posix_",
    "_posix",
    "linux_",
    "_linux",
)

IMPORT_RE = re.compile(r"^\s*(?:use|import|export\s+use)\s+([^.{\s]+(?:\.[^.{\s]+)*)")
RUNTIME_HOOK_RE = re.compile(r"\bextern\s+fn\s+rt_[A-Za-z0-9_]*")
BACKEND_HOOK_RE = re.compile(
    r"\bextern\s+fn\s+(?:rt_[A-Za-z0-9_]*|spl_memtrack_[A-Za-z0-9_]*|stdin_read_char)\b"
)
NOGC_SYNC_WILDCARD_RE = re.compile(
    r"\bexport\s+use\s+(?:std\.)?nogc_sync_mut\.([A-Za-z0-9_./]+)\.\*"
)
GC_ASYNC_SELF_FACADE_RE = re.compile(
    r"^\s*export\s+use\s+(?:std\.)?gc_async_mut\.[A-Za-z0-9_./]+(?:\.\*|\.[A-Za-z0-9_]+|\s*\{)"
)
FORBIDDEN_SIMPLEOS_IMPORT_RE = re.compile(r"\b(?:os\.posix|os\.libc|posix\.|libc\.)\b")
FORBIDDEN_PORTABLE_IMPORT_RE = re.compile(r"\b(?:std\.posix|std\.linux|os\.posix|os\.libc|posix\.|linux\.)\b")
FORBIDDEN_NOGC_IMPORT_RE = re.compile(r"\b(?:std\.)?gc_(?:async|sync)_(?:mut|immut)\b")


def git_files(patterns: tuple[str, ...]) -> list[Path]:
    cmd = ["git", "ls-files", *patterns]
    result = subprocess.run(cmd, cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE)
    return [ROOT / line for line in result.stdout.splitlines() if line.endswith(".spl")]


def tracked_spl_under(roots: tuple[str, ...]) -> list[Path]:
    patterns = tuple(f"{root}/**/*.spl" for root in roots) + tuple(f"{root}/*.spl" for root in roots)
    seen: dict[str, Path] = {}
    for path in git_files(patterns):
        seen[path.as_posix()] = path
    return [seen[key] for key in sorted(seen)]


def code_lines(path: Path) -> list[tuple[int, str]]:
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return []
    lines: list[tuple[int, str]] = []
    for line_no, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        lines.append((line_no, stripped))
    return lines


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def direct_runtime_hooks() -> list[str]:
    hits: list[str] = []
    for path in tracked_spl_under(ASYNC_COMPAT_ROOTS):
        for line_no, stripped in code_lines(path):
            if RUNTIME_HOOK_RE.search(stripped):
                hits.append(f"{rel(path)}:{line_no}: {stripped}")
    return hits


def exact_duplicate_runtime_hooks() -> list[str]:
    hits: list[str] = []
    for source_root in ASYNC_COMPAT_ROOTS:
        for source_path in tracked_spl_under((source_root,)):
            rel_path = source_path.relative_to(ROOT / source_root)
            sync_path = ROOT / "src/lib/nogc_sync_mut" / rel_path
            if not sync_path.exists():
                continue

            source_text = source_path.read_text(encoding="utf-8", errors="ignore")
            if not RUNTIME_HOOK_RE.search(source_text):
                continue

            sync_text = sync_path.read_text(encoding="utf-8", errors="ignore")
            if source_text == sync_text:
                hits.append(f"{rel(source_path)} duplicates backend hook owner {rel(sync_path)}")
    return hits


def sync_compat_direct_runtime_hooks() -> list[str]:
    hits: list[str] = []
    for path in tracked_spl_under(SYNC_COMPAT_ROOTS):
        for line_no, stripped in code_lines(path):
            if RUNTIME_HOOK_RE.search(stripped):
                hits.append(f"{rel(path)}:{line_no}: {stripped}")
    return hits


def facade_target_module(target_prefix: str, rel_path: str) -> str:
    if rel_path == "__init__.spl":
        return target_prefix
    if rel_path.endswith("/__init__.spl"):
        module_path = rel_path[: -len("/__init__.spl")].replace("/", ".")
    else:
        module_path = rel_path[:-len(".spl")].replace("/", ".")
    return f"{target_prefix}.{module_path}"


def facade_mirror_violations() -> list[str]:
    hits: list[str] = []
    for source_root, target_root, target_prefix in FACADE_MIRRORS:
        for source_path in tracked_spl_under((source_root,)):
            rel_path = source_path.relative_to(ROOT / source_root).as_posix()
            target_path = ROOT / target_root / rel_path
            if not target_path.exists():
                hits.append(f"{rel(source_path)}: missing backing module {target_path.relative_to(ROOT).as_posix()}")
                continue

            expected = facade_target_module(target_prefix, rel_path)
            text = source_path.read_text(encoding="utf-8", errors="ignore")
            if f"export use {expected}" not in text:
                hits.append(f"{rel(source_path)}: missing facade export to {expected}")
    return hits


def semantic_lines(path: Path) -> list[tuple[int, str]]:
    ignored_prefixes = ("#", "@allow", "@gc", "@no_gc")
    return [
        (line_no, stripped)
        for line_no, stripped in code_lines(path)
        if not stripped.startswith(ignored_prefixes)
    ]


def gc_async_one_line_self_facades() -> list[str]:
    hits: list[str] = []
    for path in tracked_spl_under(("src/lib/gc_async_mut",)):
        lines = semantic_lines(path)
        if len(lines) != 1:
            continue
        line_no, stripped = lines[0]
        if GC_ASYNC_SELF_FACADE_RE.search(stripped):
            hits.append(f"{rel(path)}:{line_no}: {stripped}")
    return hits


def no_gc_async_runtime_owner_wildcards() -> list[str]:
    hits: list[str] = []
    for path in tracked_spl_under(("src/lib/nogc_async_mut",)):
        for line_no, stripped in code_lines(path):
            match = NOGC_SYNC_WILDCARD_RE.search(stripped)
            if not match:
                continue
            sync_path = ROOT / "src/lib/nogc_sync_mut" / (match.group(1).replace(".", "/") + ".spl")
            if not sync_path.exists():
                continue
            sync_text = sync_path.read_text(encoding="utf-8", errors="ignore")
            if BACKEND_HOOK_RE.search(sync_text):
                hits.append(f"{rel(path)}:{line_no}: {stripped} -> {rel(sync_path)}")
    return hits


def gc_async_runtime_owner_wildcards() -> list[str]:
    hits: list[str] = []
    for path in tracked_spl_under(("src/lib/gc_async_mut",)):
        for line_no, stripped in code_lines(path):
            match = NOGC_SYNC_WILDCARD_RE.search(stripped)
            if not match:
                continue
            sync_path = ROOT / "src/lib/nogc_sync_mut" / (match.group(1).replace(".", "/") + ".spl")
            if not sync_path.exists():
                continue
            sync_text = sync_path.read_text(encoding="utf-8", errors="ignore")
            if BACKEND_HOOK_RE.search(sync_text):
                hits.append(f"{rel(path)}:{line_no}: {stripped} -> {rel(sync_path)}")
    return hits


def simpleos_lower_layer_imports() -> list[str]:
    hits: list[str] = []
    for path in tracked_spl_under(SIMPLEOS_NATIVE_ROOTS):
        for line_no, stripped in code_lines(path):
            if IMPORT_RE.match(stripped) and FORBIDDEN_SIMPLEOS_IMPORT_RE.search(stripped):
                hits.append(f"{rel(path)}:{line_no}: {stripped}")
    return hits


def is_platform_or_compat_path(path: Path) -> bool:
    path_text = "/" + rel(path)
    return any(part in path_text for part in PORTABLE_PLATFORM_ALLOW_PARTS)


def portable_lib_imports() -> list[str]:
    hits: list[str] = []
    for path in tracked_spl_under(PORTABLE_LIB_ROOTS):
        if is_platform_or_compat_path(path):
            continue
        for line_no, stripped in code_lines(path):
            if IMPORT_RE.match(stripped) and FORBIDDEN_PORTABLE_IMPORT_RE.search(stripped):
                hits.append(f"{rel(path)}:{line_no}: {stripped}")
    return hits


def nogc_family_gc_imports() -> list[str]:
    hits: list[str] = []
    for path in tracked_spl_under(NOGC_RUNTIME_ROOTS):
        for line_no, stripped in code_lines(path):
            if IMPORT_RE.match(stripped) and FORBIDDEN_NOGC_IMPORT_RE.search(stripped):
                hits.append(f"{rel(path)}:{line_no}: {stripped}")
    return hits


def documented_root_manifest_mismatches() -> list[str]:
    hits: list[str] = []
    try:
        matrix = SUPPORT_MATRIX.read_text(encoding="utf-8", errors="ignore")
    except OSError as err:
        return [f"{rel(SUPPORT_MATRIX)}: cannot read support matrix: {err}"]

    table_start = matrix.find("| Family | Compiler GcMode Enforcement |")
    table_end = matrix.find("### Compiler enforcement detail", table_start)
    if table_start < 0 or table_end < 0:
        return [f"{rel(SUPPORT_MATRIX)}: cannot locate current proof status table"]
    proof_table = matrix[table_start:table_end]

    for family in RUNTIME_FAMILIES:
        row_prefix = f"| `{family}` |"
        rows = [line for line in proof_table.splitlines() if line.startswith(row_prefix)]
        if not rows:
            hits.append(f"{rel(SUPPORT_MATRIX)}: missing current proof status row for {family}")
            continue
        row = rows[-1]
        columns = [column.strip() for column in row.strip().strip("|").split("|")]
        if len(columns) < 4:
            hits.append(f"{rel(SUPPORT_MATRIX)}: malformed current proof status row for {family}")
            continue
        documented = columns[3]
        has_manifest = (ROOT / "src/lib" / family / "__init__.spl").exists()
        documents_present = not documented.lower().startswith("no ")
        if documents_present != has_manifest:
            expected = "present" if has_manifest else "absent"
            hits.append(
                f"{rel(SUPPORT_MATRIX)}: {family} documents root manifest as "
                f"`{documented}`, but tracked src/lib/{family}/__init__.spl is {expected}"
            )
    return hits


def main() -> int:
    runtime_hooks = direct_runtime_hooks()
    duplicate_runtime_hooks = exact_duplicate_runtime_hooks()
    sync_runtime_hooks = sync_compat_direct_runtime_hooks()
    facade_violations = facade_mirror_violations()
    gc_self_facades = gc_async_one_line_self_facades()
    gc_wildcard_facades = gc_async_runtime_owner_wildcards()
    wildcard_facades = no_gc_async_runtime_owner_wildcards()
    simpleos_imports = simpleos_lower_layer_imports()
    portable_imports = portable_lib_imports()
    nogc_gc_imports = nogc_family_gc_imports()
    root_manifest_doc_mismatches = documented_root_manifest_mismatches()

    report = {
        "generated_by": "scripts/audit/runtime_backend_boundaries.py",
        "async_compat_direct_runtime_hook_count": len(runtime_hooks),
        "async_compat_direct_runtime_hook_samples": runtime_hooks[:20],
        "exact_duplicate_runtime_hook_count": len(duplicate_runtime_hooks),
        "exact_duplicate_runtime_hook_samples": duplicate_runtime_hooks[:20],
        "sync_compat_direct_runtime_hook_count": len(sync_runtime_hooks),
        "sync_compat_direct_runtime_hook_samples": sync_runtime_hooks[:20],
        "sync_compat_facade_mirror_violation_count": len(facade_violations),
        "sync_compat_facade_mirror_violation_samples": facade_violations[:20],
        "gc_async_one_line_self_facade_count": len(gc_self_facades),
        "gc_async_one_line_self_facade_samples": gc_self_facades[:20],
        "gc_async_runtime_owner_wildcard_facade_count": len(gc_wildcard_facades),
        "gc_async_runtime_owner_wildcard_facade_samples": gc_wildcard_facades[:20],
        "nogc_async_runtime_owner_wildcard_facade_count": len(wildcard_facades),
        "nogc_async_runtime_owner_wildcard_facade_samples": wildcard_facades[:20],
        "simpleos_lower_layer_posix_libc_import_count": len(simpleos_imports),
        "simpleos_lower_layer_posix_libc_import_samples": simpleos_imports[:20],
        "portable_lib_forbidden_posix_linux_import_count": len(portable_imports),
        "portable_lib_forbidden_posix_linux_import_samples": portable_imports[:20],
        "nogc_family_forbidden_gc_import_count": len(nogc_gc_imports),
        "nogc_family_forbidden_gc_import_samples": nogc_gc_imports[:20],
        "documented_root_manifest_mismatch_count": len(root_manifest_doc_mismatches),
        "documented_root_manifest_mismatch_samples": root_manifest_doc_mismatches[:20],
        "pass": not runtime_hooks
        and not duplicate_runtime_hooks
        and not sync_runtime_hooks
        and not facade_violations
        and not gc_self_facades
        and not gc_wildcard_facades
        and not wildcard_facades
        and not simpleos_imports
        and not portable_imports
        and not nogc_gc_imports
        and not root_manifest_doc_mismatches,
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
