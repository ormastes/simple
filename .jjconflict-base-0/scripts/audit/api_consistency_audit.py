#!/usr/bin/env python3
"""Audit public-ish Simple API names against the production naming contract.

This gate is intentionally split into hard failures and advisory debt:
- Hard failures are names the contract explicitly rejects.
- Predicate-prefix names are counted as legacy/advisory because the current
  codebase has many established `is_*`/`has_*` helpers and migrating them needs
  compatibility planning.
"""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BASELINE = ROOT / "scripts/audit/api_consistency_baseline.json"
SCAN_ROOTS = [
    ROOT / "src/compiler",
    ROOT / "src/app",
    ROOT / "src/lib/common",
]
DECL_RE = re.compile(r"^\s*(?:static\s+fn|fn|me)\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
HARD_REJECTED = {
    "get_or_fail": "Use fetch for required lookup or get for optional lookup.",
    "maybe_get_value": "Use get for optional lookup.",
    "filter_not": "Use reject for filter-drop semantics.",
    "append_all_items": "Use extend or concat.",
    "stringify": "Use to_string.",
    "str_value": "Use as_str or to_string depending on allocation.",
    "do_validation": "Use validate or check.",
    "transform_values": "Use map when the receiver already implies values.",
    "for_each_item": "Use each.",
    "iterate_all": "Use each or iter.",
}
ADVISORY_PREFIXES = ("is_", "has_")


def load_baseline() -> dict:
    try:
        with BASELINE.open(encoding="utf-8") as fh:
            return json.load(fh)
    except FileNotFoundError:
        return {}


def root_bucket(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    for root in SCAN_ROOTS:
        root_rel = root.relative_to(ROOT).as_posix()
        if rel.startswith(root_rel + "/"):
            return root_rel
    return rel.split("/", 1)[0]


def iter_files() -> list[Path]:
    files: list[Path] = []
    for root in SCAN_ROOTS:
        if not root.exists():
            continue
        for path in root.rglob("*.spl"):
            rel = path.relative_to(ROOT).as_posix()
            if "/vendor/" in rel:
                continue
            files.append(path)
    return sorted(files)


def main() -> int:
    hard_hits: list[str] = []
    advisory_hits: list[str] = []
    advisory_by_root: dict[str, int] = {}
    declarations = 0

    for path in iter_files():
        rel = path.relative_to(ROOT).as_posix()
        try:
            lines = path.read_text(errors="ignore").splitlines()
        except OSError:
            continue
        for line_no, line in enumerate(lines, 1):
            match = DECL_RE.match(line)
            if not match:
                continue
            declarations += 1
            name = match.group(1)
            if name in HARD_REJECTED:
                hard_hits.append(f"{rel}:{line_no}: {name} - {HARD_REJECTED[name]}")
            elif name.startswith(ADVISORY_PREFIXES):
                advisory_hits.append(f"{rel}:{line_no}: {name}")
                bucket = root_bucket(path)
                advisory_by_root[bucket] = advisory_by_root.get(bucket, 0) + 1

    baseline = load_baseline()
    baseline_advisory = baseline.get("advisory_predicate_prefix_debt")
    baseline_by_root = baseline.get("advisory_predicate_prefix_debt_by_root", {})
    baseline_violations: list[str] = []
    if isinstance(baseline_advisory, int) and len(advisory_hits) > baseline_advisory:
        baseline_violations.append(
            f"advisory predicate-prefix debt increased from {baseline_advisory} to {len(advisory_hits)}"
        )
    if isinstance(baseline_by_root, dict):
        for bucket, count in sorted(advisory_by_root.items()):
            baseline_count = baseline_by_root.get(bucket)
            if isinstance(baseline_count, int) and count > baseline_count:
                baseline_violations.append(
                    f"{bucket} advisory predicate-prefix debt increased from {baseline_count} to {count}"
                )

    print("API Consistency Audit")
    print("=====================")
    print(f"Scanned {declarations} function/method declarations")
    print(f"Hard violations: {len(hard_hits)}")
    for item in hard_hits[:50]:
        print(f"  - {item}")
    if len(hard_hits) > 50:
        print(f"  ... {len(hard_hits) - 50} more")
    print(f"Advisory predicate-prefix debt: {len(advisory_hits)}")
    for item in advisory_hits[:20]:
        print(f"  - {item}")
    if len(advisory_hits) > 20:
        print(f"  ... {len(advisory_hits) - 20} more")
    if isinstance(baseline_advisory, int):
        print(f"Advisory baseline: {baseline_advisory}")
    if advisory_by_root:
        print("Advisory debt by root:")
        for bucket, count in sorted(advisory_by_root.items()):
            print(f"  - {bucket}: {count}")
    if baseline_violations:
        print("Baseline violations:")
        for item in baseline_violations:
            print(f"  - {item}")
    return 1 if hard_hits or baseline_violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
