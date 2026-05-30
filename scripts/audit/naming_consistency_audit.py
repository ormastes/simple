#!/usr/bin/env python3
"""Audit public Simple API names for verbose naming patterns.

Checks:
  N001 - Verbose `get_*` prefix on noun accessors in src/lib/
  N002 - Module naming inconsistency (both short and long forms in same layer)
  N003 - Duplicate predicate (is_*/has_*) functions across files (same name+sig)
  N004 - `set_from_*` constructor pattern (should be `from_*`)

Exit 0 if no NEW violations beyond baseline. Exit 1 on new violations.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASELINE = ROOT / "scripts/audit/naming_consistency_baseline.json"
LIB_ROOT = ROOT / "src/lib"

PUB_FN_GET_RE = re.compile(r"^\s*pub fn (get_[A-Za-z_][A-Za-z0-9_]*)\s*[<(]")
SET_FROM_RE = re.compile(r"^\s*pub fn (set_from_[A-Za-z_][A-Za-z0-9_]*)\s*[<(]")
PRED_RE = re.compile(r"^\s*pub fn ((is_|has_)[A-Za-z_][A-Za-z0-9_]*)\s*\(([^)]*)\)")

N002_CONFLICT_PAIRS = [
    ("fs", "file_system"),
    ("db", "database"),
    ("compress", "compression"),
]


# ---------------------------------------------------------------------------
# File helpers
# ---------------------------------------------------------------------------

def iter_lib_files() -> list[Path]:
    files: list[Path] = []
    if not LIB_ROOT.exists():
        return files
    for path in LIB_ROOT.rglob("*.spl"):
        rel = path.relative_to(ROOT).as_posix()
        if "/vendor/" in rel:
            continue
        files.append(path)
    return sorted(files)


def read_lines(path: Path) -> list[str]:
    try:
        return path.read_text(errors="ignore").splitlines()
    except OSError:
        return []


# ---------------------------------------------------------------------------
# Check implementations
# ---------------------------------------------------------------------------

def check_n001(files: list[Path]) -> list[dict]:
    """N001: Verbose `get_*` prefix — any `pub fn get_X` where X is a noun."""
    hits: list[dict] = []
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        for lineno, line in enumerate(read_lines(path), 1):
            m = PUB_FN_GET_RE.match(line)
            if not m:
                continue
            name = m.group(1)
            suggestion = name[4:]  # drop "get_"
            hits.append({
                "code": "N001",
                "file": rel,
                "line": lineno,
                "current": name,
                "suggested": suggestion,
                "message": f"Verbose `get_` prefix: rename `{name}` to `{suggestion}`",
            })
    return hits


def check_n002() -> list[dict]:
    """N002: Module naming inconsistency — short and long form coexist in the same layer."""
    hits: list[dict] = []
    if not LIB_ROOT.exists():
        return hits
    for layer in sorted(LIB_ROOT.iterdir()):
        if not layer.is_dir():
            continue
        subdirs = {d.name for d in layer.iterdir() if d.is_dir()}
        layer_rel = layer.relative_to(ROOT).as_posix()
        for short, long_form in N002_CONFLICT_PAIRS:
            if short in subdirs and long_form in subdirs:
                hits.append({
                    "code": "N002",
                    "file": layer_rel,
                    "line": 0,
                    "current": f"{short}/ + {long_form}/",
                    "suggested": f"{short}/ (API) + {long_form}/ (impl)",
                    "message": (
                        f"Complementary pair: `{short}/` (public API) and `{long_form}/` "
                        f"(impl/legacy) coexist in `{layer_rel}/` — verify cross-references "
                        f"(see lib_architecture.md §5)"
                    ),
                })
    return hits


def check_n003(files: list[Path]) -> list[dict]:
    """N003: Duplicate predicate — same `is_*`/`has_*` name+signature in multiple files."""
    pred_map: dict[tuple[str, str], list[tuple[str, int]]] = defaultdict(list)
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        for lineno, line in enumerate(read_lines(path), 1):
            m = PRED_RE.match(line)
            if not m:
                continue
            fname = m.group(1)
            sig = m.group(3).strip()
            pred_map[(fname, sig)].append((rel, lineno))

    hits: list[dict] = []
    for (fname, sig), locs in sorted(pred_map.items()):
        if len(locs) < 2:
            continue
        first_file, first_line = locs[0]
        others = "; ".join(f"{f}:{ln}" for f, ln in locs[1:])
        hits.append({
            "code": "N003",
            "file": first_file,
            "line": first_line,
            "current": f"{fname}({sig})",
            "suggested": f"single canonical definition (duplicated in: {others})",
            "message": (
                f"Duplicate predicate `{fname}({sig})` declared in {len(locs)} files — "
                f"consider delegating to one canonical definition"
            ),
            "duplicates": [{"file": f, "line": ln} for f, ln in locs],
        })
    return hits


def check_n004(files: list[Path]) -> list[dict]:
    """N004: `set_from_*` pattern that looks like a constructor (should be `from_*`)."""
    hits: list[dict] = []
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        for lineno, line in enumerate(read_lines(path), 1):
            m = SET_FROM_RE.match(line)
            if not m:
                continue
            name = m.group(1)
            suggestion = name[4:]  # drop "set_" -> "from_*"
            hits.append({
                "code": "N004",
                "file": rel,
                "line": lineno,
                "current": name,
                "suggested": suggestion,
                "message": f"`set_from_*` constructor pattern: rename `{name}` to `{suggestion}`",
            })
    return hits


# ---------------------------------------------------------------------------
# Baseline helpers
# ---------------------------------------------------------------------------

def load_baseline(path: Path) -> dict:
    try:
        with path.open(encoding="utf-8") as fh:
            return json.load(fh)
    except FileNotFoundError:
        return {}


def count_by_code(hits: list[dict]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for h in hits:
        counts[h["code"]] = counts.get(h["code"], 0) + 1
    return counts


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def print_hits(hits: list[dict], limit: int = 50) -> None:
    shown = hits[:limit]
    for h in shown:
        loc = f"{h['file']}:{h['line']}" if h["line"] else h["file"]
        print(f"  [{h['code']}] {loc}: {h['message']}")
    if len(hits) > limit:
        print(f"  ... {len(hits) - limit} more")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description="Naming consistency audit for Simple source.")
    parser.add_argument(
        "--baseline",
        metavar="PATH",
        default=str(DEFAULT_BASELINE),
        help="Path to baseline JSON (default: scripts/audit/naming_consistency_baseline.json)",
    )
    parser.add_argument(
        "--fix-suggestions",
        metavar="PATH",
        help="Write machine-readable fix suggestions to this JSON file",
    )
    args = parser.parse_args()

    baseline_path = Path(args.baseline)
    baseline = load_baseline(baseline_path)

    files = iter_lib_files()

    n001 = check_n001(files)
    n002 = check_n002()
    n003 = check_n003(files)
    n004 = check_n004(files)

    all_hits = n001 + n002 + n003 + n004
    counts = count_by_code(all_hits)

    print("Naming Consistency Audit")
    print("========================")
    print(f"Scanned {len(files)} .spl files under src/lib/")
    print()

    print(f"N001 - Verbose get_* prefix: {len(n001)}")
    print_hits(n001)
    print()

    print(f"N002 - Module naming inconsistency: {len(n002)}")
    print_hits(n002)
    print()

    print(f"N003 - Duplicate predicates: {len(n003)}")
    print_hits(n003)
    print()

    print(f"N004 - set_from_* constructor pattern: {len(n004)}")
    print_hits(n004)
    print()

    # Baseline comparison
    baseline_counts = baseline.get("counts", {})
    new_violations: list[str] = []
    for code, count in sorted(counts.items()):
        base = baseline_counts.get(code)
        if isinstance(base, int) and count > base:
            new_violations.append(
                f"{code} violation count increased from {base} to {count}"
            )

    if baseline_counts:
        print("Baseline comparison:")
        for code in sorted(set(list(counts) + list(baseline_counts))):
            cur = counts.get(code, 0)
            base = baseline_counts.get(code, "N/A")
            status = ""
            if isinstance(base, int):
                if cur > base:
                    status = " [REGRESSION]"
                elif cur < base:
                    status = " [IMPROVED]"
            print(f"  {code}: current={cur}, baseline={base}{status}")
        print()

    if new_violations:
        print("Baseline violations (CI gate):")
        for item in new_violations:
            print(f"  - {item}")
        print()

    if args.fix_suggestions:
        fix_path = Path(args.fix_suggestions)
        fix_data = {
            "generated_on": __import__("datetime").date.today().isoformat(),
            "fixes": [
                {
                    "code": h["code"],
                    "file": h["file"],
                    "line": h["line"],
                    "current": h["current"],
                    "suggested": h["suggested"],
                }
                for h in all_hits
            ],
        }
        fix_path.write_text(json.dumps(fix_data, indent=2), encoding="utf-8")
        print(f"Fix suggestions written to: {fix_path}")

    return 1 if new_violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
