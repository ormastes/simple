#!/usr/bin/env python3
"""Audit compiler diagnostic code literals for stable public shapes."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCAN_ROOTS = [ROOT / "src/compiler", ROOT / "src/app", ROOT / "src/compiler_rust/driver/src/cli"]
SOURCE_SUFFIXES = {".spl", ".rs"}
CODE_ASSIGN = re.compile(
    r"\b(?:error_code|warning_code)\s*:\s*\"([^\"]+)\""
    r"|\bcode\s*:\s*Some\(\"([^\"]+)\"(?:\.to_string\(\))?\)"
)
PUBLIC_CODE = re.compile(r"^[EW][0-9]{4}$")
ALLOWED_TOOL_CODE = re.compile(r"^(L-[A-Z]+-[0-9]{3}|SEC-[A-Z]+[0-9]{3}|GAME-[A-Z]+-[0-9]{3})$")


def is_allowed(code: str) -> bool:
    return bool(PUBLIC_CODE.match(code) or ALLOWED_TOOL_CODE.match(code))


def main() -> int:
    violations: list[str] = []
    scanned = 0
    for root in SCAN_ROOTS:
        if not root.exists():
            continue
        for path in sorted(root.rglob("*")):
            if path.suffix not in SOURCE_SUFFIXES:
                continue
            rel = path.relative_to(ROOT).as_posix()
            if "/vendor/" in rel:
                continue
            scanned += 1
            try:
                text = path.read_text(errors="ignore")
            except OSError:
                continue
            for line_no, line in enumerate(text.splitlines(), 1):
                for match in CODE_ASSIGN.finditer(line):
                    code = match.group(1) or match.group(2)
                    if not is_allowed(code):
                        violations.append(f"{rel}:{line_no}: {code}")

    print("Diagnostic Code Audit")
    print("=====================")
    print(f"Scanned {scanned} files")
    if not violations:
        print("All diagnostic code literals use stable public shapes")
        return 0
    print("Invalid diagnostic code literals:")
    for item in violations[:50]:
        print(f"  - {item}")
    if len(violations) > 50:
        print(f"  ... {len(violations) - 50} more")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
