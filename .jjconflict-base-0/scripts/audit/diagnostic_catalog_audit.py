#!/usr/bin/env python3
"""Verify stable diagnostic codes have useful catalog explanations."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CODE_ASSIGN = re.compile(
    r"\b(?:error_code|warning_code)\s*:\s*\"([EW][0-9]{4})\""
    r"|\bcode\s*:\s*Some\(\"([EW][0-9]{4})\"(?:\.to_string\(\))?\)"
)
ENUM_ERROR_CODE = re.compile(r"^\s*([EW][0-9]{4})\s*$")
CATALOG_ENTRY_START = "self.register(ErrorExplanation("
CATALOG_CODE = re.compile(r"\bcode:\s*\"([EW][0-9]{4})\"")
TEXT_FIELD = re.compile(r"\b(title|description):\s*\"([^\"]+)\"")
LIST_FIELD = re.compile(r"\b(causes|fixes):\s*\[([^\]]*)\]", re.DOTALL)
SCAN_ROOTS = [ROOT / "src/compiler", ROOT / "src/app", ROOT / "src/compiler_rust/driver/src/cli"]
SOURCE_SUFFIXES = {".spl", ".rs"}
CATALOG = ROOT / "src/compiler/95.interp/interpreter/errors.spl"


def assigned_codes() -> set[str]:
    codes: set[str] = set()
    for root in SCAN_ROOTS:
        if not root.exists():
            continue
        for path in sorted(root.rglob("*")):
            if path.suffix not in SOURCE_SUFFIXES:
                continue
            try:
                text = path.read_text(errors="ignore")
            except OSError:
                continue
            for match in CODE_ASSIGN.finditer(text):
                code = match.group(1) or match.group(2)
                codes.add(code)
            in_error_code_enum = False
            for line in text.splitlines():
                stripped = line.strip()
                if stripped.startswith("enum ") and stripped.endswith("ErrorCode:"):
                    in_error_code_enum = True
                    continue
                if in_error_code_enum and stripped and not line.startswith(" "):
                    in_error_code_enum = False
                if in_error_code_enum:
                    enum_match = ENUM_ERROR_CODE.match(line)
                    if enum_match:
                        codes.add(enum_match.group(1))
    return codes


def catalog_entries() -> dict[str, dict[str, object]]:
    if not CATALOG.exists():
        return {}
    text = CATALOG.read_text(errors="ignore")
    entries: dict[str, dict[str, object]] = {}
    for block in text.split(CATALOG_ENTRY_START)[1:]:
        end = block.find("))")
        if end < 0:
            continue
        body = block[:end]
        code_match = CATALOG_CODE.search(body)
        if not code_match:
            continue
        code = code_match.group(1)
        fields: dict[str, object] = {"code": code}
        for match in TEXT_FIELD.finditer(body):
            fields[match.group(1)] = match.group(2).strip()
        for match in LIST_FIELD.finditer(body):
            values = [item.strip() for item in re.findall(r"\"([^\"]+)\"", match.group(2))]
            fields[match.group(1)] = values
        entries[code] = fields
    return entries


def quality_violations(assigned: set[str], entries: dict[str, dict[str, object]]) -> list[str]:
    violations: list[str] = []
    for code in sorted(assigned):
        entry = entries.get(code)
        if not entry:
            violations.append(f"{code}: missing catalog entry")
            continue
        for field in ("title", "description"):
            value = entry.get(field)
            if not isinstance(value, str) or not value:
                violations.append(f"{code}: missing non-empty {field}")
        for field in ("causes", "fixes"):
            value = entry.get(field)
            if not isinstance(value, list) or len(value) == 0:
                violations.append(f"{code}: missing non-empty {field}")
    return violations


def main() -> int:
    assigned = assigned_codes()
    catalog = catalog_entries()
    missing = sorted(assigned - set(catalog.keys()))
    quality = quality_violations(assigned, catalog)

    print("Diagnostic Catalog Audit")
    print("========================")
    print(f"Assigned stable codes: {len(assigned)}")
    print(f"Catalog entries: {len(catalog)}")
    if not missing and not quality:
        print("All assigned stable diagnostic codes have useful catalog entries")
        return 0
    if missing:
        print("Missing catalog entries:")
        for code in missing:
            print(f"  - {code}")
    if quality:
        print("Catalog quality violations:")
        for item in quality:
            print(f"  - {item}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
