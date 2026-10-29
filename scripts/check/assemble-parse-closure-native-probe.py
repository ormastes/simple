#!/usr/bin/env python3
"""Assemble the production closure owner with deterministic native domain fixtures.

Only import directives are removed. Production functions and scratch helpers
are copied verbatim; domain I/O is supplied by the fixture. This is allocator
and transaction-lifetime evidence, not full coordinator/inventory admission.
"""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def without_imports(path: Path) -> str:
    lines = path.read_text().splitlines(keepends=True)
    result = []
    importing = False
    for line in lines:
        if line.startswith("use "):
            importing = "{" in line and "}" not in line
            continue
        if importing:
            if "}" in line:
                importing = False
            continue
        result.append(line)
    if importing:
        raise ValueError(f"unterminated import in {path}")
    return "".join(result)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--owner", type=Path, default=ROOT / "src/app/cli/native_build_parse_closure_owner.spl")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    text = "use std.nogc_sync_mut.sffi.transient.*\n"
    text += without_imports(ROOT / "src/app/cli/native_build_parse_closure_scratch.spl")
    text += "\n" + without_imports(args.owner)
    text += "\n" + (ROOT / "test/fixtures/bootstrap/parse_closure_staged_coordinator.spl").read_text()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text)


if __name__ == "__main__":
    main()
