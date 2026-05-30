#!/usr/bin/env python3
"""Ingest runtime hardening markers from QEMU serial logs.

The script is intentionally fail-closed: it only writes green evidence files
when serial logs contain the expected runtime markers. It does not synthesize
canary variation or text-write trap success from static source state.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUT_ROOT = ROOT / "build/multiarch"
DEFAULT_ARCHES = ["x86_64", "x86_32", "aarch64", "arm32", "riscv64", "riscv32"]
CANARY_RE = re.compile(r"\[harden\]\s+canary\s+arch=([A-Za-z0-9_]+)\s+value=([0-9]+)")
TEXT_TRAP_RE = re.compile(r"\[harden\]\s+text_write_trap=(pass|fail)\b")


def _read(path: Path) -> str:
    try:
        return path.read_text(errors="ignore")
    except OSError:
        return ""


def _write_json(path: Path, body: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n")


def ingest_canary(arch: str, logs: list[Path]) -> bool:
    values: list[str] = []
    sources: list[str] = []
    for log in logs:
        body = _read(log)
        for match in CANARY_RE.finditer(body):
            if match.group(1) != arch:
                continue
            value = match.group(2)
            if value != "0":
                values.append(value)
                sources.append(str(log.relative_to(ROOT) if log.is_relative_to(ROOT) else log))
    distinct = sorted(set(values))
    ok = len(distinct) >= 2
    if values:
        _write_json(
            OUT_ROOT / arch / "canary_runtime.json",
            {
                "arch": arch,
                "differs_across_reboots": ok,
                "samples": values[:8],
                "distinct_sample_count": len(distinct),
                "sources": sources[:8],
            },
        )
    return ok


def ingest_text_trap(logs: list[Path]) -> bool:
    passed = False
    sources: list[str] = []
    for log in logs:
        body = _read(log)
        for match in TEXT_TRAP_RE.finditer(body):
            if match.group(1) == "pass":
                passed = True
                sources.append(str(log.relative_to(ROOT) if log.is_relative_to(ROOT) else log))
    if sources:
        _write_json(
            OUT_ROOT / "x86_64/text_write_trap.json",
            {
                "arch": "x86_64",
                "trap_observed": passed,
                "sources": sources[:8],
            },
        )
    return passed


def discover_logs() -> list[Path]:
    candidates: list[Path] = []
    for pattern in (
        "build/multiarch/**/*.log",
        "build/multiarch/**/*serial*.txt",
        "build/multiarch/**/*serial*.log",
        "build/qemu-*serial*.log",
    ):
        candidates.extend(ROOT.glob(pattern))
    return sorted(set(path for path in candidates if path.is_file()))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--arch", action="append")
    parser.add_argument("logs", nargs="*")
    args = parser.parse_args()

    logs = [Path(p).resolve() for p in args.logs] if args.logs else discover_logs()
    arches = args.arch if args.arch else DEFAULT_ARCHES
    canary_results = [ingest_canary(arch, logs) for arch in arches]
    canary_ok = all(canary_results)
    text_ok = ingest_text_trap(logs)
    return 0 if canary_ok and text_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
