#!/usr/bin/env python3
"""Generate SimpleOS multiarch hardening audit evidence.

This script intentionally reports missing evidence as failing JSON fields. It
does not manufacture green hardening status; tests can use the report to show
which production gates are still blocked.
"""

from __future__ import annotations

import json
import os
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "build/multiarch/harden_audit_report.json"
ARCHES = ["x86_64", "x86_32", "aarch64", "arm32", "riscv64", "riscv32"]

VENDORED_PARTS = {
    "src/compiler_rust/vendor",
    "src/runtime/vendor",
}

HAL_PREFIXES = (
    "src/os/kernel/arch/",
    "src/lib/nogc_async_mut_noalloc/baremetal/",
)


def owned_spl_files() -> list[Path]:
    files: list[Path] = []
    for base in ("src/os", "src/lib", "src/app"):
        root = ROOT / base
        if not root.exists():
            continue
        for path in root.rglob("*.spl"):
            rel = path.relative_to(ROOT).as_posix()
            if any(rel.startswith(part) for part in VENDORED_PARTS):
                continue
            files.append(path)
    return files


def code_lines(path: Path) -> list[tuple[int, str]]:
    out: list[tuple[int, str]] = []
    try:
        text = path.read_text(errors="ignore")
    except OSError:
        return out
    for idx, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        out.append((idx, stripped))
    return out


def outside_hal(path: Path) -> bool:
    rel = path.relative_to(ROOT).as_posix()
    return not any(rel.startswith(prefix) for prefix in HAL_PREFIXES)


def count_unsafe_outside_hal(files: list[Path]) -> tuple[int, list[str]]:
    hits: list[str] = []
    for path in files:
        if not outside_hal(path):
            continue
        rel = path.relative_to(ROOT).as_posix()
        for line_no, stripped in code_lines(path):
            if stripped.startswith("unsafe:") or stripped.startswith("@nocheck"):
                hits.append(f"{rel}:{line_no}")
    return len(hits), hits[:20]


def count_direct_arch_imports(files: list[Path]) -> tuple[int, list[str]]:
    pattern = re.compile(r"^\s*use\s+os\.kernel\.arch\.(x86_64|x86_32|arm64|arm32|riscv64|riscv32)\b")
    hits: list[str] = []
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        if rel.startswith("src/os/kernel/arch/"):
            continue
        if rel.startswith("src/os/kernel/arch_adapt/"):
            continue
        try:
            text = path.read_text(errors="ignore")
        except OSError:
            continue
        for line_no, line in enumerate(text.splitlines(), 1):
            if pattern.search(line):
                hits.append(f"{rel}:{line_no}")
    return len(hits), hits[:20]


def wx_violations(files: list[Path]) -> tuple[int, list[str]]:
    hits: list[str] = []
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        if not rel.startswith("src/os/kernel/"):
            continue
        for line_no, stripped in code_lines(path):
            if "VmFlags(bits:" in stripped and "VM_WRITABLE" in stripped and "VM_NO_EXECUTE" not in stripped:
                hits.append(f"{rel}:{line_no}")
            elif "VmFlags(bits:" in stripped and "bits: 7" in stripped:
                hits.append(f"{rel}:{line_no}")
    return len(hits), hits[:20]


def cap_check_coverage() -> tuple[int, int]:
    path = ROOT / "src/os/kernel/ipc/syscall.spl"
    if not path.exists():
        return 0, 0
    lines = path.read_text(errors="ignore").splitlines()
    branches: list[tuple[str, str]] = []
    current_name = ""
    current_body: list[str] = []
    in_syscall_match = False
    for line in lines:
        stripped = line.strip()
        if stripped == "match args.id:":
            in_syscall_match = True
            continue
        if not in_syscall_match:
            continue
        if stripped.startswith("fn ") and current_name:
            break
        if stripped.startswith("case ") and "#" in stripped:
            if current_name:
                branches.append((current_name, "\n".join(current_body)))
            current_name = stripped
            current_body = [stripped]
        elif current_name:
            current_body.append(line)
    if current_name:
        branches.append((current_name, "\n".join(current_body)))

    protected = 0
    uncovered = 0
    for name, body in branches:
        if "always allowed" in name:
            continue
        protected = protected + 1
        if "_cap_check(" not in body:
            uncovered = uncovered + 1

    if protected <= 0:
        return 0, 0
    coverage = int(((protected - uncovered) * 100) / protected)
    return coverage, uncovered


def check_bounds_emitted() -> bool:
    lowering_paths = [
        ROOT / "src/compiler/50.mir/mir_lowering_expr_part1.spl",
        ROOT / "src/compiler/50.mir/mir_lowering_stmts.spl",
    ]
    runtime_paths = [
        ROOT / "src/runtime/runtime.c",
        ROOT / "src/runtime/runtime.h",
    ]
    try:
        lowering = "\n".join(path.read_text(errors="ignore") for path in lowering_paths)
        runtime = "\n".join(path.read_text(errors="ignore") for path in runtime_paths)
    except OSError:
        return False
    return (
        'MirInstKind.Intrinsic(nil, "bounds_check"' in lowering
        and "__simple_intrinsic_bounds_check" in runtime
    )


def canary_log_ok(arch: str) -> bool:
    path = ROOT / f"build/multiarch/{arch}/canary_runtime.json"
    if not path.exists():
        return False
    try:
        body = json.loads(path.read_text(errors="ignore"))
    except (OSError, json.JSONDecodeError):
        return False
    return body.get("differs_across_reboots") is True


def text_write_trap_ok() -> bool:
    path = ROOT / "build/multiarch/x86_64/text_write_trap.json"
    if not path.exists():
        return False
    try:
        body = json.loads(path.read_text(errors="ignore"))
    except (OSError, json.JSONDecodeError):
        return False
    return body.get("trap_observed") is True


def main() -> int:
    files = owned_spl_files()
    nocheck_unsafe_count, unsafe_samples = count_unsafe_outside_hal(files)
    direct_arch_count, direct_arch_samples = count_direct_arch_imports(files)
    wx_count, wx_samples = wx_violations(files)
    cap_pct, uncovered_syscalls = cap_check_coverage()

    per_arch_exit_codes = {}
    canary_runtime = {}
    for arch in ARCHES:
        canary_ok = canary_log_ok(arch)
        canary_runtime[arch] = {"differs_across_reboots": canary_ok}
        per_arch_exit_codes[arch] = 0 if canary_ok else 1

    text_trap = text_write_trap_ok()
    report = {
        "generated_by": "scripts/audit/os_harden_audit.py",
        "nocheck_outside_hal": nocheck_unsafe_count,
        "unsafe_outside_hal": nocheck_unsafe_count,
        "unsafe_outside_hal_samples": unsafe_samples,
        "direct_arch_imports_outside_arch": direct_arch_count,
        "direct_arch_import_samples": direct_arch_samples,
        "cap_check_coverage_pct": cap_pct,
        "syscall_variants_uncovered": uncovered_syscalls,
        "wx_violations": wx_count,
        "wx_violation_samples": wx_samples,
        "x86_32_nx_status": "present_in_audit_pending_runtime_proof",
        "text_write_trap": text_trap,
        "check_bounds_emitted": check_bounds_emitted(),
        "canary_runtime": canary_runtime,
        "per_arch_exit_codes": per_arch_exit_codes,
    }
    report["all_arch_pass"] = (
        nocheck_unsafe_count == 0
        and direct_arch_count == 0
        and wx_count == 0
        and cap_pct == 100
        and uncovered_syscalls == 0
        and text_trap
        and report["check_bounds_emitted"]
        and all(code == 0 for code in per_arch_exit_codes.values())
    )

    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0 if report["all_arch_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
