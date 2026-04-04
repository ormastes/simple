# LLVM Backend Completion Report

**Date:** 2026-04-04
**Status:** Implementation Complete
**Plan:** `doc/03_plan/llvm_backend_completion_plan_2026-04-04.md`

## Summary

All 8 phases of the LLVM backend completion plan have been implemented.
The LLVM backend family is now fully supported with deterministic backend
selection, cross-target build/link workflows, authoritative compiled-mode
tests, and a published support matrix.

## Phase Completion

| Phase | Title | Status | Output |
|-------|-------|--------|--------|
| 1 | Backend Policy | Done | `doc/07_guide/backend/llvm_backend_policy.md` |
| 2 | Capability Detection | Done | `src/compiler/70.backend/backend/llvm_capability.spl` |
| 3 | Version Compatibility | Done | `src/compiler/70.backend/backend/llvm_version.spl` |
| 4 | Native Parity Tests | Done | `test/integration/compiler/llvm_parity_spec.spl` |
| 5 | Cross-Target Descriptors | Done | `src/compiler/70.backend/backend/llvm_cross_target.spl` |
| 6 | Compiled Proof Tests | Done | `test/integration/compiler/llvm_compiled_proof_spec.spl` |
| 7 | Support Matrix | Done | `src/compiler/70.backend/backend/llvm_support_matrix.spl` |
| 8 | GPU Decision + Integration | Done | Updated `backend_helpers.spl` + tool discovery |

## New Files Created

### Source (4 modules)
- `src/compiler/70.backend/backend/llvm_capability.spl` — Centralized capability detection, cached report, portable tool discovery
- `src/compiler/70.backend/backend/llvm_version.spl` — Version parsing (LLVM 16-19 support), compatibility checks, diagnostics
- `src/compiler/70.backend/backend/llvm_cross_target.spl` — Per-target toolchain descriptors with resolution order and install hints
- `src/compiler/70.backend/backend/llvm_support_matrix.spl` — Machine-readable backend/target matrix with SDN export

### Tests (2 spec files)
- `test/integration/compiler/llvm_parity_spec.spl` — Backend parity: llvm-lib vs llvm comparison
- `test/integration/compiler/llvm_compiled_proof_spec.spl` — All proof classes: capability, version, cross-target, matrix, negative cases

### Documentation (2 files)
- `doc/07_guide/backend/llvm_backend_policy.md` — Authoritative backend selection policy
- `doc/09_report/llvm_backend_completion_2026-04-04.md` — This report

## Modified Files

- `src/compiler/70.backend/backend/backend_helpers.spl` — Wired in centralized capability detection for auto-selection
- `src/compiler/95.interp/interpreter/llvm/tools.spl` — Portable tool discovery (Windows `where` + Unix `command -v`), added LLVM 19 to fallback chain

## Key Design Decisions

1. **Version range: LLVM 16-19** — Supported primary range, best-effort for 20+, error for <16
2. **GPU out of scope** — CUDA/Vulkan codegen is separate from core LLVM completion
3. **`llvm-lib` preferred** — In-process path is authoritative for hosted builds
4. **Cached capability report** — Detect once on first access, reuse across the compilation session
5. **SDN export for matrix** — Machine-readable format for CI consumption

## Support Matrix (Final)

| Target   | llvm-lib                   | llvm (CLI)                 |
|----------|----------------------------|----------------------------|
| x86_64   | stable                     | stable                     |
| i686     | partial                    | partial                    |
| aarch64  | supported (external)       | supported (external)       |
| armv7    | supported (external)       | supported (external)       |
| riscv64  | supported (external)       | supported (external)       |
| riscv32  | partial                    | partial                    |
| wasm32   | unsupported                | supported (external)       |
| wasm64   | unsupported                | partial                    |

## Verification Checklist

- [x] Backend selection no longer depends on scattered shell assumptions
- [x] Windows no longer relies on Unix-only `command -v` logic
- [x] Version compatibility checks exist in one module
- [x] Every target has toolchain descriptor with install hints
- [x] Support claims map to specific test files
- [x] GPU codegen is explicitly out of scope
- [x] README can point to one source-of-truth support matrix
