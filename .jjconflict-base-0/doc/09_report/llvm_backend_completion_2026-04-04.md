# LLVM Backend Completion Report

**Date:** 2026-04-04
**Status:** Full-Family Completion — all rows resolved to stable/unsupported
**Plan:** `doc/03_plan/llvm_backend_completion_plan_2026-04-04.md`, `doc/03_plan/llvm_full_family_multi_agent_completion_plan_2026-04-04.md`

## Summary

All 8 phases of the LLVM backend completion plan have been implemented, followed
by a full-family closure program that resolved every remaining ambiguous row.
The LLVM backend family now has deterministic backend selection, cross-target
build/link workflows, and a fully closed support matrix with no ambiguous
middle states — every row is either `stable` (with authoritative proof) or
`unsupported` (with deterministic diagnostics).

## Full-Family Closure (Multi-Agent Completion)

The full-family closure program eliminated all `partial` and `supported (external)`
states from the public matrix. Executed via 5 parallel Opus agent teams:

### Final Matrix

| Target   | llvm-lib       | llvm (CLI)     | Change |
|----------|----------------|----------------|--------|
| x86_64   | **stable**     | **stable**     | no change |
| i686     | unsupported    | unsupported    | demoted — multilib not portable |
| aarch64  | **stable**     | **stable**     | llvm-lib promoted (libLLVM includes AArch64 natively) |
| armv7    | unsupported    | unsupported    | demoted — hard-float ABI + sysroot not portable |
| riscv64  | **stable**     | **stable**     | llvm-lib promoted (libLLVM includes RISC-V natively) |
| riscv32  | unsupported    | unsupported    | demoted — baremetal-only, not portable |
| wasm32   | unsupported    | **stable**     | no change (llvm-lib WASM not implemented) |
| wasm64   | unsupported    | **stable**     | no change (llvm-lib WASM not implemented) |

### Rows Promoted (2)
- **aarch64 llvm-lib:** Standard distro libLLVM includes AArch64 target; cross-linker readily available
- **riscv64 llvm-lib:** Standard distro libLLVM includes RISC-V target; cross-linker readily available

### Rows Demoted (4)
- **i686 (both):** 32-bit multilib requires gcc-multilib which is not universally available
- **armv7 (both):** Hard-float ABI cross-compilation requires non-standard sysroot setup
- **riscv32 (both):** Bare-metal only with no hosted linking; toolchain setup not portable

### rust-llvm Decision
Per [ADR](../04_architecture/adr_rust_llvm_exclusion.md): formally excluded from public family claim (bootstrap-only).

### New Test Files
- `test/integration/compiler/llvm_i686_closure_spec.spl`
- `test/integration/compiler/llvm_aarch64_closure_spec.spl`
- `test/integration/compiler/llvm_armv7_closure_spec.spl`
- `test/integration/compiler/llvm_riscv_closure_spec.spl`

### New Source Additions
- `FinalSupportLevel` enum in `llvm_support_matrix.spl` — two-state public API
- `validate_matrix_closure()` — returns errors for non-final rows
- `detect_multilib()`, `detect_cross_sysroot()`, `detect_cross_linker()` in `llvm_capability.spl`
- `generate_capability_report()` — comprehensive cross-target diagnostic

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
6. **`rust-llvm` is bootstrap-only** — It is documented as an out-of-band seed path, not a public matrix column or release claim

## Support Matrix (Final)

| Target   | llvm-lib       | llvm (CLI)     |
|----------|----------------|----------------|
| x86_64   | stable         | stable         |
| i686     | unsupported    | unsupported    |
| aarch64  | stable         | stable         |
| armv7    | unsupported    | unsupported    |
| riscv64  | stable         | stable         |
| riscv32  | unsupported    | unsupported    |
| wasm32   | unsupported    | stable         |
| wasm64   | unsupported    | stable         |

The table above is the truth source for public LLVM support. The public matrix
now has no `partial` or `supported (external)` rows. Each row is either
`stable` with authoritative proof or `unsupported` with deterministic
diagnostics. `rust-llvm` remains a bootstrap-only seed path and is not part of
this public matrix.

## Verification Checklist

- [x] Backend selection no longer depends on scattered shell assumptions
- [x] Windows no longer relies on Unix-only `command -v` logic
- [x] Version compatibility checks exist in one module
- [x] Every target has toolchain descriptor with install hints
- [x] Hosted x86_64 rows have compile/link proof, not just capability probes
- [x] Promoted CLI cross-target rows (`aarch64`, `riscv64`, `wasm32`, `wasm64`) have real artifact/link proof
- [x] Support claims map to specific test files
- [x] GPU codegen is explicitly out of scope
- [x] README can point to one source-of-truth support matrix
