# Workaround: f27 manual continuation of 10 modules via riscv_formal overlay

- **Date:** 2026-11-22
- **Updated:** 2026-11-27
- **Status:** fix-implemented-verification-pending
- **Severity:** P2

## Symptom

In Phase 3 build f27, 10 modules had to be compiled manually. `src/os/_QemuRunner/os_build_run.spl` failed HIR because its source base lacked fix a679b749ff6, which changes `src/lib/hardware/riscv_common/core/riscv_formal.spl`. 8 dependents cascaded, including `main_and_help`.

## Workaround

The manual continuation uses an overlay with release's fixed `riscv_formal.spl`.

## Removal condition

Remove the overlay when the Phase 3 to Phase 3 self-build runs from a base containing a679b749ff6 and the residual split-brain import and `pub` visibility fixes.

## Root Cause & Fix (2026-11-27)

`a679b749ff6` (and follow-up `0b8f0f43060`) landed the core `verify_rv64_qemu_user_proof_contract` helper in `src/lib/hardware/riscv_common/core/riscv_formal.spl` and `verify_qemu_formal_output` in `src/os/_QemuRunner/os_build_run.spl`, without any in-tree overlay script or `@workaround` annotation remaining, but left three residual defects:

1. **Split-brain bare `hardware.riscv_common.core.riscv_formal` imports:** Full checkouts resolve `use hardware.riscv_common.core.riscv_formal` to `src/hardware/riscv_common/core/riscv_formal.spl` (which imports `compiler.backend.vhdl_constraints`), whereas sparse checkouts and native-build snapshots (`src/{app,lib,compiler,os,plugins}`) resolve it to `src/lib/hardware/riscv_common/core/riscv_formal.spl`. Updated `src/os/_QemuRunner/os_build_run.spl`, `src/os/qemu_runner_part2.spl`, `src/lib/nogc_sync_mut/debug/remote/exec/adapter_ghdl_rv32.spl`, and `src/lib/nogc_async_mut/debug/remote/exec/adapter_ghdl_rv32.spl` to use `std.hardware.riscv_common.core.riscv_formal`.
2. **Unused bare imports:** Removed unused `use hardware.riscv_common.core.riscv_formal.{verify_rv64_qemu_user_proof_contract}` from `src/os/_QemuRunner/runner_targets.spl`, `src/os/_QemuRunner/scenario_catalog.spl`, `src/os/_QemuRunner/scenario_disks.spl`, and `src/os/_QemuRunner/scenario_exec.spl`.
3. **Missing `pub` visibility and baseline debt:** Marked `render_retire_chain_report`, `verify_rv32_default_vhdl_constraints`, `verify_rv32_ghdl_return_zero_contract`, `verify_rv64_qemu_user_proof_contract`, and `probe_riscv_external_formal` as `pub fn` in `src/lib/hardware/riscv_common/core/riscv_formal.spl`, marked `verify_qemu_formal_output` as `pub fn` in `src/os/_QemuRunner/os_build_run.spl` and `src/os/qemu_runner_part2.spl`, and removed the corresponding 5 resolved rows from `scripts/check/private_import_baseline.txt`.

## Regression Coverage

- `test/01_unit/hardware/riscv_common/riscv_formal_lib_overlay_spec.spl`: verifies `verify_rv64_qemu_user_proof_contract` (positive + all 7 missing-marker failure paths), `check_retire_chain` / `render_retire_chain_report`, `pub fn` visibility declarations, canonical `std.hardware.riscv_common.core.riscv_formal` imports, and absence of bare `hardware.riscv_common` imports across all 8 consumers.
- `test/01_unit/os/riscv_formal_overlay_regression_spec.spl`: verifies `verify_qemu_formal_output` delegation through `os.qemu_runner` and `os._QemuRunner.os_build_run` across `Riscv64` (pass/fail) and `X86_64`/`Riscv32` without external QEMU execution.

## Verification & Pending Evidence

- `C:\dev\simple\bin\simple.exe run` direct check against `std.hardware.riscv_common.core.riscv_formal` (with `SIMPLE_LIB=<worktree>\src`): `SEED_RUN_PASS` (`RUN_EXIT=0`) covering all 6 `pub fn` imports, `verify_rv64_qemu_user_proof_contract` pass/failure cases, `check_retire_chain`, and `render_retire_chain_report`.
- `C:\dev\simple\bin\simple.exe test ... --mode=interpreter` on both new specs exited `1` (`outcome=ERROR`, `declared>=5`/`>=3`, `executed=0`) because `C:\dev\simple\bin\simple.exe` is a 2026-11-19 bootstrap seed (`f3e12b05d390532d6f3b69254069525009492156`) that predates `@representation_boundary` in `src/lib/nogc_sync_mut/io/file_bytes.spl` pulled transitively by `std.spec`; `C:\dev\simple\bin\release\x86_64-pc-windows-msvc\simple.exe` is absent on this host; `simple.exe check` exited `1`; `simple_stage3_srfix5.exe` hit `cold-hir-module-source-mismatch` on `native-build` and stalled in `compile`.
- `sh scripts/audit/direct-env-runtime-guard.shs --working`: `STATUS: PASS`.
- **Pending:** Run both regression specs on a current post-`b44e00caabd` self-hosted compiler/runtime and complete a clean Phase 3-to-Phase-3 bootstrap/RV64 verification pass from a base containing these commits before transitioning to `fixed`.

## Related

f28's failure (`runtime_c_compile_pool_v1.spl` importing `cpu_count_checked` from `std.io_runtime`, introduced by e0aea49c8e9) is already fixed by #10777 (5d5c17bf4e0); no new row.
