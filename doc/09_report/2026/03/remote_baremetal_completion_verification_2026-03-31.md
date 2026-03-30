# Remote Baremetal Completion Verification

**Date:** 2026-03-31  
**Scope:** CH32 composite-runner completion, RV32 raw injected regression lane, and remote baremetal/JIT wording cleanup.  
**Status:** PASS

## Summary

Repo-side remote baremetal completion work is verified for the implemented scope:

- CH32V307 composite JIT execution is now wired through a real `wlink` adapter
- the old CH32 "not implemented" composite-runner placeholder is removed
- RV32 raw injected execution is covered by a dedicated regression lane and kept separate from the stable ELF proof
- docs and spec wording now match the implemented lane split

## Files Verified

- [adapter_ch32v307.spl](/home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/debug/remote/exec/adapter_ch32v307.spl)
- [test_executor_composite_jit_generic.spl](/home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/test_runner/test_executor_composite_jit_generic.spl)
- [ch32v307_adapter_spec.spl](/home/ormastes/dev/pub/simple/test/unit/lib/remote_exec/ch32v307_adapter_spec.spl)
- [ch32v307_composite_runner_path_spec.spl](/home/ormastes/dev/pub/simple/test/integration/remote_jit/ch32v307_composite_runner_path_spec.spl)
- [qemu_rv32_raw_injected_regression_spec.spl](/home/ormastes/dev/pub/simple/test/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl)
- [remote_baremetal_remaining_without_trace32_2026-03-24.md](/home/ormastes/dev/pub/simple/doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)
- [remote_baremetal_runtime_spec.md](/home/ormastes/dev/pub/simple/doc/06_spec/remote_baremetal_runtime_spec.md)

## Verification Evidence

Build and lint:

- `bin/simple build lint`
- Result: passed for the current tree; existing upstream warnings remain outside this feature slice

Targeted tests:

- `bin/simple test test/unit/lib/remote_exec/ch32v307_adapter_spec.spl`
- `bin/simple test test/unit/lib/remote_exec/remote_exec_host_spec.spl`
- `bin/simple test test/integration/remote_jit/ch32v307_composite_runner_path_spec.spl`
- `bin/simple test test/integration/remote_jit/ch32v307_composite_runner_spec.spl`
- `bin/simple test test/feature/app/remote_jit/ch32v307_jit_e2e_spec.spl`
- `bin/simple test test/integration/remote_jit/qemu_rv32_composite_runner_spec.spl`
- `bin/simple test test/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl`
- `bin/simple test test/feature/app/remote_jit/qemu_rv32_jit_e2e_spec.spl`
- `bin/simple test test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
- `bin/simple test test/integration/remote_jit/baremetal_library_host_spec.spl`
- `bin/simple test test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl`

Live host checks:

- `wlink status --chip CH32V30X` detected a connected `CH32V307VCT6`
- a one-off live probe spec executed `run_test_file_jit_ch32v307(...)` successfully on this host
- `qemu-system-riscv32` and `gdb-multiarch` are installed on this host

Stub audit:

- scanned touched implementation and spec files for `pass_todo`, `pass_do_nothing`, `pass_dn`, `TODO`, and `FIXME`
- result: no stub markers found in the touched feature files

## Findings

- No feature-scope failures were found after implementation.
- The test runner still caches unchanged specs aggressively, so a temporary external spec was used to prove the live CH32 composite path without relying on cached results.
- `doc/06_spec/remote_baremetal_runtime_spec.md` is generated-style documentation but was updated manually here to keep references aligned until the next docgen refresh.

## Gate

STATUS: PASS
