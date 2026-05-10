# VHDL Backend And GHDL RV32 Remote Verification

**Date:** 2026-03-31  
**Scope:** VHDL backend fail-fast completion, MIR-backed package/process emission, and GHDL RV32 remote-interpreter composite routing.  
**Status:** PASS

## Summary

This scope is verified for the implemented slice:

- the VHDL backend now fails explicitly on unsupported MIR instead of silently emitting placeholder comments
- package and process emission are wired through live MIR-backed backend paths
- the composite remote runner recognizes `interpreter(remote(baremetal(ghdl(riscv32))))` and can execute checked-in ELF artifacts through the GHDL semihost runner
- system and feature specs now assert the real parser and routing behavior instead of stale TODO placeholders

The original plan remains only partially complete overall. The mailbox-backed simulated remote interpreter lane and the Simple-defined RV32 hardware flow are still open.

## Current blocker note

This report remains valid for the verified VHDL/GHDL slice it covers. It is not the current runtime blocker report for the larger RISC-V program.

Current blocker documentation now lives in:

- `doc/01_research/local/rv64_user_mode_exec.md`
- `doc/01_research/domain/rv64_user_mode_exec.md`
- `doc/02_requirements/feature/rv64_user_mode_exec.md`
- `doc/03_plan/rv64_user_mode_exec.md`

Those documents describe the active blocker for true RV64 user-mode execution and its downstream dependency chain to Linux, repo-native simulation, RTL/VHDL end-state work, and GUI OS bring-up.

## Files Verified

- [vhdl_backend.spl](src/compiler/70.backend/backend/vhdl_backend.spl)
- [test_executor_composite.spl](src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl)
- [__init__.spl](src/lib/nogc_sync_mut/test_runner/__init__.spl)
- [vhdl_backend_spec.spl](test/unit/compiler/backend/vhdl_backend_spec.spl)
- [remote_interpreter_backend_spec.spl](test/system/remote_interpreter_backend_spec.spl)
- [multi_mode_test_runner_spec.spl](test/system/multi_mode_test_runner_spec.spl)
- [remote_baremetal_qemu_hello_spec.spl](test/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl)

## Verification Evidence

Build and lint:

- `bin/simple build lint`
- Result: passed for the current tree; existing repo-wide Rust/clippy warnings remain outside this feature slice

Focused tests:

- `bin/simple test test/unit/compiler/backend/vhdl_backend_spec.spl`
- `bin/simple test test/system/remote_interpreter_backend_spec.spl`
- `bin/simple test test/system/multi_mode_test_runner_spec.spl`
- `bin/simple test test/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl`
- `bin/simple test test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
- `bin/simple test test/feature/baremetal/ghdl_riscv32_semihost_spec.spl`
- `bin/simple test test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl`
- `bin/simple test test/integration/remote_jit/qemu_rv32_composite_runner_spec.spl`

Broader suites:

- `bin/simple test test/feature/app/remote_baremetal/`
- `bin/simple test test/integration/remote_jit/`
- `bin/simple test test/unit/compiler/backend/`

Stub audit:

- scanned the touched implementation and spec files for `pass_todo`, `pass_do_nothing`, `pass_dn`, `TODO`, and `FIXME`
- result: no stub markers in the touched VHDL backend and remote-interpreter files

## Findings

- No failures were found in the implemented VHDL backend slice or the GHDL RV32 composite-routing slice.
- The current GHDL proof is a semihosted ELF execution lane, not the mailbox-based `riscv32_sim_vhdl` remote-interpreter design from the plan.
- The plan document was stale before this verification pass and has been updated to distinguish completed Phase 1 work from later hardware/mailbox phases.

## Gate

STATUS: PASS
