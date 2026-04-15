<!-- codex-research -->
# RV64 User-Mode Exec — Local Research

**Feature:** `rv64_user_mode_exec`  
**Date:** 2026-04-02  
**Status:** Draft

## Scope

This note records the current repo truth for the blocking RISC-V milestone:

- real ELF-backed userspace launch on `simple-rv64`
- real RV64 user-mode trap entry, `ecall`, return, and exit
- explicit dependency links from that blocker to RV32 parity, Linux boot, repo-native simulation, RTL/VHDL generation, and GUI OS bring-up

It does not claim those downstream milestones are implemented today.

## Findings

### 1. The launch ABI exists, but execution is still transitional

- `src/os/userlib/process.spl` exposes `spawn_binary(path, priority)`.
- `src/os/services/init/init_service.spl` already uses that path-based launch ABI instead of `spawn(0, ...)`.
- `src/os/kernel/ipc/syscall.spl` resolves path bytes, loads boot-packaged executable bytes, builds a `UserProcessImage`, and calls `create_user_task(...)`.
- `src/os/kernel/loader/executable_source.spl`, `elf_loader.spl`, and `process_image.spl` now form a real path-to-image pipeline.

Current limitation:
- the executable source is still boot-packaged bytes, not VFS-backed file loading
- the scheduler handoff is still transitional and not yet a proven U-mode runtime

### 2. RV64 ELF validation and process-image construction are present

- `src/os/kernel/loader/elf_loader.spl` validates static RISC-V ELF32/ELF64 `ET_EXEC` images with `PT_LOAD` segments only.
- `src/os/kernel/loader/process_image.spl` converts validated ELF data into `UserProcessImage` with entry point, loadable segments, and stack metadata.
- `src/os/kernel/types/task_types.spl` now carries `UserLoadSegment` and `UserProcessImage`.

Current limitation:
- image construction is not yet followed by proven memory mapping and true U-mode restore
- the byte source is a staging mechanism, not a final userspace filesystem-backed exec path

### 3. The RV64 scheduler path marks user tasks, but does not yet prove real user execution

- `src/os/kernel/scheduler/scheduler.spl` has `create_user_task(...)`.
- the `TaskControlBlock` now distinguishes `is_user`, `entry_point`, `user_stack`, and `address_space`.
- the current implementation still mirrors user launch state through the generic `TaskContext` used by the scheduler.

Current limitation:
- this is enough for a launch contract and unit coverage
- it is not yet enough to prove the CPU enters RV64 U-mode and returns via trap handling

### 4. RV64 trap/runtime policy is now partially modeled, but not wired through a real trap vector

- `src/os/kernel/arch/riscv64/trap_model.spl` now models:
  - kernel vs user initial `sstatus`
  - trap classification
  - syscall register marshalling
  - `ecall` result application and `sepc` advance
- `src/os/kernel/arch/riscv64/interrupt.spl` has `rv64_dispatch_trap(...)` that routes timer, external interrupt, software interrupt, and user `ecall` at the policy level.
- `src/os/kernel/arch/riscv64/context.spl` now exposes an explicit `create_user(...)` path.

Current limitation:
- `_rv64_trap_vector` is still an extern placeholder
- there is no repo-proven assembly trap frame save/restore path connected to `rv64_dispatch_trap(...)`
- there is no proven `sret` return path back to a running user ELF

### 5. RV32 is behind RV64 for this milestone

- `src/os/kernel/arch/riscv32` has boot, SBI, timer, interrupt, paging, and context scaffolding.
- the RV32 context switch file still contains `pass_todo` for the real switch/save/restore path.

Conclusion:
- RV32 should remain follow-on work after RV64 user-mode execution is real
- the repo should not claim user-mode parity across RV64 and RV32 today

### 6. QEMU is still the only authoritative OS execution oracle

- `src/os/machine_profile.spl` defines `simple-rv64` and `simple-rv32`.
- `src/app/sim/main.spl` and `src/app/sim/profile.spl` provide a source-level simulator CLI surface.
- `src/os/qemu_runner.spl` is still the real execution backend behind current OS proof lanes.
- `test/qemu/os/boot/riscv64_boot_qemu_spec.spl` and `test/qemu/os/boot/riscv32_boot_qemu_spec.spl` are the current boot smoke proofs.

Current limitation:
- `simple sim` is an oracle wrapper, not a repo-native system simulator
- no repo-native fast/lockstep simulator exists yet

### 7. Linux boot and GUI OS remain downstream of the RV64 user-mode blocker

- there is no current repo-native RV64 Linux boot proof in the OS tree
- no current repo-native simulator exists to host that Linux target
- the desktop/compositor/apps tree exists, but there is no proven RV64 GUI-OS-on-RISC-V execution lane through a repo-native simulator

Dependency truth:
- true RV64 user-mode exec is a prerequisite for credible userspace, init, and later Linux/simulator work
- Linux boot, simulator work, and GUI bring-up should not be treated as parallel completion claims for the current blocker

## Current Proof Matrix

| Area | Current state |
|---|---|
| RV64 ELF validation | implemented |
| RV64 path-based launch ABI | implemented |
| RV64 user task metadata | implemented |
| RV64 U-mode entry/return | not yet proven |
| RV64 user `ecall` end-to-end | policy modeled, runtime wiring incomplete |
| RV32 user-mode parity | not ready |
| Repo-native simulator | not implemented |
| RV64 Linux boot | not implemented |
| GUI OS on RISC-V simulator | not implemented |
| VHDL/RTL generated full RISC-V system | not implemented |

## Conclusion

The current blocking milestone is precise:

- keep `spawn_binary(path, priority)` as the stable launch ABI
- finish the real RV64 trap/runtime path so one ELF-backed task runs in U-mode, performs `ecall`, returns, and exits
- only after that should the repo treat RV32 parity, Linux boot, repo-native simulation, RTL/VHDL generation, or GUI OS-on-simulator as active downstream milestones
