# RV64 User-Mode Exec — Requirements

**Feature:** `rv64_user_mode_exec`  
**Date:** 2026-04-02  
**Status:** Draft  
**Related:** [Local Research](../../01_research/local/rv64_user_mode_exec.md), [Domain Research](../../01_research/domain/rv64_user_mode_exec.md)

## Motivation

The repo already has the outer launch contract for RISC-V userspace:

- path-based `spawn_binary(path, priority)`
- ELF validation and process-image construction
- user-task creation in the scheduler

The missing blocker is true RV64 user-mode execution:

- U-mode entry from an ELF-backed task
- `ecall` trap into the kernel
- return to user execution
- clean userspace exit

Everything else in the larger RISC-V program depends on that runtime milestone.

## In Scope

- **REQ-RV64-UME-001**: Keep `spawn_binary(path, priority)` as the only public userspace launch ABI for this milestone.
- **REQ-RV64-UME-002**: Launch at least one real static RV64 ELF-backed task from the existing path namespace.
- **REQ-RV64-UME-003**: The launched RV64 task must enter U-mode, not remain a scheduler-only pseudo-user task.
- **REQ-RV64-UME-004**: User `ecall` must reach kernel syscall dispatch using the standard RV64 register ABI shape already modeled in the repo.
- **REQ-RV64-UME-005**: Syscall return must restore user execution state, including `a0` result and advanced `sepc`.
- **REQ-RV64-UME-006**: The first proof binary must perform one visible syscall and then exit cleanly.
- **REQ-RV64-UME-007**: Unsupported trap causes and unsupported executable images must fail explicitly.
- **REQ-RV64-UME-008**: RV32 parity is follow-on work and must reuse the same launch and syscall design later.
- **REQ-RV64-UME-009**: Linux boot, repo-native simulation, VHDL/RTL generation, and GUI OS bring-up remain explicitly downstream of this blocker.

## Out of Scope

- Dynamic linking or shared-library userspace
- Full VFS-backed executable loading in this milestone
- RV32 true user-mode execution in the same slice
- RV64 Linux boot
- Repo-native simulator implementation
- Generated RV32/RV64 RTL or VHDL system completion
- GUI desktop bring-up on RISC-V

## Acceptance Criteria

1. `spawn_binary(path, priority)` still drives the only userspace launch ABI.
2. One RV64 ELF-backed task launches from a known `/sys/services/*` or `/sys/apps/*` path.
3. That task reaches U-mode and executes at least one `ecall`.
4. The kernel returns a syscall result to userspace and advances past the `ecall`.
5. The task exits cleanly and the kernel records completion deterministically.
6. Unknown trap causes and invalid executables return explicit failures.
7. Documentation keeps downstream Linux/simulator/RTL/GUI work explicit without claiming them complete.

## Dependencies

- `src/os/kernel/loader/*` for executable bytes, ELF parsing, and process-image construction
- `src/os/kernel/scheduler/scheduler.spl` for user-task creation and state
- `src/os/kernel/arch/riscv64/*` for trap entry, context creation, and return path
- `src/os/kernel/ipc/syscall.spl` for syscall dispatch

## Downstream Dependency Map

- **Next after this milestone**: RV32 carryover and VFS-backed executable source
- **Blocked on this milestone**: RV64 Linux userspace/runtime credibility
- **Blocked on Linux/runtime credibility**: repo-native simulator board/device contract
- **Blocked on simulator + machine contract**: GUI OS-on-simulator proof
- **Blocked on stable machine/runtime contract**: generated RV32/RV64 RTL and VHDL end-state proof
