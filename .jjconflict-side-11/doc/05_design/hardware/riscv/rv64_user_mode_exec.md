# RV64 User-Mode Exec — Detail Design

**Date:** 2026-04-02  
**Requirement:** [rv64_user_mode_exec](../02_requirements/feature/rv64_user_mode_exec.md)

## Control Flow

1. init or another kernel service calls `spawn_binary(path, priority)`
2. kernel launch code resolves executable bytes and builds `UserProcessImage`
3. scheduler creates a user task with RV64 U-mode return state
4. restored task begins executing the ELF entry in U-mode
5. user code executes `ecall`
6. `_rv64_trap_vector` saves a trap frame and transfers control to the Simple-level RV64 dispatcher
7. dispatcher classifies the trap:
   - timer interrupt
   - external interrupt
   - software interrupt
   - user `ecall`
   - unsupported trap
8. for user `ecall`, dispatcher builds `SyscallArgs` from:
   - `a7` -> syscall ID
   - `a0`-`a5` -> args
9. `syscall_handler(...)` returns `SyscallResult`
10. dispatcher writes:
   - `a0 = result`
   - `sepc = sepc + 4`
11. trap return restores the updated frame and executes `sret`

## Trap-Frame Contract

The runtime handoff must preserve:

- integer registers needed for syscall and resume
- `sepc`
- `sstatus`
- `scause`

The runtime must assume:

- `SPP=0` for user return
- `SPIE` is set so interrupts restore correctly after `sret`
- unsupported trap causes are fatal for this milestone unless already handled as timer, external, or software interrupts

## User Task Creation

- `create_user_task(...)` remains the scheduler entrypoint for user tasks.
- the RV64 user-task path must create true U-mode return state, not just mirror entry/stack into generic context fields.
- the launch contract remains path-based and stable even while executable bytes are still boot-packaged.

## First Proof Binary

Use one minimal static RV64 ELF bound to an existing `/sys/services/*` or `/sys/apps/*` path.

Required behavior:

- execute in U-mode
- perform one visible output syscall
- optionally perform `GetPid`
- call `Exit`

This binary is the only required end-to-end proof artifact for the milestone.

## Failure Modes

- invalid path or invalid executable -> explicit launch failure
- unsupported trap cause -> explicit fatal runtime path
- unknown syscall ID -> explicit syscall error return
- kernel/scheduler path must not silently downgrade user launch to kernel-mode execution

## Deferred Design

- RV32 true user-mode carryover
- VFS-backed executable bytes
- Linux kernel boot handoff
- repo-native simulator machine/device model
- GUI OS launch on the repo-native simulator
- generated RTL/VHDL full-system path
