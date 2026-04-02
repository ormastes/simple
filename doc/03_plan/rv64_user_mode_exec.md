<!-- codex-design -->
# RV64 User-Mode Exec — Plan

**Date:** 2026-04-02  
**Status:** Draft  
**Requirement:** [rv64_user_mode_exec](../02_requirements/feature/rv64_user_mode_exec.md)

## Objective

Complete the blocking runtime milestone for the RISC-V program:

- one ELF-backed RV64 task launches through the existing path-based ABI
- the task enters U-mode
- user `ecall` reaches kernel syscall dispatch
- the kernel returns to userspace and the task exits cleanly

This plan also records the dependency chain to Linux boot, repo-native simulation, RTL/VHDL generation, and GUI OS bring-up without treating those as current-slice deliverables.

## Workstreams

### W1: RV64 trap entry and return

- Replace the placeholder `_rv64_trap_vector` path with a real trap entry that saves an RV64 trap frame, invokes the Simple-level dispatcher, and returns with `sret`.
- Ensure `SPP`, `SPIE`, and `sepc` are restored according to user-vs-kernel task type.
- Treat unsupported trap causes as explicit fatal paths with deterministic logging.

### W2: RV64 syscall runtime path

- Keep the current syscall ABI shape already modeled in the repo: `a7` for ID, `a0`-`a5` for args, `a0` for result.
- Wire the trap frame to `syscall_handler(...)`.
- Advance `sepc` after handled user `ecall`.

### W3: Scheduler and user-task handoff

- Keep `spawn_binary(path, priority)` and `create_user_task(...)` stable.
- Replace the current transitional scheduler/context behavior with RV64-specific user-context creation and restore semantics.
- Preserve the existing kernel-task path; do not invent a second public launch API.

### W4: First proof binary

- Keep the current path namespace under `/sys/services/*` or `/sys/apps/*`.
- Replace the inert staged executable proof with one minimal RV64 static ELF that performs output, optional `GetPid`, and `Exit`.
- Keep the executable source transitional if necessary, but hold the public path contract stable.

### W5: Downstream staging, not execution

- RV32 parity starts only after W1-W4 are green.
- Linux boot remains blocked until true userspace execution is real and the machine handoff is stable.
- Repo-native simulator remains blocked behind stable runtime and machine-profile contracts.
- GUI OS and RTL/VHDL end-state work remain downstream of simulator and machine-contract completion.

## Recommended Delivery Order

1. Trap entry/return and syscall runtime.
2. Scheduler/context handoff for true user tasks.
3. First proof binary and QEMU proof.
4. RV32 carryover.
5. Linux/simulator/RTL/GUI downstream phases after blocker completion.

## Risks

- Leaving the trap vector unimplemented would keep the repo stuck at policy-only user-mode modeling.
- Mixing Linux or simulator execution work into this blocker slice would blur proof boundaries and slow completion.
- Replacing the public launch ABI during blocker work would destabilize later RV32, VFS, and simulator phases.
