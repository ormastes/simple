<!-- codex-design -->
# RV64 User-Mode Exec — Architecture

**Date:** 2026-04-02  
**Requirement:** [rv64_user_mode_exec](../02_requirements/feature/rv64_user_mode_exec.md)

## Architecture Summary

This feature completes the missing runtime bridge between the existing ELF launch pipeline and real RV64 user-mode execution.

The architecture remains intentionally narrow:

1. executable bytes become a validated `UserProcessImage`
2. scheduler creates a user task from that image
3. `_rv64_trap_vector` is the only machine entrypoint for supervisor traps
4. the trap stub saves/restores the trap frame and returns with `sret`
5. Simple-level runtime code classifies traps and dispatches syscalls

QEMU remains the oracle backend for this milestone.

## Runtime Layers

### Launch and image layer

- `spawn_binary(path, priority)` remains the only public userspace launch ABI.
- kernel launch code resolves bytes, validates ELF, and builds `UserProcessImage`.
- this layer prepares entry, stack, and segment metadata only; it does not own trap semantics.

### Task representation layer

- scheduler owns task identity, readiness, parentage, and user-vs-kernel task classification.
- task state must carry enough information to resume a user task through RV64 user return semantics.
- scheduler policy must not redefine syscall ABI or trap classification.

### RV64 trap/runtime layer

- `_rv64_trap_vector` is the single supervisor trap entrypoint in scope.
- architecture code owns trap-frame save/restore and `sret`.
- `rv64_dispatch_trap(...)` owns trap classification and syscall/interrupt policy.
- the runtime boundary is one saved RV64 trap frame: GPR state plus `sepc`, `sstatus`, and `scause`.

### Oracle proof layer

- `simple-rv64` under QEMU is the execution oracle.
- current proof target is one real userspace task, not Linux boot, repo-native simulation, or GUI bring-up.

## Design Rules

- Do not add a second userspace launch API.
- Do not let scheduler metadata substitute for architectural return state; `sstatus` and `sepc` are part of the runtime contract.
- Keep the trap stub minimal and architecture-specific, and keep syscall semantics in Simple-level code.
- Keep Linux, repo-native simulation, RV32 parity, and RTL/VHDL system work downstream of this milestone.

## Consequences

- Later RV32 carryover can reuse the same layer split.
- Later VFS-backed exec can replace executable-byte sourcing without changing the runtime seam.
- Later Linux and simulator work can build on the same machine-profile and launch/runtime boundary instead of inventing a second boot/runtime stack.
