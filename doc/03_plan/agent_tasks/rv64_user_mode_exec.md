# RV64 User-Mode Exec — Agent Tasks

**Feature:** `rv64_user_mode_exec`  
**Date:** 2026-04-02

## Parallel Team Split

### Team A: RV64 trap entry and return

- Own the real `_rv64_trap_vector` implementation, trap-frame shape, and `sret` return path.
- Consume the existing trap-model contract instead of redefining syscall or scheduler policy.

### Team B: RV64 syscall runtime

- Own the runtime marshalling between the saved trap frame and `syscall_handler(...)`.
- Preserve `a7`/`a0`-`a5` input and `a0` result conventions.

### Team C: Scheduler and user-context handoff

- Own RV64-specific user task context creation and restore semantics.
- Preserve `spawn_binary(path, priority)` and `create_user_task(...)` as the stable external handoff.

### Team D: Proof binary and launch path

- Own the first real RV64 proof executable and the path-based launch target under `/sys/services/*` or `/sys/apps/*`.
- Keep the executable source transitional if needed, but do not bypass the launch ABI.

### Team E: Proof matrix and doc alignment

- Own unit/QEMU proof updates and the doc/report language around the blocker.
- Keep Linux, repo-native simulator, RTL/VHDL, and GUI work classified as downstream dependencies until the blocker proof is complete.

## Coordination Rules

- Team A defines the trap-frame contract.
- Team B consumes that contract and owns syscall runtime only.
- Team C must not invent a separate user launch path.
- Team D must launch only through the existing path-based API.
- Team E updates proof claims only after the runtime contract is agreed.
