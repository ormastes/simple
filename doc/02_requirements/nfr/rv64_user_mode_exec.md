# RV64 User-Mode Exec — NFR Requirements

**Feature:** `rv64_user_mode_exec`  
**Date:** 2026-04-02  
**Status:** Draft  
**Related:** [Feature Requirements](../feature/rv64_user_mode_exec.md)

## Non-Functional Requirements

- **NFR-RV64-UME-001 Deterministic trap semantics**: RV64 trap handling must produce deterministic outcomes for supported interrupts, supported user `ecall`, and unsupported causes.
- **NFR-RV64-UME-002 No silent degradation**: unsupported executable features, unsupported trap causes, and unsupported syscall IDs must fail explicitly instead of degrading into no-op behavior.
- **NFR-RV64-UME-003 Stable ABI contract**: `a0`-`a5`, `a7`, `a0` return, `sepc` advance, and user-vs-kernel `sstatus` setup must remain stable and testable.
- **NFR-RV64-UME-004 Oracle-backed proof**: until a repo-native simulator exists, the proof lane for this milestone must remain QEMU-backed and named as such.
- **NFR-RV64-UME-005 Documentation truthfulness**: docs and reports must distinguish implemented blocker work from deferred Linux, simulator, RTL/VHDL, and GUI milestones.
- **NFR-RV64-UME-006 Forward-compatible interfaces**: the blocker implementation must preserve the existing public launch ABI and machine-profile direction so later VFS, RV32, Linux, and simulator work can build on it.

## Verification Strategy

- Unit tests for trap classification, syscall register marshalling, syscall result write-back, and initial `sstatus` setup.
- Unit or integration tests for launch-path rejection cases.
- QEMU RV64 smoke proving one ELF-backed user task reaches the real trap/runtime path.
- Doc review ensuring stale RV32/VHDL docs defer to this blocker package for current runtime truth.
