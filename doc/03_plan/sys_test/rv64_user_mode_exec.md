# RV64 User-Mode Exec — System Test Plan

**Feature:** `rv64_user_mode_exec`  
**Date:** 2026-04-02

## Coverage Matrix

### Unit-level blocker proof

- trap classification for timer, external interrupt, software interrupt, user `ecall`, and unsupported causes
- initial kernel-vs-user `sstatus` setup
- syscall register marshalling and result write-back
- executable and launch-path failure behavior

### QEMU oracle proof

- boot `simple-rv64` through the current QEMU-backed machine profile
- launch one ELF-backed userspace task through `spawn_binary(path, priority)`
- confirm the task reaches user mode, performs one visible syscall, and exits cleanly
- confirm invalid executables and unsupported trap causes fail deterministically

### Explicitly deferred proof

- RV32 true user-mode execution
- RV64 Linux boot
- repo-native simulator execution
- GUI OS running on the repo-native simulator
- generated RTL/VHDL full-system execution proof

## Test Assertions

- The blocker proof must name QEMU as the oracle backend.
- No test description may claim repo-native simulator completion.
- No test description may claim Linux or GUI RISC-V completion before those milestones have dedicated proofs.
