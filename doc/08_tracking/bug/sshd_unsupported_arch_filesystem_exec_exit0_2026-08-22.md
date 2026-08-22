# SSHD unsupported-architecture filesystem exec returned success

Status: FIXED IN SOURCE (2026-08-22); target execution remains unverified

## Problem

The x86_32, ARM64, ARM32, and RISC-V 32 target variants of the deferred SSH
filesystem-exec launcher returned `0` without resolving, loading, or executing
the requested program. The SSH channel therefore emitted a successful exit
status for an unsupported capability.

## Fix and contract

`ssh_exec_status_contract.spl` owns the architecture-neutral fail-closed
result. Unsupported launchers return the deterministic bounded result
`([], 126, false)`. Exit `127` remains reserved for a real PATH/name miss on implemented
x86_64 and RISC-V 64 paths. Those working launch paths and their stdout/API
contracts are unchanged.

The focused production contract spec calls the result owner directly and pins
all four target branches to it while retaining the x86_64 and RISC-V 64 spawn
bindings. This is source/interpreter contract evidence, not QEMU or target-
native filesystem-exec evidence. Live target proof still requires an admitted
self-hosted runtime and the corresponding launcher implementation.
