# Feature expert: SimpleOS server execution matrix

## Canonical artifacts

- State: `.spipe/simpleos_server_execution_matrix/state.md`
- Requirements: `doc/02_requirements/feature/simpleos_server_execution_matrix.md`
- Architecture/design: `doc/04_architecture/simpleos_server_execution_matrix.md`
  and `doc/05_design/simpleos_server_execution_matrix.md`
- Plan: `doc/03_plan/agent_tasks/simpleos_server_execution_matrix.md`
- Guide: `doc/07_guide/platform/simpleos/simpleos_server_execution_matrix.md`

## Truth contract

The three target modes are `qemu-arm64-cpu`, `unoq-cpu`, and `unoq-gpu` and
share `SimpleOsServerExecutionReceiptV1`. A credited row launches current-source
server bytes through the target filesystem, proves public HTTP/DB behavior, and
binds source, image/executable, target, command and transcript identities.

Never substitute x86, a marker ELF, a host process, Debian userspace, a Rust
seed, or a source-shape check. TCG proves correctness only. Physical UNO Q
evidence requires the SimpleOS boot/download path plus serial/SSH transcript.

Mutable web, DB and filesystem state has one parent owner. Optional device work
receives copied/frozen or generation-bound input and returns a bounded encoded
receipt for validation and deterministic commit; raw pointers and GPU mutation
of canonical state are forbidden.

## Current implementation order

1. ARM64 virtio-net/TCP and EL0 network/file syscall marshaling.
2. ARM64 filesystem-resolved server ELF and durable FAT32 DB state.
3. Physical QRB2210 SimpleOS build/boot plus safe filesystem deployment.
4. Separate CPU-only and Adreno/Vulkan submit/fence/readback receipts.
5. Linux comparison only after public protocols are correct and runnable.

Unavailable rows remain open with exact resume commands and Todo ownership.
