# x86_64 QEMU Release Lineage, Nonce, and Clean-Source Gap

**Date:** 2026-08-11  
**Status:** OPEN  
**Acceptance criteria:** AC-4 through AC-7, AC-14

## Diagnostic result

The Linux x86_64 QEMU row now boots through multiboot, mounts its NVMe FAT32
image, enumerates ten real `/SYS/APPS` entries, loads an x86_64 ELF from that
filesystem, executes its mapped entry, captures
`hello from x86_64 filesystem program` from target UART, observes return zero,
and prints `TEST PASSED`. QEMU exits 1 because `isa-debug-exit` encodes the
guest success value as `(value << 1) | 1`; the transcript, rather than ordinary
POSIX zero, is the canonical success classification for this descriptor.

Retained evidence:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_64/20260811T083000Z/serial.log
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_64/20260811T083000Z/evidence.env
```

The bring-up also repaired two owner defects: the documented 192 MiB
freestanding heap had drifted to 1 GiB and placed the boot stack outside the
512 MiB guest, and the canonical runner did not convert the emitted ELF64
container to the ELF32 multiboot container required by QEMU `-kernel`.

## Why this is not release PASS

The kernel was cross-built by the Rust bootstrap seed from a shared dirty
worktree, and the transcript lacks the required per-run nonce correlation.
Those facts block release qualification despite complete guest behavior.

## Unblock condition

Deploy an admitted pure-Simple Stage 4 CLI, isolate or clean the intentional
source lane, rebuild the kernel and image, inject a run nonce into media and
serial expectations, and run the canonical x86_64 row once. Retain the exact
source, compiler, kernel, image, QEMU, argv, accelerator, nonce, transcript,
and program receipt identities.

## Ownership

- Owner: x86_64 SimpleOS execution lane
- Final reviewer: independent normal/highest-capability reviewer
