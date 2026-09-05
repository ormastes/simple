# ARM32 QEMU Release Lineage and Nonce Gap

**Date:** 2026-08-11  
**Status:** OPEN  
**Acceptance criteria:** AC-4 through AC-7, AC-14

## Diagnostic result

Linux QEMU now boots the canonical ARM32 descriptor, mounts the FAT32 image,
enumerates ten real `/SYS/APPS` directory entries, loads an ARM ELF from that
filesystem, executes its mapped entry, captures
`hello from arm32 filesystem program` from target UART, observes return zero,
and exits QEMU with status zero. The retained transcript and receipt are:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/arm32/20260811T074500Z/serial.log
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/arm32/20260811T074500Z/evidence.env
```

The semihosting success path in
`examples/09_embedded/simple_os/arch/arm32/boot/baremetal_stubs.c` now supplies
the ARM `ADP_Stopped_ApplicationExit` reason (`0x20026`), so a passing guest no
longer produces host exit status 1.

## Why this is not release PASS

The kernel was cross-built with
`src/compiler_rust/target/release/simple`, whose own version output identifies
it as a bootstrap seed. The transcript also predates the required per-run nonce
correlation. Those two provenance gaps prevent promotion to production or
release evidence even though the guest behavior itself is complete.

## Unblock condition

Deploy an admitted pure-Simple Stage 4 CLI, rebuild the ARM32 kernel and image
from that compiler lineage, inject one run nonce into the media and expected
serial contract, and execute the canonical ARM32 row once. Retain compiler,
kernel, image, QEMU, argv, nonce, transcript, and exit hashes in the evidence
bundle.

## Ownership

- Owner: ARM32 SimpleOS execution lane
- Final reviewer: independent normal/highest-capability reviewer
