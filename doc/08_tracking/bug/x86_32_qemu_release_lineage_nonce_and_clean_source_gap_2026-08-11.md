# x86_32 QEMU Release Lineage, Nonce, and Clean-Source Gap

**Date:** 2026-08-11  
**Status:** OPEN  
**Acceptance criteria:** AC-4 through AC-7, AC-14

## Diagnostic result

Linux QEMU boots the x86_32 multiboot kernel with a FAT32 initrd, enumerates
ten real `/SYS/APPS` entries, loads an ELF32 program from that filesystem,
executes its mapped entry, captures `hello from x86_32 filesystem program`
from target UART, observes return zero, and prints `TEST PASSED`. QEMU exit 1
is the expected `isa-debug-exit` success encoding.

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_32/20260811T090000Z/evidence.env
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_32/20260811T090000Z/serial.log
```

The previous lane merely scanned raw initrd bytes and returned synthetic PIDs
through a test `int 0x80` dispatcher. It now parses FAT32 directory and cluster
chains and calls the loaded program entry before emitting the compatibility
execution marker.

## Release blockers and resume

The kernel was cross-built by the Rust bootstrap seed from a shared dirty
worktree, and the serial protocol lacks per-run nonce correlation. Deploy an
admitted pure-Simple Stage 4 CLI, isolate clean source, rebuild kernel/media,
inject the nonce into media and expected output, and run the canonical row
once. Retain all source/compiler/kernel/image/QEMU/argv/nonce identities.

- Owner: x86_32 SimpleOS execution lane
- Final reviewer: independent normal/highest-capability reviewer
