# ARM32 QEMU Release Lineage and Nonce Gap
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## 2026-11-11 addendum — P3 traverse lane ne1 verdict: BLOCKED (OPEN)

No newer ARM32 evidence found at the `origin/release/1.0.0` tip: no
nonce-correlated 2026-09+ ARM32 transcript/receipt in `doc/09_report/` or
`doc/08_tracking/evidence/`, and the bug_db row remains `open`
(triage-20261027-v4: validity=valid, action=keep_open). The two provenance
gaps named in this doc therefore stand: the 2026-08-11 transcript predates
per-run nonce correlation, and its kernel was cross-built from the Rust seed
lineage, not an admitted pure-Simple Stage 4 compiler.

This Windows lane host has no `qemu-system-arm`, so the unblock condition
cannot be executed here. Exact grant command (Linux/QEMU host, admitted
pure-Simple Stage 4 CLI selected as the build compiler):

```sh
sh scripts/check/check-arm32-qemu-real-exec-markers.shs   # expects: SIMPLEOS_FS_EXEC_OK arch=arm32 nonce=<run-nonce>
```

Retain compiler, kernel, image, QEMU, argv, nonce, transcript, and exit
hashes per this doc's unblock condition. Status stays OPEN. Lane evidence:
`build/review/p3fix-ne1-20261111.sdn` row 4.
