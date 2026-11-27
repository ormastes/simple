# RISC-V 64 QEMU Release Lineage and Nonce Gap
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-11  
**Status:** OPEN  
**Acceptance criteria:** AC-7, AC-14

## Proven diagnostic behavior

Descriptor-identical Linux QEMU boots the canonical RV64 acceptance kernel and
shared-storage FAT32 image. The guest enumerates ten real `/SYS/APPS` entries,
loads an executable RV64 ELF from FAT32, executes its instructions, emits target
UART stdout, returns zero, and reaches `TEST PASSED`.

Evidence:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/riscv64/20260811T054000Z/
```

## Remaining release blockers

1. Cross-target compilation used the Rust bootstrap seed because the deployed
   pure-Simple compiler does not currently provide this target path.
2. The guest markers are not yet correlated with a per-run nonce supplied by
   the runner, so the strict receipt classifier cannot accept them.

The behavior is real but remains diagnostic until both facts are corrected and
the canonical system spec is run once through the deployed pure-Simple CLI.

## Ownership

- Owner: RISC-V64 SimpleOS execution lane
- Merge owner: SOSIX/QEMU integration lane
- Final reviewer: independent normal/highest-capability reviewer


## Verification 2026-11-05 (riscv-sweep lane, work/riscv-sweep-20261105)

Bookkeeping re-check only. Both release blockers stand: RV64 cross-compilation
still routes through the Rust seed (no deployed pure-Simple target path), and
the guest markers are not yet correlated with a per-run runner nonce, so the
strict receipt classifier still cannot accept them. No canonical system-spec
run through the deployed pure-Simple CLI exists. Status: OPEN (unchanged).

## 2026-11-11 — lane boot13 (work/p3-boot13-20261111)

Status: **BLOCKED** (host-limited) — remains OPEN; both release blockers stand at
guard level on this tip (c8b6d0ebe90e):

1. No canonical system-spec run through the deployed pure-Simple CLI exists.
   The fresh *seed* binary lists `riscv64` as a stable cranelift target
   (`bin/simple.exe targets`), but a seed target listing is bootstrap metadata,
   not the deployed pure-Simple RV64 target path this doc requires — and the
   canonical run itself needs QEMU RV64, which this Windows host does not have
   (`command -v qemu-system-riscv64` -> not found).
2. No per-run runner nonce correlation exists for the riscv64 line: the
   nonce-slot guards cover arm64 and x86-64 only
   (`scripts/check/check-arm64-qemu-nonce-slot.shs`,
   `scripts/check/check-x86-64-qemu-nonce-slot.shs`); there is no
   `check-riscv64-qemu-nonce-slot.shs`, so the strict receipt classifier still
   cannot accept riscv64 guest markers.

Exact grant (run on a Linux host with `qemu-system-riscv64`, OpenSBI + U-Boot
qemu-riscv64 packages, and the workspace-admitted deployed pure-Simple
`bin/release/<triple>/simple`):

```
sh scripts/check/check-linux-riscv64-bootstrap-qemu.shs --smoke
sh scripts/check/check-simpleos-riscv64-opensbi-guest-boot.shs
```

plus a riscv64 nonce-slot guard landed analogously to
`scripts/check/check-arm64-qemu-nonce-slot.shs`, and one canonical
`test/03_system` RV64 spec run through the deployed pure-Simple CLI with the
runner-supplied nonce correlated into the retained receipt.


---

## Lane disposition 2026-11-13 (p3-misc-b)

Not pursued in this lane: re-verified 2026-11-05: both blockers stand (seed cross-compile, no per-run nonce). Needs the QEMU/release-lineage lane on a Linux host with cargo.
---

## Lane disposition 2026-11-13 (live-p3-l4, work/live-p3-l4-20261113, base f790f7f266e)

Concurs with boot13/p3-misc-b: BLOCKED on this host — both release blockers stand at guard level (no canonical system-spec run through the deployed pure-Simple CLI; no riscv64 runner-nonce guard — only arm64/x86-64 nonce-slot guards exist), and this Windows lane has no `qemu-system-riscv64` (`command -v` empty). The exact grant (Linux host with QEMU RV64 + OpenSBI/U-Boot + workspace-admitted deployed CLI) is recorded in the boot13 addendum. No in-lane change. Owner: RISC-V64 SimpleOS execution lane + SOSIX/QEMU integration lane.
