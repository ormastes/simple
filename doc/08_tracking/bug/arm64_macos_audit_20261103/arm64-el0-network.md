# ARM64 EL0/network repair — 2026-11-03

Canonical bug: simpleos_arm64_el0_server_syscall_and_virtio_net_gap_2026-08-14. Claim: arm64-el0-net-20261103; parent owns DB. Applied debug/coding skills. Source base a1a892525d9; candidate 8fd1ecd6ec7 in /tmp/simple-arm64-net-ring-cursor-20261103. No heavy builds or QEMU system execution.

## Current source and actual defect

The shared syscall owner bypasses the historical ENOSYS helper and checks/copied user buffers; ARM64 C dispatch routes authorized requests to real direct socket exports when the NIC is ready. The modern VirtIO-MMIO transport and server boot entry are present. This does not prove their live acceptance.

A separate concrete transport bug remains in rt_arm64_virtio_net_send: selected descriptor slot is used as available-ring position. Ring publication must use producer avail.idx modulo8 while storing the independently selected descriptor ID. Timed-out send descriptors remain device-owned; subsequent slot reuse need not match producer position. The old sender's actual extracted C function consumes a stale ring entry and times out for producer0/reusable descriptor1.

Candidate changes only that publication position plus a checked explanatory comment. C boundary is expressly permitted by this bug's owner rationale. Storage/PCI/input regions remain untouched.

## Checks performed once

- Pre-fix python3 scripts/check/check-arm64-net-tx-ring-cursor.py printed TX ring mismatch producer=0 descriptor=1 result=-110 (failing regression).
- Post-fix python3 scripts/check/check-arm64-net-tx-ring-cursor.py --negative-control: PASS56publication/reuse/wrap cases; PASS old-descriptor-index mutation rejection. Fixture compiles extracted production constants, structures, zero helper and send function. Device model consumes ring producer positions and writes used completions; cache-maintenance boundary alone substituted. Actual packet bytes and unrelated outstanding descriptor ownership checked.
- clang --target=aarch64-none-elf -ffreestanding -fsyntax-only full baremetal_stubs.c: exit0; pre-existing _rt_int_fits_tagged signed-shift warning.
- Working/staged direct-env guards PASS; executable spec count under doc/06_spec zero; whitespace clean.

Astra exact-head review requested. No firmware boot, EL0 runtime, host-visible NIC/HTTP, or durability qualification claimed. Broader bug remains in progress; this is one demonstrated owner repair.

## Landed source slice

PR6393 merged into release/1.0.0 at8800efa39238be2f9d095cc80b0b4a5a8298249f; reviewed head8fd1ecd6ec7. Astra final exact-head verdict zeroP0/P1. PR diff and comments read (none), self-review posted, remote branch deleted. Push gates passed after restoring sparse-checkout scripts/hooks/config dependencies, no bypass. Full test-tree divergence is inherited identical parent/candidate (877vs455baseline,59mirror-only); no test-tree/baseline edits.

Worktree safely reduced to sparse checkout preserving committed source and external patch, reclaiming approximately2.61GiB measured host available-space delta.

Parent must keep canonical broader EL0/network bug in progress: transport publication is repaired, but live ARM64 NIC, EL0, host-visible HTTP and storage admission remain unproved. Do not mark entire record fixed or native-qualified from this host test.
