# SOSIX QEMU matrix evidence status — 2026-08-13

## Scope and acceptance

The matrix remains `4 hosts × 6 guests = 24` rows. A row is PASS only when its
canonical `evidence.env` is producer-generated from a clean source, a closed
pre-run host admission, hash-bound QEMU/firmware/kernel/image/program artifacts,
and an ordered transcript proving boot, real `/SYS/APPS` listing, a filesystem
program, exit/reap, and `TEST PASSED`. A diagnostic transcript or handwritten
record is not a replacement.

The collector remains the only matrix-promotion owner and requires exactly 24
valid bundles. macOS is postponed for lack of a prepared Darwin executor, not
excluded or complete.

## Current evidence ledger

| Host | Guest | Status | Authoritative evidence / exact resume |
| --- | --- | --- | --- |
| Linux | x86_64 | canonical row PASS | `linux/x86_64-ovmf-canonical-20260813-final/canonical-root/linux/x86_64/run-X86_64_COLLECTOR_NONCE_20260813_V3/evidence.env`; OVMF pflash → GRUB → guest entry → real FS program/reap. |
| Linux | arm64 | canonical row PASS | `linux/arm64-canonical-v21-20260812/canonical-root/linux/arm64/run-arm64-collector-v21-20260812-n1/evidence.env`; direct-kernel v2 receipt. |
| Linux | riscv32 | canonical row PASS | `native-v2-1832753b/linux/riscv32/run-COLLECTOR-RV32-1832753B-A/evidence.env`; direct-kernel v2 receipt. |
| Linux | x86_32 | blocked | CPL3 filesystem lifecycle has no linked `enter_user_first.s`, no installed GDT/TSS/`esp0` owner, only a weak same-CPL `int 0x80` probe bridge, and a context switch that never restores `to`; freeze and wire authenticated token/stack/trap/scheduler owners before a live run. |
| Linux | arm32 | blocked | The current entry is an NVFS/SMF probe chain that can print `TEST PASSED`; it neither reads mounted `/FSEXEC.ELF` nor performs a user-mode/SVC/reap lifecycle. ARM32 vector/SVC owners remain below canonical staging and boot-secret integration, so no live row exists. |
| Linux | riscv64 | blocked | Existing retained records are diagnostics; rebuild and canonical direct-kernel/OpenSBI closure remains required. |
| Windows | all six | blocked, matrix peer missing | The documented `scripts/check/check-sosix-qemu-matrix.ps1` does not exist. Implement the PowerShell peer with the same admission/runtime/spec/producer closure before a prepared Windows host can execute `-AllGuests -Run -Parallel`. |
| macOS | all six | postponed, not complete | On a prepared Darwin host use `SIMPLE_QEMU_ACCELERATOR=tcg sh scripts/check/check-sosix-qemu-matrix.shs --host macos --all-guests --run --parallel`; retain native-host blockers until then. |
| FreeBSD | all six | blocked, target-host execution required | Linux bootstrap preflight currently fails `base_image`: obtain the checksum-pinned FreeBSD 14.4 cloud image, run `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke --download`, then on FreeBSD run `sh scripts/check/check-sosix-qemu-matrix.shs --host freebsd --all-guests --run --parallel`. |

All artifact paths above are rooted at
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/`.

The 2026-08-13 Linux all-guest preflight is retained at
`linux/matrix/linux-matrix-preflight-20260813/`. All six host-admission
receipts passed (including emulator, accelerator and shared-storage checks),
but this checkout publishes only the x86_64 kernel/image pair; the other five
rows correctly report missing current build artifacts. That local publication
state does not supersede the immutable ARM64 and RV32 PASS bundles above.

## Parallel ownership plan

1. The matrix wrapper remains the sole host-admission/settings owner. It may
   fan out only selected guest rows; every child receives the same immutable
   settings receipt and writes a distinct run directory.
2. A guest row owns its nonce image, firmware-variable copy, serial transcript,
   kernel/image/program hashes and producer invocation. It may not modify a
   shared base image or another row's run directory.
3. The collector is the sole parent-authoritative commit point. It imports only
   completed producer bundles, validates their hashes/stages, and rejects any
   non-24-row promotion.
4. External-host operators own execution only; the root/high reviewer owns
   source/lineage review and collector promotion. A blocked or postponed row
   remains a visible acceptance criterion.

## Next current-host work

1. Keep the three Linux PASS bundles immutable; do not merge their old
   diagnostic predecessors into the collector source.
2. Complete RV64 fresh canonical closure, then execute one producer run.
3. Continue the ABI-frozen x86_32 and ARM32 privilege-entry owners through
   mounted ELF staging, live entry, exit 37 and reaping before attempting a
   producer run.
4. After each new bundle, invoke the collector once with the full source root;
   it must remain blocked until all 24 valid rows exist.
