# ARM64 VirtIO storage repair — 2026-11-03

Owned bug: `arm64_simpleos_virtio_blk_durable_write_gap_2026-08-14`; parent canonical claim `arm64-storage-20261103` confirmed 10:14:41Z. Isolated worktree `/tmp/simple-arm64-storage-durability-20261103`, branch `work/arm64-storage-durability-20261103`, base `4cc3cd4a800837eb21dd4d2d83303e50cb5d32d7`, candidate `11eaac8111b`.

## Existing implementation

The stale initial report does not describe today's complete source: FAT32 atomic replace now has journal banks, checked write/FLUSH sequencing, recovery and a mount-published capability gate. VirtIO write/flush paths acquire atomic request ownership, validate used-ring heads, handle device status, and quarantine/reset after indeterminate completion. These prior implementations do not prove live persistence. `test/03_system/os/server/fat32_database_replace_reboot_spec.spl` remains explicitly failing/unimplemented for real QEMU crash injection and reboot.

## Actual newly repaired source defect

Both `driver_operations.spl` method `init_ok` and `driver_class.spl` function `virtio_blk_arm_init` negotiate only low feature bit9 (FLUSH), then read optional config offset276 (`blk_size`) without negotiating bit6. They assigned that hint to `sector_size`, contradicting VirtIO's fixed512-byte request/capacity unit. A4096 hint makes `read_sector_owned_bytes` reject non512 size and `write_sector` reject512-byte data; a4096-byte write instead exceeds the1024-byte DMA scratch allocation.

Candidate removes both optional config reads and explicitly preserves512 transfer sectors. No admission, FLUSH, completion or recovery condition was weakened. Primary contract: https://docs.oasis-open.org/virtio/virtio/v1.2/virtio-v1.2.html (§5.2 block device).

## Verification and limits

- `git diff --check`: PASS.
- `sh scripts/audit/direct-env-runtime-guard.shs --working`: PASS.
- `sh scripts/audit/direct-env-runtime-guard.shs --staged`: PASS (run before staging; no staged changes then).
- Required `find doc/06_spec -name '*_spec.spl' | wc -l`:0.
- Added structural coverage to existing durability-boundary spec; **not executed** because no admitted self-hosted test runtime is available. No Rust-seed fallback.
- Documented actual future MMIO fixture matrix: both init routes, hint4096/512/0, capacity512 units, exact adjacent-LBA512 transfers, no config276 read, partial rejection, FLUSH feature present/absent, same-image fresh-QEMU reboot. This is an acceptance specification, **not an implemented or passed MMIO fixture**.
- No heavy build, QEMU, new CI run, target execution or durability claim.
- Astra exact-head source review requested. No PR/push/merge yet; source repair remains unqualified pending review/test disposition.

Canonical DB is parent-owned and was not edited here. Full historical durability bug remains unresolved; this candidate addresses a concrete prerequisite defect only.

## Independent review and hold

Astra reviewed exact candidate `11eaac8111b`: zero concrete P0/P1 source findings for the narrow512-byte protocol-unit correction; independently confirmed OASIS1.2 §5.2.5. Structural text assertions are not executed initialization/MMIO evidence. Parent and reviewer require holding the candidate unlanded until behavioral verification is available; no whole-bug status promotion or durability claim.

On parent instruction the clean committed worktree was converted to sparse checkout retaining driver/check scripts/focused OS tests/bugdocs/rules. Footprint124MiB; reported filesystem free31GiB after conversion. Candidate commit and all owned files preserved.
