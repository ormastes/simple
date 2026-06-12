# FAT32 driver: no cycle guard for cluster-chain walks (infinite-loop hazard)

- **Status:** closed — cycle guard implemented 2026-06-11
- **Found:** 2026-06-11 by the Lean `fat32` formal model (FINDING-T3 in
  `src/verification/fat32/Fat32/Theorems.lean`)
- **Severity:** was high (infinite loop on cyclic FAT); now guarded

## Detail

The Lean model's `chainWalkGuarded` carries a fuel bound and T1 proves the
walk terminates in ≤ fuel+1 clusters.

### What was implemented (wave-4b, 2026-06-11)

- `Fat32Filesystem.data_clusters` field added; computed in `mount()` as
  `(total_sectors_32 - data_start_sector) / sectors_per_cluster`.
- `Fat32Filesystem._read_fat_entry(dev, cluster)` — reads one 28-bit FAT32
  entry from disk via `dev.read_sector`.
- `Fat32Filesystem.read_cluster_chain(dev, start)` — guarded walk matching
  `chainWalkGuarded` semantics:
  - fuel = `data_clusters`; decremented before each cluster append
  - Returns `Err("fat32: cluster chain exceeds volume cluster count (cycle?)")`
    on fuel exhaustion
  - Returns `Err` on FREE (0x00000000) or BAD (0x0FFFFFF7) entries mid-chain
  - Returns `Err` for `start < 2` (invalid/reserved cluster number)
  - Returns `Ok([])` for empty-chain edge cases (`current < 2` exit)
- `Fat32Filesystem.make_for_chain_test(...)` — test factory for unit specs.
- `src/os/kernel/fs/fat32.spl` updated; Lean model unchanged (semantics match
  `chainWalkGuarded` exactly; `lake build` green, zero sorry).

### Regression spec

`test/01_unit/os/kernel/fs/fat32_chain_walk_spec.spl` — 11 tests, all green:
  - linear chain walk (1, 3, N clusters; EOC boundary values)
  - cycle guard (fuel exhaustion on 2→3→2 cycle; chain > fuel → Err)
  - fuel exactly equal to chain length → Ok
  - FREE / BAD mid-chain → Err
  - invalid start (cluster 0, cluster 1) → Err

### What was implemented (wave-4c, 2026-06-11)

- `Fat32Filesystem.read(dev, h, buf)` — signature extended with `dev: BlockDevice`
  parameter; implementation replaced the `root_dir_data` shortcut with a proper
  cluster-chain walk via `read_cluster_chain(dev, h.start_cluster)`.
- File bytes are assembled in chain order: each cluster's sectors are fetched via
  `dev.read_sector(lba)` and copied into `buf`, respecting `h.file_size` so
  cluster padding past the real EOF is never returned.
- `Fat32Filesystem.make_for_read_test(...)` — additional test factory exposing
  explicit `data_start_sector` and `sectors_per_cluster` for read-unit specs.
- `test/01_unit/os/kernel/fs/fat32_read_spec.spl` — 10 tests:
  single-cluster exact read, buf-smaller-than-file read, size-truncation of
  last cluster, two-cluster and three-cluster assembly in chain order,
  multi-cluster truncation, EOF/empty-buf early exits, cyclic FAT → Err(EIO),
  FREE mid-chain → Err(EIO).

### FINDING-T1 — CLOSED (wave-4c done)

`read()` now walks the guarded cluster chain via `read_cluster_chain`.  Any
cyclic or corrupt FAT encountered during a `read()` call surfaces as
`Err(EIO=-5)` rather than hanging. Wave-4d (allocator + crossLinkFree wiring)
remains open as FINDING-T2.

### What was implemented (wave-4e, 2026-06-12)

FINDING-T2-dirent: on-disk directory-entry persistence after write().

- `FileHandle` struct gained two new fields:
  - `dirent_sector: u64` — LBA of the 512-byte sector holding the file's 32-byte
    directory entry (0 = no backing dirent, e.g. test-only handles).
  - `dirent_offset: i32` — byte offset within that sector where the entry begins.
- `Fat32Filesystem.open()` now records `dirent_sector`/`dirent_offset` by
  computing `root_dir_lba + (entry_offset / bps)` and `entry_offset % bps`.
- `Fat32Filesystem._update_dirent(dev, h)` — new private method:
  reads `h.dirent_sector`, patches the 32-byte entry in-place
  (cluster_high +20..+21, cluster_low +26..+27, file_size +28..+31),
  writes the sector back, and updates the `root_dir_data` cache at the
  corresponding flat offset so `stat()` and subsequent `open()` calls see
  the new values without a remount. Skips entirely when `h.dirent_sector == 0`.
- `Fat32Filesystem.write()` calls `_update_dirent` after updating `h.file_size`,
  removing the `NOTE` placeholder about missing persistence.
- `Fat32Filesystem.make_for_dirent_test(...)` — new test factory accepting an
  initial `root_dir_data` slice so `_find_root_entry` / `open()` can resolve
  8.3 names in unit tests.
- `Fat32Filesystem._find_root_entry()` signature changed from
  `Result<i32?, i32>` to `Result<i32, i32>` (sentinel -1 for not-found) to
  avoid an interpreter limitation where `.unwrap()` fails on `i32?` Optional
  values stored as raw primitives.  `open()` and `stat()` updated accordingly.
- `test/01_unit/os/kernel/fs/fat32_dirent_spec.spl` — 7 new tests, all green:
  - `open()` records `dirent_sector = 64` (root-dir LBA) and `dirent_offset = 32`
  - after `write()`, on-disk dirent cluster_low reflects allocated cluster 2
  - after `write()`, on-disk dirent cluster_high is 0 (cluster < 65536)
  - after `write()`, on-disk dirent file_size equals bytes written
  - `root_dir_data` cache file_size coherent (stat() sees updated size)
  - `dirent_sector=0` handle skips `_update_dirent` without error

### FINDING-T2-dirent — CLOSED (wave-4e done, 2026-06-12)

After write(), `first_cluster` and `file_size` are now persisted to the
on-disk directory entry; the `root_dir_data` cache is kept coherent in the
same call.  A remount will see the correct metadata.

### Open items (not part of this fix)

None remaining for the cycle-guard / allocator / dirent chain.

## Fix direction (original)

When implementing wave-4b chain walking, bound the walk by the total cluster
count of the volume (the natural fuel value: a valid chain can never exceed
`data_clusters`), returning Err on exhaustion instead of looping. Wire the
allocator (when written) to the `crossLinkFree` invariant from the Lean model.
