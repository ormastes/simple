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
`Err(EIO=-5)` rather than hanging.

### What was implemented (wave-4d, 2026-06-11)

- `ENOSPC: i32 = -28` error code added.
- `Fat32Filesystem._write_fat_entry(dev, cluster, value)` — writes one 28-bit
  FAT32 entry via `dev.write_sector`; preserves the top 4 reserved bits of the
  existing on-disk word (read-modify-write).
- `Fat32Filesystem.allocate_cluster(dev)` — scans FAT starting at cluster 2
  for a FREE (0x00000000) entry, bounded by `data_clusters`; marks it EOC
  (0x0FFFFFFF) before returning, satisfying the `crossLinkFree` ordering
  contract (no FREE cluster is ever linked).  Returns `Err(ENOSPC=-28)` when
  the FAT is full.
- `Fat32Filesystem.append_cluster(dev, chain_end, new_cluster)` — links
  `chain_end → new_cluster` in the FAT.  Requires that `new_cluster` is
  already marked EOC (guaranteed by `allocate_cluster`).
- `Fat32Filesystem.write(dev, h, buf)` — append-only write path: allocates the
  first cluster for fresh files (`h.start_cluster < 2`), extends the chain when
  `buf` requires more clusters, writes data via read-modify-write sector writes,
  and returns `Ok(updated_handle)` with `updated_handle.file_size` reflecting
  bytes written.  `FileHandle` is a value type in Simple; callers must use the
  returned handle.
- `Fat32Filesystem.make_for_alloc_test(...)` — additional test factory for
  allocator/write unit specs.
- Lean: `T7a_valid_link_ge2`, `T7b_free_not_in_chain`,
  `T7c_alloc_step2_new_chain_disjoint` — three new theorems (zero sorry)
  proving that a FREE cluster cannot appear in any existing chain walk, and
  that the singleton [nc] (post-Step-2) is disjoint from all pre-existing chains.
  This wires the `crossLinkFree` invariant to the allocator's ordering contract.
  `lake build` green, zero sorry.

### FINDING-T2 — CLOSED (wave-4d done — partial)

The cluster allocator is implemented.  `crossLinkFree` is wired via T7b/T7c.

**Open sub-item: on-disk directory-entry persistence.**
`write()` updates `FileHandle.file_size` in memory but does not rewrite the
FAT32 directory entry (dirent) on disk.  Updating the dirent requires locating
the 32-byte entry in the root-dir cluster and writing back the new file size
at bytes 28-31.  This is a separate tracked item; the written data IS
durably stored in the cluster chain (readable back via `read()`), but the
file size as seen by a fresh `open()` + `stat()` will still reflect the
original on-disk value.  Tracked as a follow-up under FINDING-T2-dirent.

### Regression spec

`test/01_unit/os/kernel/fs/fat32_alloc_spec.spl` — 9 tests, all green:
  - `allocate_cluster`: cluster 2 from empty FAT marked EOC; skips used clusters;
    full FAT → Err(ENOSPC=-28).
  - `append_cluster`: links chain_end → new_cluster; EOC at new tail preserved.
  - `_write_fat_entry`: preserves bits 28-31 of existing entry.
  - `write()`: fresh handle allocates + stores bytes readable via read();
    multi-cluster write extends chain; full FAT → Err(ENOSPC).

## Fix direction (original)

When implementing wave-4b chain walking, bound the walk by the total cluster
count of the volume (the natural fuel value: a valid chain can never exceed
`data_clusters`), returning Err on exhaustion instead of looping. Wire the
allocator (when written) to the `crossLinkFree` invariant from the Lean model.
