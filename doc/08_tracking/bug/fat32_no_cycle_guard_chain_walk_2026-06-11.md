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

### Open items (not part of this fix)

- FINDING-T2: No allocator (`write()` remains an ENOSYS stub). The
  `crossLinkFree` invariant cannot be wired until wave-4d lands.

## Fix direction (original)

When implementing wave-4b chain walking, bound the walk by the total cluster
count of the volume (the natural fuel value: a valid chain can never exceed
`data_clusters`), returning Err on exhaustion instead of looping. Wire the
allocator (when written) to the `crossLinkFree` invariant from the Lean model.
