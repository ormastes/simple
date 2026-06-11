# FAT32 driver: no cycle guard for cluster-chain walks (infinite-loop hazard)

- **Status:** open (latent — chain walking not yet implemented)
- **Found:** 2026-06-11 by the Lean `fat32` formal model (FINDING-T3 in
  `src/verification/fat32/Fat32/Theorems.lean`)
- **Severity:** low today, high once wave-4b lands — a corrupted/cyclic FAT
  table would hang the kernel in an unbounded loop.

## Detail

The Lean model's `chainWalkGuarded` carries a fuel bound and T1 proves the
walk terminates in ≤ fuel+1 clusters. The real `fat32.spl` has NO such guard
— and currently no chain walk at all:

- `read_cluster_chain` (wave-4b) is unimplemented; `read()` serves only the
  mount-time cached `root_dir_data` (FINDING-T1).
- No allocator exists; `write()` is a stub returning -1 (FINDING-T2), so the
  proved no-cross-link invariant (`crossLinkFree`) has nothing to wire to yet.

## Fix direction

When implementing wave-4b chain walking, bound the walk by the total cluster
count of the volume (the natural fuel value: a valid chain can never exceed
`data_clusters`), returning Err on exhaustion instead of looping. Wire the
allocator (when written) to the `crossLinkFree` invariant from the Lean model.
