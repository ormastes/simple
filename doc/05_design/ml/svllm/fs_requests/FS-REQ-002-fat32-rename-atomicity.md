# FS-REQ-002: FAT32 rename is not atomic

- **Date:** 2026-04-18
- **svllm phase:** A2
- **Triggering code:** `src/lib/gc_async_mut/svllm/nvfs_client/std_fs.spl:publish_atomic`
- **Need (API or semantic):** either (a) a FAT32-aware `fs_publish_atomic`
  that emulates atomicity via a write-ahead marker file, or (b) a typed
  capability flag on `query_caps()` that lets the packer refuse to publish
  on a non-atomic filesystem.
- **Current workaround:** `publish_atomic` maps 1:1 to POSIX `rename(2)`.
  On ext4/xfs this is atomic (same directory). On FAT32 it is delete-then-
  create — a power-cut between the two can leave the final filename present
  but empty, or absent-despite-source-existing. Packer's visibility rule
  (manifest is the fencepost) mitigates but doesn't fully solve the race
  when the manifest itself is being renamed.
- **Measured impact:** no perf impact. Correctness: documented as
  "safe-stale" in arch.md §5 — on crash the next packer start must clean up
  orphan `*.bin` + `*.tmp`. Not acceptable for multi-tenant clusters.
- **Proposed mapping:** upgrade `NvfsCaps.supports_atomic_publish: bool` into
  a tri-state (`Atomic`, `BestEffort`, `Unsupported`) and have the A2 packer
  abort when BestEffort on a production storage class.
- **Priority:** P2 (FAT32 is bring-up only; canonical nvfs adapter replaces
  this path).
- **Status:** open
