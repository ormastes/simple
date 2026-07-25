/-!
# `Nvfs.Basic` — Primitive types

Enumerations and scalar abbreviations used by the NVFS state model.  These
mirror the Simple implementation in `examples/nvfs/src/core/` but are
stripped to what the proofs need.

Design source: `doc/05_design/nvfs_design.md` (v1, §3 Storage classes,
§4 Arenas, §5.1 Superblock, §5.3 Intent log).
-/

namespace Nvfs

/-- 64-bit arena identifier.  Arenas are unique over the lifetime of the
pool (never reused). -/
abbrev ArenaId : Type := Nat

/-- Logical page / extent key used by the pmap. -/
abbrev LogicalId : Type := Nat

/-- Monotone 64-bit log sequence number (`WAL`). -/
abbrev Lsn : Type := Nat

/-- Generation counter.  Bumped atomically on every checkpoint publish. -/
abbrev Generation : Type := Nat

/-- 32-bit CRC32C checksum, modelled abstractly. -/
abbrev Checksum : Type := Nat

/-- The six NVFS storage classes (design §3.1).

* `METADURABLE` — superblock, manifests, pmap roots, catalogs.
* `DBWAL`       — spostgre WAL, svllm append-only logs.
* `DBTEMP`      — temp forks, sort/hash spill; discarded on restart.
* `GENERALMUT`  — general mutable (out-of-place) data extents.
* `IMMUTABLE`   — tensor packs, manifests, model blobs (sealed on first close).
* `COLD`        — archival / backup-root referenced extents.
-/
inductive StorageClass where
  | metadurable
  | dbwal
  | dbtemp
  | generalmut
  | immutable
  | cold
  deriving DecidableEq, Repr

/-- Three durability classes (design §3.3).

These map straight to the `Durability` header field that every arena
carries.  `volatile` is discardable on crash, `groupCommit` batches
fsyncs, `sync` forces a per-op barrier. -/
inductive Durability where
  | volatile
  | groupCommit
  | sync
  deriving DecidableEq, Repr

/-- WAL op-codes (design §5.3).  These drive crash-recovery replay. -/
inductive WalOp where
  | arenaCreate
  | arenaSeal
  | arenaDiscard
  | pmapPublish
  | extentAlloc
  | extentFree
  | reflinkBump
  | reflinkDrop
  deriving DecidableEq, Repr

/-- Errors returned by transitions.  Kept small and total so `Except`
case-analysis in the theorems stays tractable. -/
inductive FsError where
  | alreadySealed
  | alreadyDiscarded
  | arenaNotFound
  | arenaStillReferenced
  | refcountUnderflow
  | logicalConflict
  | lsnNotMonotone
  | publishBeforeDurable
  | superblockCorrupt
  | snapshotPinsArena
  | reflinkNotFound
  deriving DecidableEq, Repr

end Nvfs
