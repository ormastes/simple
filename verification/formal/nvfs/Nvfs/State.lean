import Nvfs.Basic

/-!
# `Nvfs.State` — the filesystem world state

State records used as the argument to every transition.  We stay in the
purely-functional, total fragment — no `Option`/`Except` baked into the
fields — so `decide`, `simp` and `omega` can all close the easy cases.

Design source: `doc/05_design/nvfs_design.md` §4 (arena object),
§5.1 (superblock), §5.2 (pmap), §5.3 (WAL), §9 (snapshots).
-/


namespace Nvfs

/-- An NVFS arena (design §4.1 + §5.2).

* `sealed`   — once `true`, append is rejected (monotone).
* `discarded`— once `true`, the arena is dead; no reads/writes.
* `bytes`    — the append-only byte buffer.  Modelled as `List UInt8`.
* `genCreated` — the checkpoint generation at which the arena was born.
* `refcount`  — count of pmap + reflink + snapshot references.
-/
structure Arena where
  id         : ArenaId
  class_     : StorageClass
  durability : Durability
  sealed     : Bool
  discarded  : Bool
  bytes      : List UInt8
  genCreated : Generation
  refcount   : Nat
  deriving Repr

/-- A pmap entry (design §5.2).  Maps a logical page/extent id to a
slice of an arena. -/
structure PmapEntry where
  logical  : LogicalId
  phys     : ArenaId
  offset   : Nat
  len      : Nat
  birthGen : Generation
  /-- When `true`, this entry is part of a reflink/clone set that is
  allowed to alias another entry's `(phys, offset)`. -/
  shared   : Bool
  checksum : Checksum
  deriving Repr

/-- Checkpoint root (design §5.1 body).  Points at the live inode tree,
extent tree and allocator root.  `validChecksum` models the on-disk
CRC32C over the checkpoint header. -/
structure CheckpointRoot where
  inodeRoot     : ArenaId
  extentRoot    : ArenaId
  allocRoot     : ArenaId
  generation    : Generation
  lsnAtSeal     : Lsn
  validChecksum : Bool
  deriving Repr

/-- Dual-replica superblock (design §5.1).  Only one replica is the
"active" root at any time; the other is the previous or staging copy. -/
structure Superblock where
  replicaA : CheckpointRoot
  replicaB : CheckpointRoot
  /-- `false` selects A, `true` selects B. -/
  active   : Bool
  deriving Repr

/-- A WAL record.  Payload is kept abstract as a byte list — we only
reason about LSN ordering and durability here. -/
structure WalRecord where
  lsn     : Lsn
  op      : WalOp
  payload : List UInt8
  birthGen : Generation
  deriving Repr

/-- An active snapshot pins a set of arenas at a specific generation. -/
structure Snapshot where
  generation : Generation
  pinned     : List ArenaId
  deriving Repr

/-- Full NVFS state — the "world" that transitions rewrite. -/
structure FsState where
  arenas       : List Arena
  pmap         : List PmapEntry
  superblock   : Superblock
  wal          : List WalRecord
  durableLsn   : Lsn
  currentGen   : Generation
  mountEpoch   : Nat
  snapshots    : List Snapshot
  deriving Repr

/-- Trivial initial state: one empty, un-sealed, un-discarded metadurable
arena and an empty pmap / WAL.  Used by the feature-file scenarios. -/
def FsState.empty : FsState :=
  let root : CheckpointRoot := {
    inodeRoot := 0, extentRoot := 0, allocRoot := 0,
    generation := 0, lsnAtSeal := 0, validChecksum := true }
  { arenas := []
    pmap := []
    superblock := { replicaA := root, replicaB := root, active := false }
    wal := []
    durableLsn := 0
    currentGen := 0
    mountEpoch := 0
    snapshots := [] }

/-- Find an arena by id.  Returns `none` if not present.  Proofs prefer
the `List.find?` spelling so the `simp` set handles it. -/
def FsState.findArena (s : FsState) (a : ArenaId) : Option Arena :=
  s.arenas.find? (fun ar => ar.id == a)

/-- The currently active checkpoint root. -/
def FsState.activeRoot (s : FsState) : CheckpointRoot :=
  if s.superblock.active then s.superblock.replicaB else s.superblock.replicaA

end Nvfs
