import Nvfs.State
import Nvfs.Invariants

/-!
# `Nvfs.Ops` — transitions

Every transition has signature `FsState → Input → Except FsError FsState`
and **must** preserve `AllInvariants`.  The op bodies are kept as direct
as possible: explicit `match`/`if` trees so `cases`/`simp`/`decide` can
unfold them in `Theorems.lean`.
-/


namespace Nvfs

/-! ### arena_create -/

structure ArenaCreateArgs where
  id         : ArenaId
  class_     : StorageClass
  durability : Durability

def arena_create (s : FsState) (args : ArenaCreateArgs) : Except FsError FsState :=
  if s.arenas.any (fun ar => ar.id == args.id) then
    Except.error FsError.arenaNotFound  -- id reuse: treat as lookup failure
  else
    let ar : Arena := {
      id := args.id, class_ := args.class_, durability := args.durability,
      sealed := false, discarded := false, bytes := [],
      genCreated := s.currentGen, refcount := 0 }
    Except.ok { s with arenas := ar :: s.arenas }

/-! ### arena_append -/

structure ArenaAppendArgs where
  id    : ArenaId
  bytes : List UInt8

/-- Append to a non-sealed, non-discarded arena.  Rejects otherwise. -/
def arena_append (s : FsState) (args : ArenaAppendArgs) : Except FsError FsState :=
  match s.findArena args.id with
  | none => Except.error FsError.arenaNotFound
  | some ar =>
    if ar.sealed then
      Except.error FsError.alreadySealed
    else if ar.discarded then
      Except.error FsError.alreadyDiscarded
    else
      let ar' := { ar with bytes := ar.bytes ++ args.bytes }
      Except.ok { s with
        arenas := s.arenas.map (fun x => if x.id == ar.id then ar' else x) }

/-! ### arena_readv — read-only, no state change -/

def arena_readv (s : FsState) (id : ArenaId) : Except FsError (List UInt8) :=
  match s.findArena id with
  | none => Except.error FsError.arenaNotFound
  | some ar =>
    if ar.discarded then Except.error FsError.alreadyDiscarded
    else Except.ok ar.bytes

/-! ### arena_seal -/

def arena_seal (s : FsState) (id : ArenaId) : Except FsError FsState :=
  match s.findArena id with
  | none => Except.error FsError.arenaNotFound
  | some ar =>
    if ar.sealed then
      -- idempotent: already sealed is ok
      Except.ok s
    else if ar.discarded then
      Except.error FsError.alreadyDiscarded
    else
      let ar' := { ar with sealed := true }
      Except.ok { s with
        arenas := s.arenas.map (fun x => if x.id == ar.id then ar' else x) }

/-! ### arena_discard -/

/-- Discard only if refcount = 0 AND no snapshot pins the arena. -/
def arena_discard (s : FsState) (id : ArenaId) : Except FsError FsState :=
  match s.findArena id with
  | none => Except.error FsError.arenaNotFound
  | some ar =>
    if ar.refcount > 0 then
      Except.error FsError.arenaStillReferenced
    else if s.snapshots.any (fun sn => sn.pinned.contains id) then
      Except.error FsError.snapshotPinsArena
    else
      let ar' := { ar with discarded := true }
      Except.ok { s with
        arenas := s.arenas.map (fun x => if x.id == ar.id then ar' else x) }

/-! ### arena_clone_range — reflink bump -/

structure CloneRangeArgs where
  src     : ArenaId
  dstLogical : LogicalId
  offset  : Nat
  len     : Nat
  birthGen : Generation
  checksum : Checksum

/-- Create a reflink: install a new `shared` pmap entry and bump the
source arena's refcount. -/
def arena_clone_range (s : FsState) (args : CloneRangeArgs)
    : Except FsError FsState :=
  match s.findArena args.src with
  | none => Except.error FsError.arenaNotFound
  | some ar =>
    if ar.discarded then Except.error FsError.alreadyDiscarded
    else
      let e : PmapEntry := {
        logical := args.dstLogical, phys := args.src,
        offset := args.offset, len := args.len,
        birthGen := args.birthGen, shared := true,
        checksum := args.checksum }
      let ar' := { ar with refcount := ar.refcount + 1 }
      Except.ok { s with
        arenas := s.arenas.map (fun x => if x.id == ar.id then ar' else x),
        pmap := e :: s.pmap }

/-! ### pmap_publish -/

structure PmapPublishArgs where
  logical  : LogicalId
  phys     : ArenaId
  offset   : Nat
  len      : Nat
  birthGen : Generation
  checksum : Checksum

/-- Publish a new pmap entry — only legal if the matching WAL record is
already durable (I5). -/
def pmap_publish (s : FsState) (args : PmapPublishArgs) : Except FsError FsState :=
  if !(s.wal.any (fun r =>
        decide (r.op = WalOp.pmapPublish) && decide (r.birthGen = args.birthGen)
          && decide (r.lsn ≤ s.durableLsn))) then
    Except.error FsError.publishBeforeDurable
  else
  match s.findArena args.phys with
  | none => Except.error FsError.arenaNotFound
  | some ar =>
    if ar.discarded then Except.error FsError.alreadyDiscarded
    else
      let e : PmapEntry := {
        logical := args.logical, phys := args.phys,
        offset := args.offset, len := args.len,
        birthGen := args.birthGen, shared := false,
        checksum := args.checksum }
      let ar' := { ar with refcount := ar.refcount + 1 }
      Except.ok { s with
        arenas := s.arenas.map (fun x => if x.id == ar.id then ar' else x),
        pmap := e :: s.pmap }

/-! ### wal_append -/

structure WalAppendArgs where
  op       : WalOp
  payload  : List UInt8
  birthGen : Generation

/-- Assign the next strictly-greater LSN and append. -/
def wal_append (s : FsState) (args : WalAppendArgs) : Except FsError FsState :=
  let nextLsn := match s.wal.getLast? with
    | none => 1
    | some r => r.lsn + 1
  let r : WalRecord := {
    lsn := nextLsn, op := args.op, payload := args.payload,
    birthGen := args.birthGen }
  Except.ok { s with wal := s.wal ++ [r] }

/-! ### checkpoint_commit -/

structure CheckpointArgs where
  newInodeRoot  : ArenaId
  newExtentRoot : ArenaId
  newAllocRoot  : ArenaId
  newGen        : Generation
  lsnAtSeal     : Lsn

/-- Publish a new checkpoint root into the *inactive* replica slot and
flip `active`.  Refuses if the new roots don't point at live arenas. -/
def checkpoint_commit (s : FsState) (args : CheckpointArgs)
    : Except FsError FsState :=
  if !(s.arenaLive args.newInodeRoot
        && s.arenaLive args.newExtentRoot
        && s.arenaLive args.newAllocRoot) then
    Except.error FsError.arenaNotFound
  else if args.lsnAtSeal > s.durableLsn then
    Except.error FsError.publishBeforeDurable
  else
    let newRoot : CheckpointRoot := {
      inodeRoot := args.newInodeRoot,
      extentRoot := args.newExtentRoot,
      allocRoot := args.newAllocRoot,
      generation := args.newGen,
      lsnAtSeal := args.lsnAtSeal,
      validChecksum := true }
    let sb := s.superblock
    let sb' : Superblock :=
      if sb.active then
        { sb with replicaA := newRoot, active := false }
      else
        { sb with replicaB := newRoot, active := true }
    Except.ok { s with superblock := sb', currentGen := args.newGen }

/-! ### mount / unmount -/

def mount (s : FsState) : Except FsError FsState :=
  if !(I6b s) then
    Except.error FsError.superblockCorrupt
  else
    Except.ok { s with mountEpoch := s.mountEpoch + 1 }

def unmount (s : FsState) : Except FsError FsState := Except.ok s

end Nvfs
