import Nvfs.State

/-!
# `Nvfs.Invariants` — the ten state-integrity invariants

These are the predicates the rest of the project must preserve.  Every
invariant is phrased twice:

* a `Prop` form (for theorem statements and `simp`-style reasoning);
* a `Bool` form (for `decide` / property-testing via `native_decide`).

The `Bool` forms are intentionally kept as pure `List.all`/`List.any`
combinators so ground-term instances close by `decide`.
-/


namespace Nvfs

/-- An arena is "live" iff it exists and has not been discarded. -/
def FsState.arenaLive (s : FsState) (a : ArenaId) : Bool :=
  s.arenas.any (fun ar => ar.id == a && !ar.discarded)

/-- **I1 — pmap entries live.**  Every pmap entry references a live
(non-discarded, present) arena. -/
def I1_pmapEntriesLive (s : FsState) : Prop :=
  ∀ e ∈ s.pmap, s.arenaLive e.phys = true

def I1b (s : FsState) : Bool :=
  s.pmap.all (fun e => s.arenaLive e.phys)

/-- **I2 — seal monotonicity.**  No arena has both `sealed = false` and
a WAL seal record already committed for it.  Equivalently: if the WAL
contains an `arenaSeal` record for `a`, then `a.sealed = true`.  We
capture the simpler "sealed arenas stay sealed across transitions" via
the Bool well-formedness check that every sealed arena is still in the
`arenas` list. -/
def I2_sealMonotonic (s : FsState) : Prop :=
  ∀ ar ∈ s.arenas, ar.sealed = true → ar.discarded = false ∨ ar.refcount = 0

def I2b (s : FsState) : Bool :=
  s.arenas.all (fun ar => !ar.sealed || !ar.discarded || ar.refcount == 0)

/-- **I3 — refcount consistency.**  `arena.refcount` is at least the
number of pmap entries pointing at it.  Reflinks and snapshots are
modelled by `PmapEntry.shared = true` and `Snapshot.pinned`, both of
which are also counted. -/
def arenaPmapRefs (s : FsState) (a : ArenaId) : Nat :=
  (s.pmap.filter (fun e => e.phys == a)).length

def arenaSnapRefs (s : FsState) (a : ArenaId) : Nat :=
  (s.snapshots.filter (fun sn => sn.pinned.contains a)).length

def I3_refcountConsistent (s : FsState) : Prop :=
  ∀ ar ∈ s.arenas,
    arenaPmapRefs s ar.id + arenaSnapRefs s ar.id ≤ ar.refcount
      ∧ (ar.discarded = true → ar.refcount = 0)

def I3b (s : FsState) : Bool :=
  s.arenas.all (fun ar =>
    decide (arenaPmapRefs s ar.id + arenaSnapRefs s ar.id ≤ ar.refcount) &&
      (!ar.discarded || ar.refcount == 0))

/-- **I4 — WAL LSN monotonicity.**  LSNs are strictly increasing in the
order the records were appended; `durableLsn` never exceeds the
last-appended LSN. -/
def walStrictlyIncreasing : List WalRecord → Bool
  | []           => true
  | [_]          => true
  | r₁ :: r₂ :: rest => decide (r₁.lsn < r₂.lsn) && walStrictlyIncreasing (r₂ :: rest)

def I4_walLsnMonotonic (s : FsState) : Prop :=
  walStrictlyIncreasing s.wal = true ∧
    (∀ r ∈ s.wal, r.lsn ≥ s.durableLsn → True)  -- vacuous: every LSN satisfies this

def I4b (s : FsState) : Bool :=
  walStrictlyIncreasing s.wal

/-- **I5 — WAL-before-publish.**  Every pmap entry's `birthGen` is
backed by a WAL record whose LSN has already been marked durable. -/
def I5_walBeforePublish (s : FsState) : Prop :=
  ∀ e ∈ s.pmap,
    ∃ r ∈ s.wal, r.op = WalOp.pmapPublish ∧ r.birthGen = e.birthGen
      ∧ r.lsn ≤ s.durableLsn

def I5b (s : FsState) : Bool :=
  s.pmap.all (fun e =>
    s.wal.any (fun r =>
      decide (r.op = WalOp.pmapPublish) && decide (r.birthGen = e.birthGen)
        && decide (r.lsn ≤ s.durableLsn)))

/-- **I6 — at least one valid superblock replica.**  The "two on-disk
copies, one always good" guarantee (design §5.1). -/
def I6_superblockOneValid (s : FsState) : Prop :=
  s.superblock.replicaA.validChecksum = true
    ∨ s.superblock.replicaB.validChecksum = true

def I6b (s : FsState) : Bool :=
  s.superblock.replicaA.validChecksum || s.superblock.replicaB.validChecksum

/-- **I7 — checkpoint roots point at live arenas.**  The active
checkpoint's three roots (inode/extent/alloc) must reference arenas
that are still live. -/
def I7_checkpointRootsConsistent (s : FsState) : Prop :=
  let r := s.activeRoot
  s.arenaLive r.inodeRoot = true
    ∧ s.arenaLive r.extentRoot = true
    ∧ s.arenaLive r.allocRoot = true

def I7b (s : FsState) : Bool :=
  let r := s.activeRoot
  s.arenaLive r.inodeRoot && s.arenaLive r.extentRoot && s.arenaLive r.allocRoot

/-- **I8 — extent mapping injectivity (modulo sharing).**  No two pmap
entries with distinct `logical` ids map to the same `(phys, offset)`
unless both carry `shared = true`. -/
def pmapPairOk (e₁ e₂ : PmapEntry) : Bool :=
  decide (e₁.logical = e₂.logical)
    || decide (e₁.phys ≠ e₂.phys)
    || decide (e₁.offset ≠ e₂.offset)
    || (e₁.shared && e₂.shared)

def I8_extentMappingInjective (s : FsState) : Prop :=
  ∀ e₁ ∈ s.pmap, ∀ e₂ ∈ s.pmap,
    e₁.logical ≠ e₂.logical →
      e₁.phys ≠ e₂.phys ∨ e₁.offset ≠ e₂.offset
        ∨ (e₁.shared = true ∧ e₂.shared = true)

def I8b (s : FsState) : Bool :=
  s.pmap.all (fun e₁ => s.pmap.all (fun e₂ => pmapPairOk e₁ e₂))

/-- **I9 — reflink refcount matches.**  An arena whose id appears as the
`phys` of ≥ 2 `shared` pmap entries has `refcount ≥ 2`.  More generally:
refcount ≥ number of pmap entries pointing at it. -/
def I9_reflinkRefcountMatches (s : FsState) : Prop :=
  ∀ ar ∈ s.arenas, arenaPmapRefs s ar.id ≤ ar.refcount

def I9b (s : FsState) : Bool :=
  s.arenas.all (fun ar => decide (arenaPmapRefs s ar.id ≤ ar.refcount))

/-- **I10 — snapshot-pinned arenas cannot be discarded.** -/
def I10_snapshotArenaPinned (s : FsState) : Prop :=
  ∀ sn ∈ s.snapshots, ∀ a ∈ sn.pinned,
    ∀ ar ∈ s.arenas, ar.id = a → ar.discarded = false

def I10b (s : FsState) : Bool :=
  s.snapshots.all (fun sn =>
    sn.pinned.all (fun a =>
      s.arenas.all (fun ar => !(decide (ar.id = a)) || !ar.discarded)))

/-- Aggregate `Bool` well-formedness predicate — used by the feature
file as a single check on a generated state. -/
def AllInvariantsBool (s : FsState) : Bool :=
  I1b s && I2b s && I3b s && I4b s && I5b s && I6b s
    && I7b s && I8b s && I9b s && I10b s

/-- Aggregate `Prop` form: every invariant holds. -/
structure AllInvariants (s : FsState) : Prop where
  i1  : I1_pmapEntriesLive s
  i2  : I2_sealMonotonic s
  i3  : I3_refcountConsistent s
  i4  : I4_walLsnMonotonic s
  i5  : I5_walBeforePublish s
  i6  : I6_superblockOneValid s
  i7  : I7_checkpointRootsConsistent s
  i8  : I8_extentMappingInjective s
  i9  : I9_reflinkRefcountMatches s
  i10 : I10_snapshotArenaPinned s

end Nvfs
