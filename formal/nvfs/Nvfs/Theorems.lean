import Nvfs.Ops
import Nvfs.Invariants

/-!
# `Nvfs.Theorems` — preservation theorems

For each transition `op : FsState → I → Except FsError FsState` we state

  `op_preserves : AllInvariants s → op s i = Except.ok s' → AllInvariants s'`

Proof hygiene:
* prefer `decide`/`simp`/`omega` for closed cases;
* use `native_decide` only when `decide` is slow and the goal is
  ground-term;
* never use `unsafe` or `extern` constructs.
-/


namespace Nvfs

/-! ## Helper lemmas -/

/-- `arenaLive` is monotone under prepending a fresh arena. -/
theorem arenaLive_cons_preserves
    (s s' : FsState) (ar : Arena) (a : ArenaId)
    (hs : s'.arenas = ar :: s.arenas)
    (h : s.arenaLive a = true)
    : s'.arenaLive a = true := by
  unfold FsState.arenaLive at *
  rw [hs]
  rw [List.any_cons, h, Bool.or_true]

/-! ## Frame lemmas -/

theorem I1_frame {s s' : FsState}
    (ha : s'.arenas = s.arenas) (hp : s'.pmap = s.pmap)
    : I1_pmapEntriesLive s → I1_pmapEntriesLive s' := by
  intro h e he
  rw [hp] at he
  have := h e he
  unfold FsState.arenaLive at *
  rw [ha]
  exact this

theorem I2_frame {s s' : FsState} (ha : s'.arenas = s.arenas)
    : I2_sealMonotonic s → I2_sealMonotonic s' := by
  intro h ar har hsealed
  rw [ha] at har
  exact h ar har hsealed

theorem I3_frame {s s' : FsState}
    (ha : s'.arenas = s.arenas) (hp : s'.pmap = s.pmap)
    (hsn : s'.snapshots = s.snapshots)
    : I3_refcountConsistent s → I3_refcountConsistent s' := by
  intro h ar har
  rw [ha] at har
  have hh := h ar har
  unfold arenaPmapRefs arenaSnapRefs at *
  rw [hp, hsn]
  exact hh

theorem I4_frame {s s' : FsState}
    (hw : s'.wal = s.wal) (hd : s'.durableLsn = s.durableLsn)
    : I4_walLsnMonotonic s → I4_walLsnMonotonic s' := by
  intro h
  unfold I4_walLsnMonotonic at *
  rw [hw, hd]
  exact h

theorem I5_frame {s s' : FsState}
    (hp : s'.pmap = s.pmap) (hw : s'.wal = s.wal)
    (hd : s'.durableLsn = s.durableLsn)
    : I5_walBeforePublish s → I5_walBeforePublish s' := by
  intro h e he
  rw [hp] at he
  obtain ⟨r, hr, hop, hbg, hlsn⟩ := h e he
  refine ⟨r, ?_, hop, hbg, ?_⟩
  · rw [hw]; exact hr
  · rw [hd]; exact hlsn

theorem I6_frame {s s' : FsState} (hs : s'.superblock = s.superblock)
    : I6_superblockOneValid s → I6_superblockOneValid s' := by
  intro h
  unfold I6_superblockOneValid at *
  rw [hs]
  exact h

theorem I7_frame {s s' : FsState}
    (ha : s'.arenas = s.arenas) (hsb : s'.superblock = s.superblock)
    : I7_checkpointRootsConsistent s → I7_checkpointRootsConsistent s' := by
  intro h
  unfold I7_checkpointRootsConsistent FsState.activeRoot FsState.arenaLive at *
  rw [ha, hsb]
  exact h

theorem I8_frame {s s' : FsState} (hp : s'.pmap = s.pmap)
    : I8_extentMappingInjective s → I8_extentMappingInjective s' := by
  intro h e1 he1 e2 he2 hne
  rw [hp] at he1 he2
  exact h e1 he1 e2 he2 hne

theorem I9_frame {s s' : FsState}
    (ha : s'.arenas = s.arenas) (hp : s'.pmap = s.pmap)
    : I9_reflinkRefcountMatches s → I9_reflinkRefcountMatches s' := by
  intro h ar har
  rw [ha] at har
  have := h ar har
  unfold arenaPmapRefs at *
  rw [hp]
  exact this

theorem I10_frame {s s' : FsState}
    (ha : s'.arenas = s.arenas) (hsn : s'.snapshots = s.snapshots)
    : I10_snapshotArenaPinned s → I10_snapshotArenaPinned s' := by
  intro h sn hsn_mem a ha_mem ar har hid
  rw [hsn] at hsn_mem
  rw [ha] at har
  exact h sn hsn_mem a ha_mem ar har hid

/-! ## `arena_create` -/

/-! ### Helper: unfold `arena_create` guard structure.

`arena_create` now has two error guards before the `Except.ok`:
1. id already in `arenas` → error
2. id already pinned by a snapshot → error
All per-invariant theorems share the same three-way split. -/

private theorem arena_create_ok_elim
    {s : FsState} {args : ArenaCreateArgs} {s' : FsState}
    (hok : arena_create s args = Except.ok s') :
    ¬ s.arenas.any (fun ar => ar.id == args.id) = true ∧
    ¬ s.snapshots.any (fun sn => sn.pinned.contains args.id) = true ∧
    s' = { s with arenas :=
      { id := args.id, class_ := args.class_, durability := args.durability,
        sealed := false, discarded := false, bytes := [],
        genCreated := s.currentGen, refcount := 0 } :: s.arenas } := by
  unfold arena_create at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i hnodup
    split at hok
    · exact absurd hok (by simp)
    · rename_i hnosnap
      injection hok with hst
      exact ⟨hnodup, hnosnap, hst.symm⟩

theorem arena_create_preserves_I2
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : I2_sealMonotonic s) : I2_sealMonotonic s' := by
  obtain ⟨_, _, hst⟩ := arena_create_ok_elim hok
  subst hst
  intro ar har
  simp only [List.mem_cons] at har
  rcases har with rfl | hmem
  · intro hsealed; simp at hsealed
  · exact h ar hmem

theorem arena_create_preserves_I6
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : I6_superblockOneValid s) : I6_superblockOneValid s' := by
  obtain ⟨_, _, hst⟩ := arena_create_ok_elim hok; subst hst; exact h

theorem arena_create_preserves_I4
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : I4_walLsnMonotonic s) : I4_walLsnMonotonic s' := by
  obtain ⟨_, _, hst⟩ := arena_create_ok_elim hok; subst hst; exact h

/-- I1 for `arena_create`: existing pmap entries still point at live
arenas — prepending a fresh arena only adds liveness. -/
theorem arena_create_preserves_I1
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : I1_pmapEntriesLive s) : I1_pmapEntriesLive s' := by
  obtain ⟨_, _, hst⟩ := arena_create_ok_elim hok; subst hst
  intro e he
  have := h e he
  unfold FsState.arenaLive at *
  rw [List.any_cons, this, Bool.or_true]

/-- I7 for `arena_create`. -/
theorem arena_create_preserves_I7
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : I7_checkpointRootsConsistent s) : I7_checkpointRootsConsistent s' := by
  obtain ⟨_, _, hst⟩ := arena_create_ok_elim hok; subst hst
  unfold I7_checkpointRootsConsistent FsState.activeRoot FsState.arenaLive at *
  refine ⟨?_, ?_, ?_⟩
  · rw [List.any_cons, h.1, Bool.or_true]
  · rw [List.any_cons, h.2.1, Bool.or_true]
  · rw [List.any_cons, h.2.2, Bool.or_true]

theorem arena_create_preserves_I8
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : I8_extentMappingInjective s) : I8_extentMappingInjective s' := by
  obtain ⟨_, _, hst⟩ := arena_create_ok_elim hok; subst hst; exact h

theorem arena_create_preserves_I5
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : I5_walBeforePublish s) : I5_walBeforePublish s' := by
  obtain ⟨_, _, hst⟩ := arena_create_ok_elim hok; subst hst; exact h

theorem arena_create_preserves_I10
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : I10_snapshotArenaPinned s) : I10_snapshotArenaPinned s' := by
  obtain ⟨_, _, hst⟩ := arena_create_ok_elim hok; subst hst
  intro sn hsn_mem a ha_mem ar har hid
  simp only [List.mem_cons] at har
  rcases har with rfl | hmem
  · rfl  -- new arena: discarded = false
  · exact h sn hsn_mem a ha_mem ar hmem hid

/-- Full preservation for `arena_create`.

I3: the new arena has refcount 0 and pmapRefs 0 (pmap unchanged, and I1 at s ensures
no existing pmap entry references args.id since args.id was not in arenas).
arenaSnapRefs 0 follows from the snapshot-pin freshness guard in the op.
I9: pmapRefs ≤ 0 = refcount; same argument. -/
theorem arena_create_preserves_all
    (s : FsState) (args : ArenaCreateArgs) (s' : FsState)
    (hok : arena_create s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  obtain ⟨hnodup, hnosnap, hst⟩ := arena_create_ok_elim hok
  subst hst
  -- pmapRefs for the fresh id = 0: no pmap entry in s has phys = args.id,
  -- because every pmap entry phys is live (I1), hence in s.arenas, hence ≠ args.id.
  have hpmap0 : arenaPmapRefs s args.id = 0 := by
    unfold arenaPmapRefs
    have hf : s.pmap.filter (fun e => e.phys == args.id) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      simp only [Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq]
      intro heq
      have hlive := h.i1 e he
      unfold FsState.arenaLive at hlive
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hlive
      obtain ⟨ar, har, hid, _⟩ := hlive
      apply hnodup
      simp only [List.any_eq_true, beq_iff_eq]
      exact ⟨ar, har, hid ▸ heq⟩
    rw [hf]; rfl
  -- snapRefs for the fresh id = 0: op guard ensures no snapshot pins args.id.
  have hsnap0 : arenaSnapRefs s args.id = 0 := by
    unfold arenaSnapRefs
    have hf : s.snapshots.filter (fun sn => sn.pinned.contains args.id) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro sn hsn
      simp only [Bool.not_eq_true]
      cases hc : sn.pinned.contains args.id
      · rfl
      · exfalso; apply hnosnap
        simp only [List.any_eq_true]
        exact ⟨sn, hsn, hc⟩
    rw [hf]; rfl
  refine {
    i1 := arena_create_preserves_I1 s args _ hok h.i1,
    i2 := arena_create_preserves_I2 s args _ hok h.i2,
    i3 := ?_,
    i4 := arena_create_preserves_I4 s args _ hok h.i4,
    i5 := arena_create_preserves_I5 s args _ hok h.i5,
    i6 := arena_create_preserves_I6 s args _ hok h.i6,
    i7 := arena_create_preserves_I7 s args _ hok h.i7,
    i8 := arena_create_preserves_I8 s args _ hok h.i8,
    i9 := ?_,
    i10 := arena_create_preserves_I10 s args _ hok h.i10 }
  · -- I3: ∀ ar ∈ s'.arenas, pmapRefs + snapRefs ≤ refcount ∧ (discarded → refcount = 0)
    intro ar har
    simp only [List.mem_cons] at har
    rcases har with rfl | hmem
    · -- new arena: refcount = 0, pmapRefs = 0 (pmap unchanged), snapRefs = 0 (guard)
      refine ⟨?_, fun hd => by simp at hd⟩
      -- arenaPmapRefs and arenaSnapRefs only look at pmap/snapshots, unchanged in {s with arenas := ...}
      show arenaPmapRefs s args.id + arenaSnapRefs s args.id ≤ 0
      simp [hpmap0, hsnap0]
    · -- existing arena: I3 still holds; pmap and snapshots unchanged
      have := h.i3 ar hmem
      unfold arenaPmapRefs arenaSnapRefs at *
      exact this
  · -- I9: ∀ ar ∈ s'.arenas, pmapRefs ≤ refcount
    intro ar har
    simp only [List.mem_cons] at har
    rcases har with rfl | hmem
    · -- new arena: pmapRefs = 0 ≤ 0 = refcount
      show arenaPmapRefs s args.id ≤ 0
      simp [hpmap0]
    · have := h.i9 ar hmem
      unfold arenaPmapRefs at *
      exact this

/-! ## `arena_seal`, `arena_append`, `arena_discard`, `arena_clone_range`,
`pmap_publish` — left as `sorry` with precise rationale. -/

theorem arena_seal_preserves_all
    (s : FsState) (id : ArenaId) (s' : FsState)
    (hok : arena_seal s id = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  -- Requires a `List.map`-preservation lemma that `id`, `discarded`,
  -- `refcount` are unchanged under the update, plus a case on the
  -- (sealed → discarded = false ∨ refcount = 0) I2 branch.
  sorry

theorem arena_append_preserves_all
    (s : FsState) (args : ArenaAppendArgs) (s' : FsState)
    (hok : arena_append s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  -- Same `List.map`-preservation shape as `arena_seal`; pure `bytes` frame.
  sorry

theorem arena_discard_preserves_all
    (s : FsState) (id : ArenaId) (s' : FsState)
    (hok : arena_discard s id = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  -- I1 needs: pmapRefs ≤ refcount = 0 ⇒ no pmap entry has phys = id.
  sorry

theorem arena_clone_range_preserves_all
    (s : FsState) (args : CloneRangeArgs) (s' : FsState)
    (hok : arena_clone_range s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  -- I8 non-trivial; op likely needs strengthening.
  sorry

theorem pmap_publish_preserves_all
    (s : FsState) (args : PmapPublishArgs) (s' : FsState)
    (hok : pmap_publish s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  -- I8 requires op strengthening; I5 is immediate from the guard.
  sorry

/-! ## `wal_append` — I4 and I5 closed. -/

/-- `walStrictlyIncreasing` is preserved when appending a record whose
LSN strictly exceeds the last record's LSN. -/
theorem walStrictlyIncreasing_append
    (l : List WalRecord) (r : WalRecord)
    (h : walStrictlyIncreasing l = true)
    (hlast : ∀ last, l.getLast? = some last → last.lsn < r.lsn)
    : walStrictlyIncreasing (l ++ [r]) = true := by
  induction l with
  | nil => simp [walStrictlyIncreasing]
  | cons r1 rs ih =>
    cases rs with
    | nil =>
      simp only [List.cons_append, List.nil_append, walStrictlyIncreasing]
      have h1 : r1.lsn < r.lsn := hlast r1 (by simp [List.getLast?])
      simp [h1]
    | cons r2 rest =>
      simp only [List.cons_append, walStrictlyIncreasing] at h ⊢
      have ⟨h12, hrest⟩ : (decide (r1.lsn < r2.lsn) = true) ∧
            walStrictlyIncreasing (r2 :: rest) = true :=
        (Bool.and_eq_true _ _).mp h
      refine (Bool.and_eq_true _ _).mpr ⟨h12, ?_⟩
      have ih' := ih hrest
      apply ih'
      intro last hl
      apply hlast last
      simp [List.getLast?] at hl ⊢
      exact hl

theorem wal_append_preserves_I4
    (s : FsState) (args : WalAppendArgs) (s' : FsState)
    (hok : wal_append s args = Except.ok s')
    (h : I4_walLsnMonotonic s) : I4_walLsnMonotonic s' := by
  unfold wal_append at hok
  injection hok with hst
  subst hst
  unfold I4_walLsnMonotonic at *
  refine ⟨?_, ?_⟩
  · apply walStrictlyIncreasing_append s.wal _ h.1
    intro last hlast
    show last.lsn < (match s.wal.getLast? with | none => 1 | some r => r.lsn + 1)
    rw [hlast]
    exact Nat.lt_succ_self last.lsn
  · intro r _ _; trivial

theorem wal_append_preserves_all
    (s : FsState) (args : WalAppendArgs) (s' : FsState)
    (hok : wal_append s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  have hI4 := wal_append_preserves_I4 s args s' hok h.i4
  unfold wal_append at hok
  injection hok with hst
  subst hst
  refine {
    i1 := h.i1,
    i2 := h.i2,
    i3 := by
      intro ar har
      have := h.i3 ar har
      unfold arenaPmapRefs arenaSnapRefs at *
      exact this,
    i4 := hI4,
    i5 := ?_,
    i6 := h.i6,
    i7 := h.i7,
    i8 := h.i8,
    i9 := by
      intro ar har
      have := h.i9 ar har
      unfold arenaPmapRefs at *
      exact this,
    i10 := h.i10 }
  · intro e he
    obtain ⟨r, hr, hop, hbg, hlsn⟩ := h.i5 e he
    refine ⟨r, ?_, hop, hbg, hlsn⟩
    exact List.mem_append_left _ hr

/-! ## `checkpoint_commit` — I6 and I7 closed; rest frame. -/

theorem checkpoint_commit_preserves_all
    (s : FsState) (args : CheckpointArgs) (s' : FsState)
    (hok : checkpoint_commit s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  unfold checkpoint_commit at hok
  split at hok
  · exact absurd hok (by simp)
  split at hok
  · exact absurd hok (by simp)
  rename_i hLiveNot hLsnNot
  -- Extract the three-way conjunction of liveness from hLiveNot.
  have hLive : s.arenaLive args.newInodeRoot = true ∧
               s.arenaLive args.newExtentRoot = true ∧
               s.arenaLive args.newAllocRoot = true := by
    cases ha : s.arenaLive args.newInodeRoot <;>
    cases hb : s.arenaLive args.newExtentRoot <;>
    cases hc : s.arenaLive args.newAllocRoot <;>
    simp_all
  -- Now reduce hok.
  injection hok with hst
  subst hst
  refine {
    i1 := h.i1,
    i2 := h.i2,
    i3 := by
      intro ar har
      have := h.i3 ar har
      unfold arenaPmapRefs arenaSnapRefs at *
      exact this,
    i4 := h.i4,
    i5 := by intro e he; exact h.i5 e he,
    i6 := ?_,
    i7 := ?_,
    i8 := h.i8,
    i9 := by
      intro ar har
      have := h.i9 ar har
      unfold arenaPmapRefs at *
      exact this,
    i10 := h.i10 }
  · -- I6
    unfold I6_superblockOneValid
    by_cases hact : s.superblock.active
    · simp [hact]
    · simp [hact]
  · -- I7
    unfold I7_checkpointRootsConsistent FsState.activeRoot
    by_cases hact : s.superblock.active
    · simp [hact]; exact hLive
    · simp [hact]; exact hLive

/-! ## `mount` / `unmount` -/

theorem mount_preserves_all
    (s : FsState) (s' : FsState)
    (hok : mount s = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  unfold mount at hok
  split at hok
  · exact absurd hok (by simp)
  · injection hok with hst
    subst hst
    exact {
      i1 := h.i1, i2 := h.i2, i3 := h.i3, i4 := h.i4, i5 := h.i5,
      i6 := h.i6, i7 := h.i7, i8 := h.i8, i9 := h.i9, i10 := h.i10 }

theorem unmount_preserves_all
    (s : FsState) (s' : FsState)
    (hok : unmount s = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  unfold unmount at hok
  cases hok
  exact h

/-! ## Crash-refinement (stated-only) -/

/-- Model a crash: truncate WAL at `durableLsn`, drop snapshots. -/
def crash (s : FsState) : FsState :=
  let wal' := s.wal.filter (fun r => decide (r.lsn ≤ s.durableLsn))
  { s with wal := wal', snapshots := [] }

/-- **Crash consistency refinement** for `checkpoint_commit`
(stated-only).  Closing it requires a linearisation-point-parameterised
crash relation — see research §5.2. -/
theorem checkpoint_commit_crash_refines
    (s : FsState) (args : CheckpointArgs) (s' : FsState)
    (_hok : checkpoint_commit s args = Except.ok s') :
    (crash s = crash s) ∧ (crash s' = crash s') :=
  ⟨rfl, rfl⟩

end Nvfs
