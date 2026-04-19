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

private theorem findArena_id {s : FsState} {id : ArenaId} {ar : Arena}
    (hfind : s.findArena id = some ar) : ar.id = id := by
  unfold FsState.findArena at hfind
  have hpred := List.find?_some hfind
  simp [beq_iff_eq] at hpred
  exact hpred

private theorem pmapRefs_pos {s : FsState} {id : ArenaId} {e : PmapEntry}
    (he : e ∈ s.pmap) (heq : e.phys = id) : 1 ≤ arenaPmapRefs s id := by
  unfold arenaPmapRefs
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  have hnil := List.eq_nil_iff_length_eq_zero.mpr h0
  have := List.filter_eq_nil_iff.mp hnil e he
  simp [← heq] at this

private theorem arenaLive_map_ne {s : FsState} {ar ar' : Arena} {a : ArenaId}
    (hne : a ≠ ar.id) (hlive : s.arenaLive a = true) :
    FsState.arenaLive { s with arenas := s.arenas.map (fun x => if x.id == ar.id then ar' else x) } a = true := by
  unfold FsState.arenaLive at *
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at *
  obtain ⟨b, hb, hbid, hbnotd⟩ := hlive
  refine ⟨b, List.mem_map.mpr ⟨b, hb, ?_⟩, hbid, hbnotd⟩
  -- show: (if b.id == ar.id then ar' else b) = b
  have hbne : b.id ≠ ar.id := fun heq => hne (hbid ▸ heq)
  simp [hbne]

/-! ## `arena_seal`, `arena_append`, `arena_discard`, `arena_clone_range`,
`pmap_publish` — left as `sorry` with precise rationale. -/

theorem arena_seal_preserves_all
    (s : FsState) (id : ArenaId) (s' : FsState)
    (hok : arena_seal s id = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  unfold arena_seal at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i ar hfind
    have harid : ar.id = id := findArena_id hfind
    have har_mem : ar ∈ s.arenas := List.mem_of_find?_eq_some hfind
    split at hok
    · -- idempotent: already sealed, s' = s
      injection hok with hst; subst hst; exact h
    · rename_i hnotsealed
      split at hok
      · exact absurd hok (by simp)
      · rename_i hnotdisc
        have hnd : ar.discarded = false := by simp only [Bool.not_eq_true] at hnotdisc; exact hnotdisc
        injection hok with hst; subst hst
        -- s' = { s with arenas := s.arenas.map (fun x => if x.id == ar.id then { ar with sealed := true } else x) }
        -- pmap, snapshots, wal, durableLsn, superblock all unchanged
        refine {
          i1 := ?_, i2 := ?_, i3 := ?_,
          i4 := I4_frame rfl rfl h.i4,
          i5 := I5_frame rfl rfl rfl h.i5,
          i6 := I6_frame rfl h.i6,
          i7 := ?_, i8 := I8_frame rfl h.i8,
          i9 := ?_, i10 := ?_ }
        · -- I1: arenaLive preserved (discarded unchanged for all arenas)
          intro e he
          have hlive := h.i1 e he
          unfold FsState.arenaLive at *
          simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at *
          obtain ⟨b, hb, hbid, hbnotd⟩ := hlive
          by_cases hbne : b.id = ar.id
          · refine ⟨{ ar with sealed := true }, ?_, hbne ▸ hbid, by simp [hnd]⟩
            apply List.mem_map.mpr; exact ⟨b, hb, by simp [hbne]⟩
          · refine ⟨b, ?_, hbid, hbnotd⟩
            apply List.mem_map.mpr; exact ⟨b, hb, by simp [hbne]⟩
        · -- I2: sealed monotonicity
          intro a ha hsealed
          simp only [List.mem_map] at ha
          obtain ⟨b, hb, hba⟩ := ha
          by_cases hbid : b.id = ar.id
          · have hmap : (if b.id == ar.id then { ar with sealed := true } else b) =
                { ar with sealed := true } := by simp [hbid]
            rw [hmap] at hba; subst hba
            -- sealed = true, discarded = false (hnd)
            exact Or.inl hnd
          · have hmap : (if b.id == ar.id then { ar with sealed := true } else b) = b := by
              simp [hbid]
            rw [hmap] at hba; subst hba
            exact h.i2 b hb hsealed
        · -- I3: refcount consistency (pmap, snapshots, refcount all unchanged)
          intro a ha
          simp only [List.mem_map] at ha
          obtain ⟨b, hb, hba⟩ := ha
          by_cases hbid : b.id = ar.id
          · have hmap : (if b.id == ar.id then { ar with sealed := true } else b) =
                { ar with sealed := true } := by simp [hbid]
            rw [hmap] at hba; subst hba
            have h3 := h.i3 ar har_mem
            unfold arenaPmapRefs arenaSnapRefs at *; exact h3
          · have hmap : (if b.id == ar.id then { ar with sealed := true } else b) = b := by
              simp [hbid]
            rw [hmap] at hba; subst hba
            have h3 := h.i3 b hb
            unfold arenaPmapRefs arenaSnapRefs at *; exact h3
        · -- I7: checkpoint roots still live (superblock unchanged, only sealed bit changed)
          unfold I7_checkpointRootsConsistent
          -- activeRoot only reads superblock which is unchanged
          have hactEq : (({ s with arenas := s.arenas.map (fun x => if x.id == ar.id then
                { ar with sealed := true } else x) } : FsState).activeRoot) = s.activeRoot := rfl
          have har'live : ∀ rid : ArenaId, rid = ar.id →
              FsState.arenaLive ({ s with arenas := s.arenas.map (fun x => if x.id == ar.id then
                { ar with sealed := true } else x) } : FsState) rid = true := by
            intro rid hrid; subst hrid
            unfold FsState.arenaLive
            simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
            exact ⟨{ ar with sealed := true }, List.mem_map.mpr ⟨ar, har_mem, by simp⟩, rfl, by simp [hnd]⟩
          rw [hactEq]
          refine ⟨?_, ?_, ?_⟩
          · by_cases heq : s.activeRoot.inodeRoot = ar.id
            · exact har'live _ heq
            · exact arenaLive_map_ne heq h.i7.1
          · by_cases heq : s.activeRoot.extentRoot = ar.id
            · exact har'live _ heq
            · exact arenaLive_map_ne heq h.i7.2.1
          · by_cases heq : s.activeRoot.allocRoot = ar.id
            · exact har'live _ heq
            · exact arenaLive_map_ne heq h.i7.2.2
        · -- I9: pmapRefs ≤ refcount (pmap, refcount unchanged)
          intro a ha
          simp only [List.mem_map] at ha
          obtain ⟨b, hb, hba⟩ := ha
          by_cases hbid : b.id = ar.id
          · have hmap : (if b.id == ar.id then { ar with sealed := true } else b) =
                { ar with sealed := true } := by simp [hbid]
            rw [hmap] at hba; subst hba
            have := h.i9 ar har_mem
            unfold arenaPmapRefs at *; exact this
          · have hmap : (if b.id == ar.id then { ar with sealed := true } else b) = b := by
              simp [hbid]
            rw [hmap] at hba; subst hba
            have := h.i9 b hb
            unfold arenaPmapRefs at *; exact this
        · -- I10: snapshot-pinned arenas not discarded (discarded unchanged)
          intro sn hsn a ha_mem a' ha' hid
          simp only [List.mem_map] at ha'
          obtain ⟨b, hb, hba⟩ := ha'
          by_cases hbid : b.id = ar.id
          · have hmap : (if b.id == ar.id then { ar with sealed := true } else b) =
                { ar with sealed := true } := by simp [hbid]
            rw [hmap] at hba; subst hba; exact hnd
          · have hmap : (if b.id == ar.id then { ar with sealed := true } else b) = b := by
              simp [hbid]
            rw [hmap] at hba; subst hba; exact h.i10 sn hsn a ha_mem b hb hid

theorem arena_append_preserves_all
    (s : FsState) (args : ArenaAppendArgs) (s' : FsState)
    (hok : arena_append s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  unfold arena_append at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i ar hfind
    have harid : ar.id = args.id := findArena_id hfind
    have har_mem : ar ∈ s.arenas := List.mem_of_find?_eq_some hfind
    split at hok
    · exact absurd hok (by simp)
    · rename_i hnotsealed
      split at hok
      · exact absurd hok (by simp)
      · rename_i hnotdisc
        have hnd : ar.discarded = false := by simp only [Bool.not_eq_true] at hnotdisc; exact hnotdisc
        injection hok with hst; subst hst
        -- s' = { s with arenas := s.arenas.map (fun x => if x.id == ar.id then { ar with bytes := ... } else x) }
        -- only bytes changes; no invariant inspects bytes; pmap, snapshots, wal, superblock all unchanged
        refine {
          i1 := ?_, i2 := ?_, i3 := ?_,
          i4 := I4_frame rfl rfl h.i4,
          i5 := I5_frame rfl rfl rfl h.i5,
          i6 := I6_frame rfl h.i6,
          i7 := ?_, i8 := I8_frame rfl h.i8,
          i9 := ?_, i10 := ?_ }
        · -- I1: arenaLive preserved (id, discarded unchanged for all arenas)
          intro e he
          have hlive := h.i1 e he
          unfold FsState.arenaLive at *
          simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at *
          obtain ⟨b, hb, hbid, hbnotd⟩ := hlive
          by_cases hbne : b.id = ar.id
          · refine ⟨{ ar with bytes := ar.bytes ++ args.bytes }, ?_, hbne ▸ hbid, by simp [hnd]⟩
            apply List.mem_map.mpr; exact ⟨b, hb, by simp [hbne]⟩
          · refine ⟨b, ?_, hbid, hbnotd⟩
            apply List.mem_map.mpr; exact ⟨b, hb, by simp [hbne]⟩
        · -- I2: sealed monotonicity (sealed, discarded, refcount unchanged)
          intro a ha hsealed
          simp only [List.mem_map] at ha
          obtain ⟨b, hb, hba⟩ := ha
          by_cases hbid : b.id = ar.id
          · have hmap : (if b.id == ar.id then { ar with bytes := ar.bytes ++ args.bytes } else b) =
                { ar with bytes := ar.bytes ++ args.bytes } := by simp [hbid]
            rw [hmap] at hba; subst hba
            exact h.i2 ar har_mem hsealed
          · have hmap : (if b.id == ar.id then { ar with bytes := ar.bytes ++ args.bytes } else b) = b := by
              simp [hbid]
            rw [hmap] at hba; subst hba
            exact h.i2 b hb hsealed
        · -- I3: refcount consistency (pmap, snapshots, refcount all unchanged)
          intro a ha
          simp only [List.mem_map] at ha
          obtain ⟨b, hb, hba⟩ := ha
          by_cases hbid : b.id = ar.id
          · have hmap : (if b.id == ar.id then { ar with bytes := ar.bytes ++ args.bytes } else b) =
                { ar with bytes := ar.bytes ++ args.bytes } := by simp [hbid]
            rw [hmap] at hba; subst hba
            have h3 := h.i3 ar har_mem
            unfold arenaPmapRefs arenaSnapRefs at *; exact h3
          · have hmap : (if b.id == ar.id then { ar with bytes := ar.bytes ++ args.bytes } else b) = b := by
              simp [hbid]
            rw [hmap] at hba; subst hba
            have h3 := h.i3 b hb
            unfold arenaPmapRefs arenaSnapRefs at *; exact h3
        · -- I7: checkpoint roots still live (superblock unchanged, only bytes changed)
          unfold I7_checkpointRootsConsistent
          -- activeRoot only reads superblock which is unchanged
          have hactEq : (({ s with arenas := s.arenas.map (fun x => if x.id == ar.id then
                { ar with bytes := ar.bytes ++ args.bytes } else x) } : FsState).activeRoot) = s.activeRoot := rfl
          have har'live : ∀ rid : ArenaId, rid = ar.id →
              FsState.arenaLive ({ s with arenas := s.arenas.map (fun x => if x.id == ar.id then
                { ar with bytes := ar.bytes ++ args.bytes } else x) } : FsState) rid = true := by
            intro rid hrid; subst hrid
            unfold FsState.arenaLive
            simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
            exact ⟨{ ar with bytes := ar.bytes ++ args.bytes }, List.mem_map.mpr ⟨ar, har_mem, by simp⟩, rfl, by simp [hnd]⟩
          rw [hactEq]
          refine ⟨?_, ?_, ?_⟩
          · by_cases heq : s.activeRoot.inodeRoot = ar.id
            · exact har'live _ heq
            · exact arenaLive_map_ne heq h.i7.1
          · by_cases heq : s.activeRoot.extentRoot = ar.id
            · exact har'live _ heq
            · exact arenaLive_map_ne heq h.i7.2.1
          · by_cases heq : s.activeRoot.allocRoot = ar.id
            · exact har'live _ heq
            · exact arenaLive_map_ne heq h.i7.2.2
        · -- I9: pmapRefs ≤ refcount (pmap, refcount unchanged)
          intro a ha
          simp only [List.mem_map] at ha
          obtain ⟨b, hb, hba⟩ := ha
          by_cases hbid : b.id = ar.id
          · have hmap : (if b.id == ar.id then { ar with bytes := ar.bytes ++ args.bytes } else b) =
                { ar with bytes := ar.bytes ++ args.bytes } := by simp [hbid]
            rw [hmap] at hba; subst hba
            have := h.i9 ar har_mem
            unfold arenaPmapRefs at *; exact this
          · have hmap : (if b.id == ar.id then { ar with bytes := ar.bytes ++ args.bytes } else b) = b := by
              simp [hbid]
            rw [hmap] at hba; subst hba
            have := h.i9 b hb
            unfold arenaPmapRefs at *; exact this
        · -- I10: snapshot-pinned arenas not discarded (discarded unchanged)
          intro sn hsn a ha_mem a' ha' hid
          simp only [List.mem_map] at ha'
          obtain ⟨b, hb, hba⟩ := ha'
          by_cases hbid : b.id = ar.id
          · have hmap : (if b.id == ar.id then { ar with bytes := ar.bytes ++ args.bytes } else b) =
                { ar with bytes := ar.bytes ++ args.bytes } := by simp [hbid]
            rw [hmap] at hba; subst hba; exact hnd
          · have hmap : (if b.id == ar.id then { ar with bytes := ar.bytes ++ args.bytes } else b) = b := by
              simp [hbid]
            rw [hmap] at hba; subst hba; exact h.i10 sn hsn a ha_mem b hb hid

theorem arena_discard_preserves_all
    (s : FsState) (id : ArenaId) (s' : FsState)
    (hok : arena_discard s id = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  unfold arena_discard at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i ar hfind
    have harid : ar.id = id := findArena_id hfind
    split at hok
    · exact absurd hok (by simp)
    · rename_i href
      have href0 : ar.refcount = 0 := Nat.eq_zero_of_not_pos href
      split at hok
      · exact absurd hok (by simp)
      · rename_i hnosnap
        split at hok
        · exact absurd hok (by simp)
        · rename_i hnoroot
          injection hok with hst; subst hst
          have har_mem : ar ∈ s.arenas := List.mem_of_find?_eq_some hfind
          have hpmap0 : arenaPmapRefs s ar.id = 0 := by
            have := h.i9 ar har_mem; omega
          have hsnap0 : arenaSnapRefs s ar.id = 0 := by
            unfold arenaSnapRefs
            have hf : s.snapshots.filter (fun sn => sn.pinned.contains ar.id) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro sn hsn
              simp only [Bool.not_eq_true]
              cases hc : sn.pinned.contains ar.id
              · rfl
              · exfalso
                apply hnosnap
                rw [List.any_eq_true]
                exact ⟨sn, hsn, harid ▸ hc⟩
            rw [hf]; rfl
          -- Extract the three ≠ constraints from hnoroot
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hnoroot
          have hnotInodeRoot : ar.id ≠ s.activeRoot.inodeRoot := by
            intro heq; apply hnoroot; left; left; exact harid ▸ heq
          have hnotExtentRoot : ar.id ≠ s.activeRoot.extentRoot := by
            intro heq; apply hnoroot; left; right; exact harid ▸ heq
          have hnotAllocRoot : ar.id ≠ s.activeRoot.allocRoot := by
            intro heq; apply hnoroot; right; exact harid ▸ heq
          refine {
            i1 := ?_, i2 := ?_, i3 := ?_,
            i4 := I4_frame rfl rfl h.i4,
            i5 := I5_frame rfl rfl rfl h.i5,
            i6 := I6_frame rfl h.i6,
            i7 := ?_, i8 := I8_frame rfl h.i8,
            i9 := ?_, i10 := ?_ }
          · -- I1: pmap entries still live (discarded arena has pmapRefs=0, so not in pmap)
            intro e he
            have hlive := h.i1 e he
            unfold FsState.arenaLive at *
            simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at *
            obtain ⟨a, ha, haid, hanotd⟩ := hlive
            by_cases heq : a.id = ar.id
            · -- a is the discarded arena; e.phys = ar.id; but pmapRefs s ar.id = 0 → contradiction
              exact absurd (pmapRefs_pos he (haid.symm.trans heq)) (by omega)
            · exact ⟨a, List.mem_map.mpr ⟨a, ha, by simp [show a.id ≠ ar.id from heq]⟩, haid, hanotd⟩
          · -- I2: sealed → discarded=false ∨ refcount=0
            intro a ha hsealed
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            split at hba
            · subst hba; right; exact href0
            · subst hba; exact h.i2 b hb hsealed
          · -- I3: refcount consistency
            intro a ha
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            split at hba
            · subst hba
              refine ⟨?_, fun _ => href0⟩
              -- arenaPmapRefs/arenaSnapRefs only access .pmap/.snapshots, unchanged under arenas-map
              have hpm : arenaPmapRefs { s with
                    arenas := s.arenas.map (fun x => if x.id == ar.id then
                      { ar with discarded := true } else x) } ar.id =
                  arenaPmapRefs s ar.id := by unfold arenaPmapRefs; rfl
              have hsn : arenaSnapRefs { s with
                    arenas := s.arenas.map (fun x => if x.id == ar.id then
                      { ar with discarded := true } else x) } ar.id =
                  arenaSnapRefs s ar.id := by unfold arenaSnapRefs; rfl
              rw [hpm, hsn]
              simp [hpmap0, hsnap0]
            · subst hba
              have := h.i3 b hb
              unfold arenaPmapRefs arenaSnapRefs at *; exact this
          · -- I7: checkpoint roots still live (root ≠ discarded arena)
            -- superblock unchanged, so activeRoot of new state = s.activeRoot
            unfold I7_checkpointRootsConsistent
            simp only [FsState.activeRoot]
            exact ⟨arenaLive_map_ne (Ne.symm hnotInodeRoot) h.i7.1,
                   arenaLive_map_ne (Ne.symm hnotExtentRoot) h.i7.2.1,
                   arenaLive_map_ne (Ne.symm hnotAllocRoot) h.i7.2.2⟩
          · -- I9: pmapRefs ≤ refcount
            intro a ha
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            split at hba
            · subst hba
              have hq : arenaPmapRefs { s with
                    arenas := s.arenas.map (fun x => if x.id == ar.id then
                      { ar with discarded := true } else x) } ar.id =
                  arenaPmapRefs s ar.id := by unfold arenaPmapRefs; rfl
              rw [hq]; simp [hpmap0]
            · subst hba
              have := h.i9 b hb
              unfold arenaPmapRefs at *; exact this
          · -- I10: snapshot-pinned arenas not discarded
            intro sn hsn a ha_mem a' ha' hid
            simp only [List.mem_map] at ha'
            obtain ⟨b, hb, hba⟩ := ha'
            split at hba
            · subst hba
              exfalso
              apply hnosnap
              simp only [List.any_eq_true]
              -- hid : { ar with discarded := true }.id = a, i.e., ar.id = a
              -- harid : ar.id = id
              -- ha_mem : a ∈ sn.pinned
              -- need: ∃ sn ∈ s.snapshots, sn.pinned.contains id = true
              have haid : a = id := by simp at hid; rw [← harid, hid]
              exact ⟨sn, hsn, haid ▸ List.elem_eq_true_of_mem ha_mem⟩
            · subst hba; exact h.i10 sn hsn a ha_mem b hb hid

-- Helper: arenaPmapRefs after prepending an entry with phys = id increases by 1
private theorem arenaPmapRefs_cons_eq {s : FsState} {e : PmapEntry} {a : ArenaId}
    (heq : e.phys = a) :
    arenaPmapRefs { s with pmap := e :: s.pmap } a = arenaPmapRefs s a + 1 := by
  unfold arenaPmapRefs
  simp only [List.filter_cons, ← heq, beq_self_eq_true]
  simp

-- Helper: arenaPmapRefs after prepending an entry with phys ≠ id is unchanged
private theorem arenaPmapRefs_cons_ne {s : FsState} {e : PmapEntry} {a : ArenaId}
    (hne : e.phys ≠ a) :
    arenaPmapRefs { s with pmap := e :: s.pmap } a = arenaPmapRefs s a := by
  unfold arenaPmapRefs
  simp only [List.filter_cons, beq_iff_eq]
  simp [hne]

-- Helper: arenas.map only changes the matched arena; snapshots/pmap unchanged
private theorem arenaSnapRefs_map_eq {s : FsState} {ar ar' : Arena} {a : ArenaId} :
    arenaSnapRefs { s with arenas := s.arenas.map (fun x => if x.id == ar.id then ar' else x) } a =
    arenaSnapRefs s a := by
  unfold arenaSnapRefs; rfl

theorem arena_clone_range_preserves_all
    (s : FsState) (args : CloneRangeArgs) (s' : FsState)
    (hok : arena_clone_range s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  unfold arena_clone_range at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i ar hfind
    split at hok
    · exact absurd hok (by simp)
    · rename_i hnotdisc
      split at hok
      · exact absurd hok (by simp)
      · rename_i hwalok
        split at hok
        · exact absurd hok (by simp)
        · rename_i hnoconflict
          injection hok with hst; subst hst
          have har_mem : ar ∈ s.arenas := List.mem_of_find?_eq_some hfind
          have harid : ar.id = args.src := findArena_id hfind
          have hnd : ar.discarded = false := by simp only [Bool.not_eq_true] at hnotdisc; exact hnotdisc
          -- hpmapInc: inline struct literals, no let-bindings
          have hpmapInc : ∀ x : ArenaId, arenaPmapRefs
                { s with
                  arenas := s.arenas.map (fun y => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.dstLogical, phys := args.src, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := true,
                             checksum := args.checksum } :: s.pmap } x =
              arenaPmapRefs s x + (if args.src = x then 1 else 0) := by
            intro x; unfold arenaPmapRefs
            simp only [List.filter_cons, beq_iff_eq]
            by_cases hx : args.src = x <;> simp [hx]
          refine {
            i1 := ?_, i2 := ?_, i3 := ?_,
            i4 := I4_frame rfl rfl h.i4,
            i5 := ?_,
            i6 := I6_frame rfl h.i6,
            i7 := ?_, i8 := ?_, i9 := ?_, i10 := ?_ }
          · -- I1: all pmap entries (including the new one) have live phys
            intro en hen
            simp only [List.mem_cons] at hen
            rcases hen with rfl | hmem
            · -- new entry: phys = args.src = ar.id
              unfold FsState.arenaLive
              simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
              refine ⟨{ ar with refcount := ar.refcount + 1 }, ?_, harid, by simp [hnd]⟩
              apply List.mem_map.mpr; exact ⟨ar, har_mem, by simp⟩
            · -- existing entry: was live in s, still live after map
              have hlive := h.i1 en hmem
              unfold FsState.arenaLive at *
              simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at *
              obtain ⟨b, hb, hbid, hbnotd⟩ := hlive
              by_cases heq : b.id = ar.id
              · refine ⟨{ ar with refcount := ar.refcount + 1 }, ?_, heq ▸ hbid, by simp [hnd]⟩
                apply List.mem_map.mpr; exact ⟨b, hb, by simp [heq]⟩
              · refine ⟨b, ?_, hbid, hbnotd⟩
                apply List.mem_map.mpr; exact ⟨b, hb, by simp [heq]⟩
          · -- I2: sealed monotonicity (sealed and discarded unchanged for all arenas)
            intro a ha hsealed
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            -- The map function is: if b.id = ar.id then { ar with refcount+1 } else b
            -- In the matched branch, the mapped value uses ar's fields (not b's)
            by_cases hbid : b.id = ar.id
            · -- mapped to { ar with refcount+1 }: sealed = ar.sealed
              have : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = { ar with refcount := ar.refcount + 1 } := by
                simp [hbid]
              rw [this] at hba; subst hba
              -- hsealed : ar.sealed = true; need: ar.discarded = false ∨ ar.refcount + 1 = 0
              -- ar.refcount + 1 ≠ 0 for Nat, so always take left branch
              exact Or.inl ((h.i2 ar har_mem hsealed).elim id (fun _ => hnd))
            · -- mapped to b itself
              have : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = b := by
                simp [hbid]
              rw [this] at hba; subst hba
              exact h.i2 b hb hsealed
          · -- I3: refcount consistency
            intro a ha
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            by_cases hbid : b.id = ar.id
            · -- target arena: mapped to { ar with refcount+1 }
              have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = { ar with refcount := ar.refcount + 1 } := by
                simp [hbid]
              rw [hmap] at hba; subst hba
              -- a = { ar with refcount+1 }, so a.id = ar.id = args.src
              have hq := hpmapInc ar.id
              rw [if_pos harid.symm] at hq
              have hsneq : arenaSnapRefs
                { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.dstLogical, phys := args.src, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := true,
                             checksum := args.checksum } :: s.pmap } ar.id =
                arenaSnapRefs s ar.id := rfl
              rw [hq, hsneq]
              have h3 := h.i3 ar har_mem
              -- new refcount = ar.refcount + 1; pmapRefs increased by 1
              show arenaPmapRefs s ar.id + 1 + arenaSnapRefs s ar.id ≤ ar.refcount + 1 ∧
                (ar.discarded = true → ar.refcount + 1 = 0)
              exact ⟨by omega, fun hd => absurd hd (by simp [hnd])⟩
            · -- non-target arena: mapped to b itself
              have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = b := by
                simp [hbid]
              rw [hmap] at hba; subst hba
              have h3 := h.i3 b hb
              have hq := hpmapInc b.id
              have hsneq : arenaSnapRefs
                { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.dstLogical, phys := args.src, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := true,
                             checksum := args.checksum } :: s.pmap } b.id =
                arenaSnapRefs s b.id := rfl
              rw [hq, hsneq]
              -- b.id ≠ ar.id = args.src, so the if-branch is 0
              rw [if_neg (show ¬ args.src = b.id from fun h => hbid (harid ▸ h.symm))]
              exact ⟨by omega, fun hd => h3.2 hd⟩
          · -- I5: WAL guard in op ensures the new entry's birthGen is in WAL
            intro en hen
            simp only [List.mem_cons] at hen
            rcases hen with rfl | hmem
            · -- new entry: simp converts hwalok to existential; extract witness
              simp at hwalok
              obtain ⟨r, hr, hop, hbg, hlsn⟩ := hwalok
              exact ⟨r, hr, hop, hbg, hlsn⟩
            · exact h.i5 en hmem
          · -- I7: roots live; arenaLive preserved (only refcount changed, not discarded)
            -- The new state has identical superblock to s, so activeRoot fields are the same.
            -- arenaLive only reads .arenas (monotone under refcount bump).
            unfold I7_checkpointRootsConsistent
            -- new state's activeRoot = s.activeRoot since superblock unchanged
            have hactEq : { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.dstLogical, phys := args.src, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := true,
                             checksum := args.checksum } :: s.pmap }.activeRoot = s.activeRoot := rfl
            -- helper: if a root id = ar.id, the updated arena is still live
            have har'live : ∀ rid : ArenaId, rid = ar.id →
                FsState.arenaLive { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.dstLogical, phys := args.src, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := true,
                             checksum := args.checksum } :: s.pmap } rid = true := by
              intro rid hrid; subst hrid
              unfold FsState.arenaLive
              simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
              refine ⟨{ ar with refcount := ar.refcount + 1 }, ?_, rfl, by simp [hnd]⟩
              apply List.mem_map.mpr; exact ⟨ar, har_mem, by simp⟩
            -- arenaLive only reads .arenas, so pmap extension is transparent
            have hliveEq : ∀ a : ArenaId,
                FsState.arenaLive { s with arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y) } a =
                FsState.arenaLive { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.dstLogical, phys := args.src, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := true,
                             checksum := args.checksum } :: s.pmap } a := by
              intro a; unfold FsState.arenaLive; rfl
            rw [hactEq]
            refine ⟨?_, ?_, ?_⟩
            · by_cases heq : s.activeRoot.inodeRoot = ar.id
              · exact har'live _ heq
              · rw [← hliveEq]; exact arenaLive_map_ne heq h.i7.1
            · by_cases heq : s.activeRoot.extentRoot = ar.id
              · exact har'live _ heq
              · rw [← hliveEq]; exact arenaLive_map_ne heq h.i7.2.1
            · by_cases heq : s.activeRoot.allocRoot = ar.id
              · exact har'live _ heq
              · rw [← hliveEq]; exact arenaLive_map_ne heq h.i7.2.2
          · -- I8: new entry has shared=true; guard prevents non-shared conflicts
            intro e1 he1 e2 he2 hlog
            simp only [List.mem_cons] at he1 he2
            rcases he1 with he1eq | hm1 <;> rcases he2 with he2eq | hm2
            · -- both new: same entry, contradicts hlog
              subst he1eq; subst he2eq; exact absurd rfl hlog
            · -- e1=new, e2=old
              subst he1eq
              -- new entry: phys = args.src, offset = args.offset, shared = true
              by_cases hp : args.src = e2.phys
              · by_cases ho : args.offset = e2.offset
                · -- same (phys,offset), e2 must be shared else guard contradiction
                  have he2sh : e2.shared = true := by
                    cases hc : e2.shared
                    · exfalso; apply hnoconflict
                      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
                                  Bool.not_eq_true]
                      exact ⟨e2, hm2, ⟨hp.symm, ho.symm⟩, by simp [hc]⟩
                    · rfl
                  exact Or.inr (Or.inr ⟨rfl, he2sh⟩)
                · exact Or.inr (Or.inl ho)
              · exact Or.inl hp
            · -- e1=old, e2=new
              subst he2eq
              by_cases hp : e1.phys = args.src
              · by_cases ho : e1.offset = args.offset
                · have he1sh : e1.shared = true := by
                    cases hc : e1.shared
                    · exfalso; apply hnoconflict
                      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
                                  Bool.not_eq_true]
                      exact ⟨e1, hm1, ⟨hp, ho⟩, by simp [hc]⟩
                    · rfl
                  exact Or.inr (Or.inr ⟨he1sh, rfl⟩)
                · exact Or.inr (Or.inl ho)
              · exact Or.inl hp
            · -- both old: use h.i8
              exact h.i8 e1 hm1 e2 hm2 hlog
          · -- I9: pmapRefs ≤ refcount
            intro a ha
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            by_cases hbid : b.id = ar.id
            · -- target arena: refcount +1, pmapRefs +1
              have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = { ar with refcount := ar.refcount + 1 } := by simp [hbid]
              rw [hmap] at hba; subst hba
              have hq := hpmapInc ar.id
              rw [if_pos harid.symm] at hq
              simp only [hq]
              have := h.i9 ar har_mem; omega
            · -- non-target arena
              have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = b := by simp [hbid]
              rw [hmap] at hba; subst hba
              have hq := hpmapInc b.id
              -- b.id ≠ ar.id = args.src, so the if-branch is 0
              rw [if_neg (show ¬ args.src = b.id from fun h => hbid (harid ▸ h.symm))] at hq
              simp only [hq, Nat.add_zero]; exact h.i9 b hb
          · -- I10: snapshot-pinned arenas not discarded (discarded unchanged for all arenas)
            intro sn hsn a ha_mem a' ha' hid
            simp only [List.mem_map] at ha'
            obtain ⟨b, hb, hba⟩ := ha'
            by_cases hbid : b.id = ar.id
            · have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = { ar with refcount := ar.refcount + 1 } := by simp [hbid]
              rw [hmap] at hba; subst hba; exact hnd
            · have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = b := by simp [hbid]
              rw [hmap] at hba; subst hba; exact h.i10 sn hsn a ha_mem b hb hid

theorem pmap_publish_preserves_all
    (s : FsState) (args : PmapPublishArgs) (s' : FsState)
    (hok : pmap_publish s args = Except.ok s')
    (h : AllInvariants s) : AllInvariants s' := by
  unfold pmap_publish at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i hwalok
    split at hok
    · exact absurd hok (by simp)
    · rename_i hnoconflict
      split at hok
      · exact absurd hok (by simp)
      · rename_i ar hfind
        split at hok
        · exact absurd hok (by simp)
        · rename_i hnotdisc
          injection hok with hst; subst hst
          have har_mem : ar ∈ s.arenas := List.mem_of_find?_eq_some hfind
          have harid : ar.id = args.phys := findArena_id hfind
          have hnd : ar.discarded = false := by simp only [Bool.not_eq_true] at hnotdisc; exact hnotdisc
          -- hpmapInc: inline struct literals, no let-bindings
          have hpmapInc : ∀ x : ArenaId, arenaPmapRefs
                { s with
                  arenas := s.arenas.map (fun y => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.logical, phys := args.phys, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := false,
                             checksum := args.checksum } :: s.pmap } x =
              arenaPmapRefs s x + (if args.phys = x then 1 else 0) := by
            intro x; unfold arenaPmapRefs; simp only [List.filter_cons, beq_iff_eq]
            by_cases hx : args.phys = x <;> simp [hx]
          refine {
            i1 := ?_, i2 := ?_, i3 := ?_,
            i4 := I4_frame rfl rfl h.i4,
            i5 := ?_,
            i6 := I6_frame rfl h.i6,
            i7 := ?_, i8 := ?_, i9 := ?_, i10 := ?_ }
          · -- I1: all pmap entries live
            intro en hen
            simp only [List.mem_cons] at hen
            rcases hen with rfl | hmem
            · -- new entry: phys = args.phys = ar.id
              unfold FsState.arenaLive
              simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
              refine ⟨{ ar with refcount := ar.refcount + 1 }, ?_, harid, by simp [hnd]⟩
              apply List.mem_map.mpr; exact ⟨ar, har_mem, by simp⟩
            · have hlive := h.i1 en hmem
              unfold FsState.arenaLive at *
              simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at *
              obtain ⟨b, hb, hbid, hbnotd⟩ := hlive
              by_cases heq : b.id = ar.id
              · refine ⟨{ ar with refcount := ar.refcount + 1 }, ?_, heq ▸ hbid, by simp [hnd]⟩
                apply List.mem_map.mpr; exact ⟨b, hb, by simp [heq]⟩
              · refine ⟨b, ?_, hbid, hbnotd⟩
                apply List.mem_map.mpr; exact ⟨b, hb, by simp [heq]⟩
          · -- I2: sealed monotonicity
            intro a ha hsealed
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            by_cases hbid : b.id = ar.id
            · have : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = { ar with refcount := ar.refcount + 1 } := by simp [hbid]
              rw [this] at hba; subst hba
              exact Or.inl ((h.i2 ar har_mem hsealed).elim id (fun _ => hnd))
            · have : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = b := by simp [hbid]
              rw [this] at hba; subst hba
              exact h.i2 b hb hsealed
          · -- I3: refcount consistency
            intro a ha
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            by_cases hbid : b.id = ar.id
            · have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = { ar with refcount := ar.refcount + 1 } := by simp [hbid]
              rw [hmap] at hba; subst hba
              have hq := hpmapInc ar.id
              rw [if_pos harid.symm] at hq
              have hsneq : arenaSnapRefs
                { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.logical, phys := args.phys, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := false,
                             checksum := args.checksum } :: s.pmap } ar.id =
                arenaSnapRefs s ar.id := rfl
              rw [hq, hsneq]
              have h3 := h.i3 ar har_mem
              have hrc : ({ ar with refcount := ar.refcount + 1 } : Arena).refcount = ar.refcount + 1 := rfl
              have hid2 : ({ ar with refcount := ar.refcount + 1 } : Arena).id = ar.id := rfl
              rw [hid2, hrc]
              exact ⟨by omega, fun hd => absurd hd (by simp [hnd])⟩
            · have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = b := by simp [hbid]
              rw [hmap] at hba; subst hba
              have h3 := h.i3 b hb
              have hq := hpmapInc b.id
              have hsneq : arenaSnapRefs
                { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.logical, phys := args.phys, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := false,
                             checksum := args.checksum } :: s.pmap } b.id =
                arenaSnapRefs s b.id := rfl
              rw [hq, hsneq]
              -- b.id ≠ ar.id = args.phys, so the if-branch is 0
              rw [if_neg (show ¬ args.phys = b.id from fun h => hbid (harid ▸ h.symm))]
              exact ⟨by omega, fun hd => h3.2 hd⟩
          · -- I5: WAL guard gives the witness for the new entry
            intro en hen
            simp only [List.mem_cons] at hen
            rcases hen with rfl | hmem
            · -- new entry: simp converts hwalok to existential; extract witness
              simp at hwalok
              obtain ⟨r, hr, hop, hbg, hlsn⟩ := hwalok
              exact ⟨r, hr, hop, hbg, hlsn⟩
            · exact h.i5 en hmem
          · -- I7: roots live; arenaLive preserved (discarded unchanged)
            unfold I7_checkpointRootsConsistent
            have hactEq : { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.logical, phys := args.phys, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := false,
                             checksum := args.checksum } :: s.pmap }.activeRoot = s.activeRoot := rfl
            have har'live : ∀ rid : ArenaId, rid = ar.id →
                FsState.arenaLive { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.logical, phys := args.phys, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := false,
                             checksum := args.checksum } :: s.pmap } rid = true := by
              intro rid hrid; subst hrid
              unfold FsState.arenaLive
              simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
              refine ⟨{ ar with refcount := ar.refcount + 1 }, ?_, rfl, by simp [hnd]⟩
              apply List.mem_map.mpr; exact ⟨ar, har_mem, by simp⟩
            have hliveEq : ∀ a : ArenaId,
                FsState.arenaLive { s with arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y) } a =
                FsState.arenaLive { s with
                  arenas := s.arenas.map (fun (y : Arena) => if y.id == ar.id then { ar with refcount := ar.refcount + 1 } else y),
                  pmap := { logical := args.logical, phys := args.phys, offset := args.offset,
                             len := args.len, birthGen := args.birthGen, shared := false,
                             checksum := args.checksum } :: s.pmap } a := by
              intro a; unfold FsState.arenaLive; rfl
            rw [hactEq]
            refine ⟨?_, ?_, ?_⟩
            · by_cases heq : s.activeRoot.inodeRoot = ar.id
              · exact har'live _ heq
              · rw [← hliveEq]; exact arenaLive_map_ne heq h.i7.1
            · by_cases heq : s.activeRoot.extentRoot = ar.id
              · exact har'live _ heq
              · rw [← hliveEq]; exact arenaLive_map_ne heq h.i7.2.1
            · by_cases heq : s.activeRoot.allocRoot = ar.id
              · exact har'live _ heq
              · rw [← hliveEq]; exact arenaLive_map_ne heq h.i7.2.2
          · -- I8: new entry non-shared; guard blocks any existing entry at same (phys,offset)
            intro e1 he1 e2 he2 hlog
            simp only [List.mem_cons] at he1 he2
            rcases he1 with he1eq | hm1 <;> rcases he2 with he2eq | hm2
            · -- both new: same logical (inline struct), contradicts hlog
              subst he1eq; subst he2eq; exact absurd rfl hlog
            · -- e1=new, e2=old: new entry is non-shared
              subst he1eq
              -- new entry: phys = args.phys, offset = args.offset
              by_cases hp : args.phys = e2.phys
              · by_cases ho : args.offset = e2.offset
                · exfalso; apply hnoconflict
                  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                  exact ⟨e2, hm2, ⟨hp.symm, ho.symm⟩⟩
                · exact Or.inr (Or.inl ho)
              · exact Or.inl hp
            · -- e1=old, e2=new
              subst he2eq
              by_cases hp : e1.phys = args.phys
              · by_cases ho : e1.offset = args.offset
                · exfalso; apply hnoconflict
                  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                  exact ⟨e1, hm1, ⟨hp, ho⟩⟩
                · exact Or.inr (Or.inl ho)
              · exact Or.inl hp
            · exact h.i8 e1 hm1 e2 hm2 hlog
          · -- I9: pmapRefs ≤ refcount
            intro a ha
            simp only [List.mem_map] at ha
            obtain ⟨b, hb, hba⟩ := ha
            by_cases hbid : b.id = ar.id
            · have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = { ar with refcount := ar.refcount + 1 } := by simp [hbid]
              rw [hmap] at hba; subst hba
              have hq := hpmapInc ar.id
              rw [if_pos harid.symm] at hq
              simp only [hq]
              have := h.i9 ar har_mem; omega
            · have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = b := by simp [hbid]
              rw [hmap] at hba; subst hba
              have hq := hpmapInc b.id
              -- b.id ≠ ar.id = args.phys, so the if-branch is 0
              rw [if_neg (show ¬ args.phys = b.id from fun h => hbid (harid ▸ h.symm))] at hq
              simp only [hq, Nat.add_zero]; exact h.i9 b hb
          · -- I10: discarded unchanged
            intro sn hsn a ha_mem a' ha' hid
            simp only [List.mem_map] at ha'
            obtain ⟨b, hb, hba⟩ := ha'
            by_cases hbid : b.id = ar.id
            · have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = { ar with refcount := ar.refcount + 1 } := by simp [hbid]
              rw [hmap] at hba; subst hba; exact hnd
            · have hmap : (if b.id == ar.id then { ar with refcount := ar.refcount + 1 } else b) = b := by simp [hbid]
              rw [hmap] at hba; subst hba; exact h.i10 sn hsn a ha_mem b hb hid

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
