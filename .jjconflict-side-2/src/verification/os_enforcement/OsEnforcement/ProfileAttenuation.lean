/-
  OsEnforcement.ProfileAttenuation — pure model of the SimpleOS LLM-profile
  rights resolution law and the spawn-time triple attenuation, with a sorry-free
  proof of ceiling-subset, deny-wins, and triple-attenuation (master plan
  §5.4 / §17 / §21).

  Source of truth (INT3 — 2026-07-27):
    src/os/security/llm_profiles/profile_registry.spl
      resolve_effective:  effective = (base ∪ overlays) ∩ sys ∩ user − denies
        (step 1 union base+overlays; step 2 intersect BOTH ceilings; step 3
         subtract explicit denies LAST and unconditionally)
      is_subset (child & parent) == child   -- bitmask attenuation
    src/os/security/llm_profiles/profile_spawn_adapter.spl
      llm_spawn_effective_rights = profile_spawn_rights
                                 & parent_delegable & executable_ceiling
        (pure intersection — deny-by-omission, never amplified)

  Modelling notes
  ===============
  Rights are a Nat bitmask in the source; each bit is one right, so the mask is a
  SET of held right-ids.  We model rights as `List Nat`.  Bitmask AND becomes set
  intersection (`inter`, keep elements present in both) and bitmask AND-with-NOT
  becomes set difference (`diff`).  Overlay union is list append (`granted`).
  `Sub a b` is set inclusion.  Core Lean 4 only (List/Nat/Bool), no Mathlib.

  Headline theorems (SPipe manual layer):
    OsEnforcement.effective_subset_ceilings   (PA1)
    OsEnforcement.deny_wins                     (PA2)
    OsEnforcement.spawn_triple_attenuation      (PA3)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement

-- ============================================================
-- § 1  Set operations over rights bitmasks
-- ============================================================

/-- `inter a b` mirrors bitmask AND (`a & b`): keep the rights present in both. -/
def inter (a b : List Nat) : List Nat := a.filter (fun x => b.contains x)

/-- `diff a b` mirrors bitmask AND-NOT (`a & ~b`): drop the rights present in
    `b`.  Used for the unconditional deny subtraction. -/
def diff (a b : List Nat) : List Nat := a.filter (fun x => !b.contains x)

/-- Set inclusion (bitmask `is_subset`). -/
def Sub (a b : List Nat) : Prop := ∀ r, r ∈ a → r ∈ b

theorem Sub.trans {a b c : List Nat} (h1 : Sub a b) (h2 : Sub b c) : Sub a c :=
  fun r hr => h2 r (h1 r hr)

theorem inter_sub_left (a b : List Nat) : Sub (inter a b) a := by
  intro r hr; unfold inter at hr; rw [List.mem_filter] at hr; exact hr.1

theorem inter_sub_right (a b : List Nat) : Sub (inter a b) b := by
  intro r hr; unfold inter at hr; rw [List.mem_filter] at hr
  exact List.contains_iff_mem.mp hr.2

theorem diff_sub_left (a b : List Nat) : Sub (diff a b) a := by
  intro r hr; unfold diff at hr; rw [List.mem_filter] at hr; exact hr.1

/-- A right that is denied cannot survive `diff`: deny is exclusion. -/
theorem diff_excludes (a b : List Nat) (r : Nat) (h : r ∈ b) : ¬ r ∈ diff a b := by
  intro hr
  unfold diff at hr
  rw [List.mem_filter] at hr
  have h2 := hr.2
  have hc : b.contains r = true := List.contains_iff_mem.mpr h
  rw [hc] at h2
  simp at h2

-- ============================================================
-- § 2  resolve_effective
-- ============================================================

/-- Step 1 of `resolve_effective`: union base grants with every overlay's grants
    (the only union in the whole law — overlays ADD, never replace). -/
def granted (base : List Nat) (overlays : List (List Nat)) : List Nat :=
  overlays.foldl (fun acc ov => acc ++ ov) base

/-- `resolveEffective` mirrors `resolve_effective`:
      effective = (base ∪ overlays) ∩ sys ∩ user − denies
    intersecting BOTH ceilings, then subtracting denies LAST. -/
def resolveEffective (base : List Nat) (overlays : List (List Nat))
    (sys user denies : List Nat) : List Nat :=
  diff (inter (inter (granted base overlays) sys) user) denies

/-- PA1 — effective_subset_ceilings:
    the resolved effective rights are a subset of the system ceiling AND of the
    user ceiling (§17 "always a subset of each ceiling individually"). -/
theorem effective_subset_ceilings
    (base : List Nat) (overlays : List (List Nat)) (sys user denies : List Nat) :
    Sub (resolveEffective base overlays sys user denies) sys ∧
    Sub (resolveEffective base overlays sys user denies) user := by
  unfold resolveEffective
  constructor
  · exact Sub.trans (diff_sub_left _ _) (Sub.trans (inter_sub_left _ _) (inter_sub_right _ _))
  · exact Sub.trans (diff_sub_left _ _) (inter_sub_right _ _)

/-- PA2 — deny_wins:
    any right in `denies` is absent from the effective set, no matter what base
    or overlays granted (§17 "deny wins; subtracted LAST and unconditionally"). -/
theorem deny_wins
    (base : List Nat) (overlays : List (List Nat)) (sys user denies : List Nat)
    (r : Nat) (h : r ∈ denies) :
    ¬ r ∈ resolveEffective base overlays sys user denies := by
  unfold resolveEffective
  exact diff_excludes _ _ r h

-- ============================================================
-- § 3  Spawn-time triple attenuation
-- ============================================================

/-- `spawnRights` mirrors `llm_spawn_effective_rights`:
      spawn = profileRights ∩ parentDelegable ∩ executableCeiling
    a pure triple intersection — deny by omission. -/
def spawnRights (profileR parentDeleg execCeil : List Nat) : List Nat :=
  inter (inter profileR parentDeleg) execCeil

/-- PA3 — spawn_triple_attenuation:
    the spawn rights are simultaneously a subset of the profile's own rights, of
    the parent's delegable rights, and of the executable ceiling — never
    amplified beyond any of the three inputs (§5.4). -/
theorem spawn_triple_attenuation (profileR parentDeleg execCeil : List Nat) :
    Sub (spawnRights profileR parentDeleg execCeil) profileR ∧
    Sub (spawnRights profileR parentDeleg execCeil) parentDeleg ∧
    Sub (spawnRights profileR parentDeleg execCeil) execCeil := by
  unfold spawnRights
  refine ⟨?_, ?_, ?_⟩
  · exact Sub.trans (inter_sub_left _ _) (inter_sub_left _ _)
  · exact Sub.trans (inter_sub_left _ _) (inter_sub_right _ _)
  · exact inter_sub_right _ _

-- Axiom audit (must report no sorryAx)
#print axioms effective_subset_ceilings
#print axioms deny_wins
#print axioms spawn_triple_attenuation

end OsEnforcement
