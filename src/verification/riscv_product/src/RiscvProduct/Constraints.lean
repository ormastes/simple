import RiscvProduct.Generated

/-!
# RISC-V Product Profile Added Constraints

Manual proof layer. Regeneration must not overwrite this file; it imports the
generated base model and states the stronger product/resource constraints.
-/

namespace RiscvProduct

theorem rv32_profile_expected :
    (profile Lane.rv32).abi = Abi.ilp32d ∧
    (profile Lane.rv32).mmu = Mmu.sv32 ∧
    (profile Lane.rv32).maxLuts = 25000 ∧
    (profile Lane.rv32).targetMhz = 50 ∧
    (profile Lane.rv32).formalGate = FormalGate.rvfiSby := by
  simp [profile]

theorem rv64_profile_expected :
    (profile Lane.rv64).abi = Abi.lp64d ∧
    (profile Lane.rv64).mmu = Mmu.sv39 ∧
    (profile Lane.rv64).maxLuts = 45000 ∧
    (profile Lane.rv64).targetMhz = 50 ∧
    (profile Lane.rv64).formalGate = FormalGate.rvfiSby := by
  simp [profile]

theorem profile_budgets_positive (l : Lane) :
    (profile l).maxLuts > 0 ∧ (profile l).targetMhz > 0 := by
  cases l <;> simp [profile]

theorem product_metadata_override_sets_fields
    (l : Lane)
    (productLevel configurationProfile : String) :
    (withProductMetadata (profile l) productLevel configurationProfile).productLevel = productLevel ∧
    (withProductMetadata (profile l) productLevel configurationProfile).configurationProfile = configurationProfile ∧
    (withProductMetadata (profile l) productLevel configurationProfile).lane = (profile l).lane := by
  simp [withProductMetadata]

theorem product_metadata_preserves_formal_gate
    (l : Lane)
    (productLevel configurationProfile : String) :
    (withProductMetadata (profile l) productLevel configurationProfile).formalGate =
      (profile l).formalGate := by
  simp [withProductMetadata]

theorem budget_override_sets_fields
    (l : Lane)
    (maxLuts targetMhz : Nat) :
    (withBudgets (profile l) maxLuts targetMhz).maxLuts = maxLuts ∧
    (withBudgets (profile l) maxLuts targetMhz).targetMhz = targetMhz ∧
    (withBudgets (profile l) maxLuts targetMhz).formalGate = (profile l).formalGate := by
  simp [withBudgets]

theorem profiles_are_dual_arch :
    (profile Lane.rv32).lane ≠ (profile Lane.rv64).lane := by
  simp [profile]

theorem all_profiles_use_rvfi_sby (l : Lane) :
    (profile l).formalGate = FormalGate.rvfiSby := by
  cases l <;> simp [profile]

theorem next_lane_alternates (l : Lane) :
    nextLane l ≠ l := by
  cases l <;> simp [nextLane]

theorem round_robin_no_starvation (start target : Lane) :
    servedWithinTwo start target := by
  cases start <;> cases target <;> simp [servedWithinTwo, nextLane]

theorem round_robin_two_steps_returns_start (start : Lane) :
    nextLane (nextLane start) = start := by
  cases start <;> simp [nextLane]

theorem acquire_sets_single_owner (s s' : ResourceState) (l : Lane) :
    acquire s l = some s' → s'.owner = some l := by
  intro h
  cases howner : s.owner with
  | none =>
      simp [acquire, howner] at h
      cases h
      rfl
  | some owner =>
      simp [acquire, howner] at h

theorem acquire_success_requires_empty (s s' : ResourceState) (l : Lane) :
    acquire s l = some s' → s.owner = none := by
  intro h
  cases howner : s.owner with
  | none => rfl
  | some owner =>
      simp [acquire, howner] at h

theorem acquire_success_deterministic (s s1 s2 : ResourceState) (l : Lane) :
    acquire s l = some s1 → acquire s l = some s2 → s1 = s2 := by
  intro h1 h2
  cases howner : s.owner with
  | none =>
      simp [acquire, howner] at h1 h2
      cases h1
      cases h2
      rfl
  | some owner =>
      simp [acquire, howner] at h1

theorem acquire_grants_iff_empty (s : ResourceState) (l : Lane) :
    acquire s l = some { owner := some l } ↔ s.owner = none := by
  constructor
  · intro h
    exact acquire_success_requires_empty s { owner := some l } l h
  · intro h
    cases s with
    | mk current =>
        simp at h
        cases h
        simp [acquire]

theorem acquire_empty_succeeds (l : Lane) :
    acquire { owner := none } l = some { owner := some l } := by
  cases l <;> simp [acquire]

theorem acquire_empty_never_sets_other_owner (l other : Lane)
    (h : l ≠ other) :
    acquire { owner := none } l ≠ some { owner := some other } := by
  cases l <;> cases other <;> simp [acquire] at *

theorem acquire_none_requires_owner (s : ResourceState) (l : Lane) :
    acquire s l = none → ∃ owner, s.owner = some owner := by
  intro h
  cases howner : s.owner with
  | none =>
      simp [acquire, howner] at h
  | some owner =>
      exact ⟨owner, rfl⟩

theorem acquire_none_iff_occupied (s : ResourceState) (l : Lane) :
    acquire s l = none ↔ ∃ owner, s.owner = some owner := by
  constructor
  · exact acquire_none_requires_owner s l
  · intro h
    rcases h with ⟨owner, howner⟩
    unfold acquire
    rw [howner]

theorem held_resource_rejects_second_owner (s : ResourceState) (owner other : Lane) :
    s.owner = some owner → acquire s other = none := by
  intro h
  unfold acquire
  rw [h]

theorem held_resource_rejects_reentrant_acquire (owner : Lane) :
    acquire { owner := some owner } owner = none := by
  cases owner <;> simp [acquire]

theorem acquire_then_reentrant_acquire_denied (owner : Lane) :
    (acquire { owner := none } owner).bind (fun s => acquire s owner) = none := by
  cases owner <;> simp [acquire]

theorem acquire_then_any_second_acquire_denied (owner requester : Lane) :
    (acquire { owner := none } owner).bind (fun s => acquire s requester) = none := by
  cases owner <;> cases requester <;> simp [acquire]

theorem failed_second_acquire_and_release_preserves_owner (owner other : Lane)
    (h : owner ≠ other) :
    acquire { owner := some owner } other = none ∧
      release { owner := some owner } other = { owner := some owner } := by
  cases owner <;> cases other <;> simp [acquire, release] at *

theorem failed_acquire_then_owner_release_allows_requester
    (s : ResourceState) (owner requester : Lane)
    (howner : s.owner = some owner) :
    acquire s requester = none ∧
      acquire (release s owner) requester = some { owner := some requester } := by
  cases s with
  | mk current =>
      simp at howner
      cases howner
      cases owner <;> cases requester <;> simp [acquire, release]

theorem owner_release_clears_resource (l : Lane) :
    release { owner := some l } l = { owner := none } := by
  cases l <;> simp [release]

theorem owner_release_then_any_lane_acquires (owner requester : Lane) :
    acquire (release { owner := some owner } owner) requester =
      some { owner := some requester } := by
  cases owner <;> cases requester <;> simp [acquire, release]

theorem release_deterministic (s r1 r2 : ResourceState) (l : Lane) :
    release s l = r1 → release s l = r2 → r1 = r2 := by
  intro h1 h2
  rw [←h1, ←h2]

theorem release_empty_iff_unowned_or_owner (s : ResourceState) (requester : Lane) :
    release s requester = { owner := none } ↔
      s.owner = none ∨ s.owner = some requester := by
  cases s with
  | mk current =>
      cases current with
      | none =>
          simp [release]
      | some owner =>
          cases owner <;> cases requester <;> simp [release]

theorem acquire_release_roundtrip_empty (l : Lane) :
    (acquire { owner := none } l).map (fun s => release s l) = some { owner := none } := by
  cases l <;> simp [acquire, release]

theorem acquire_then_owner_release_clears (l : Lane) :
    (acquire { owner := none } l).map (fun s => release s l) =
      some { owner := none } := by
  cases l <;> simp [acquire, release]

theorem successful_acquire_then_owner_release_clears (s s' : ResourceState) (l : Lane) :
    acquire s l = some s' → release s' l = { owner := none } := by
  intro h
  cases howner : s.owner with
  | none =>
      simp [acquire, howner] at h
      cases h
      exact owner_release_clears_resource l
  | some owner =>
      simp [acquire, howner] at h

theorem acquire_then_non_owner_release_preserves_owner (owner requester : Lane)
    (h : owner ≠ requester) :
    (acquire { owner := none } owner).map (fun s => release s requester) =
      some { owner := some owner } := by
  cases owner <;> cases requester <;> simp [acquire, release] at *

theorem empty_release_noop (l : Lane) :
    release { owner := none } l = { owner := none } := by
  cases l <;> simp [release]

theorem non_owner_release_preserves_resource (owner other : Lane)
    (h : owner ≠ other) :
    release { owner := some owner } other = { owner := some owner } := by
  cases owner <;> cases other <;> simp [release] at *

theorem non_owner_release_preserves_occupied
    (s : ResourceState) (owner other : Lane)
    (howner : s.owner = some owner) (h : owner ≠ other) :
    release s other = { owner := some owner } := by
  cases s with
  | mk current =>
      simp at howner
      cases howner
      exact non_owner_release_preserves_resource owner other h

theorem release_clears_only_for_owner (owner requester : Lane) :
    release { owner := some owner } requester = { owner := none } → requester = owner := by
  cases owner <;> cases requester <;> simp [release]

theorem release_clears_occupied_only_for_owner
    (s : ResourceState) (owner requester : Lane)
    (howner : s.owner = some owner) :
    release s requester = { owner := none } → requester = owner := by
  cases s with
  | mk current =>
      simp at howner
      cases howner
      exact release_clears_only_for_owner owner requester

theorem occupied_release_noop_implies_non_owner (owner requester : Lane) :
    release { owner := some owner } requester = { owner := some owner } → requester ≠ owner := by
  cases owner <;> cases requester <;> simp [release]

end RiscvProduct
