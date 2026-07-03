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

theorem round_robin_no_starvation (start target : Lane) :
    servedWithinTwo start target := by
  cases start <;> cases target <;> simp [servedWithinTwo, nextLane]

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

theorem held_resource_rejects_second_owner (s : ResourceState) (owner other : Lane) :
    s.owner = some owner → acquire s other = none := by
  intro h
  unfold acquire
  rw [h]

theorem owner_release_clears_resource (l : Lane) :
    release { owner := some l } l = { owner := none } := by
  cases l <;> simp [release]

end RiscvProduct
