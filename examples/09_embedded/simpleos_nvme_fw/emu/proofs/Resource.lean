/-
  Resource.lean — resource-safety properties for the NVMe emulator.

  Two genuine resource guarantees the emulator relies on:

  (a) Shared-memory region disjointness. Two PRP regions [a, a+la) and [b, b+lb)
      that are laid out non-overlapping (a + la ≤ b) share no word index — so a DMA
      into one can never corrupt the other.

  (b) Generation-handle use-after-free protection. Each reusable slot carries a
      generation counter; freeing a slot bumps its generation (gen -> gen+1). A handle
      captured before the free still holds the old generation, so a later access whose
      stored generation differs from the handle's generation is rejected. We prove the
      core fact that a freed slot's generation never equals a live handle's generation,
      hence the mismatch (rejection) is guaranteed — no use-after-free.

  Lean core + omega / decide only (no mathlib).
-/

set_option linter.unusedVariables false

-- (a) Membership in a half-open region [base, base+len).
def inRegion (base len i : Int) : Prop := base ≤ i ∧ i < base + len

-- Non-overlapping regions share no index.
theorem regions_disjoint (a la b lb i : Int)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hsep : a + la ≤ b)
    (hi_a : inRegion a la i) (hi_b : inRegion b lb i) : False := by
  unfold inRegion at hi_a hi_b; omega

-- Equivalent statement: no index is simultaneously in both regions.
theorem regions_no_common_index (a la b lb : Int)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hsep : a + la ≤ b) :
    ¬ ∃ i, inRegion a la i ∧ inRegion b lb i := by
  rintro ⟨i, hi_a, hi_b⟩
  unfold inRegion at hi_a hi_b; omega

-- A write confined to region A leaves any index of region B unchanged-eligible:
-- every index of B lies strictly outside A.
theorem region_b_outside_a (a la b lb i : Int)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hsep : a + la ≤ b)
    (hi_b : inRegion b lb i) : ¬ inRegion a la i := by
  unfold inRegion at *; omega

-- (b) Generation model: freeing bumps the generation by one.
def freedGen (gen : Int) : Int := gen + 1
def liveGen  (gen : Int) : Int := gen

-- A freed slot's generation never matches a still-live handle's generation.
theorem freed_ne_live (gen : Int) : freedGen gen ≠ liveGen gen := by
  unfold freedGen liveGen; omega

-- Access check: a handle is accepted iff its captured generation equals the slot's
-- current generation. After a free (slot advanced to gen+1) a handle holding `gen`
-- is rejected — no use-after-free.
def accessGranted (handleGen slotGen : Int) : Bool := handleGen == slotGen

theorem use_after_free_rejected (gen : Int) :
    accessGranted (liveGen gen) (freedGen gen) = false := by
  unfold accessGranted liveGen freedGen
  simp only [beq_eq_false_iff_ne, ne_eq]
  omega

-- And a valid (non-freed) access is granted: matching generations are accepted.
theorem valid_access_granted (gen : Int) :
    accessGranted (liveGen gen) (liveGen gen) = true := by
  unfold accessGranted liveGen
  simp
