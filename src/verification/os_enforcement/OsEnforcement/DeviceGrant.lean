/-
  OsEnforcement.DeviceGrant — pure model of the SimpleOS independently-revocable
  device-grant ABI and the crash-revocation ordering state machine, with a
  sorry-free proof of the "no DMA without IOMMU" and revoke-ordering invariants
  (master plan §7.2 / §7.3 / §21).

  Source of truth (T2B — 2026-07-27):
    src/os/drivers/device_grant.spl
      struct DeviceGrant { device_id, rights: i64 bitmask, generation }
      grant_has / grant_revoke  (subtract-the-present-bits, no bitwise-NOT)
    src/os/drivers/device_grant_revocation.spl
      struct RevocationSequence { current_step, grant }
      revocation_can_advance (step == current+1 and step <= 10)
      revocation_apply_effect (step 3 clears DMA, step 4 clears IOMMU, step 6
        clears BAR|IOPORT|IRQ|MSI)
      revocation_can_acquire_dma (grant_has DMA AND grant_has IOMMU)

  Modelling notes
  ===============
  The real rights are a single i64 bitmask; each right is one power-of-two bit,
  so the mask behaves as a SET of held rights.  We model the held rights as a
  `List Nat` of right-ids (the bit values 1,2,4,…,32 preserved for fidelity but
  used only as distinct set atoms).  `revoke` filters out one right, matching
  `grant_revoke`'s "clear exactly that right, leave the others intact".  Core
  Lean 4 only (List/Nat/Bool), no Mathlib.

  Headline theorems (SPipe manual layer):
    OsEnforcement.revoke_independence     (DG1)
    OsEnforcement.ordering_no_skip         (DG2)
    OsEnforcement.no_dma_without_iommu     (DG3)
  Gate: `cd src/verification/os_enforcement && lake build`.
-/

namespace OsEnforcement

-- ============================================================
-- § 1  Right atoms (DGRANT_* bit values, used as set atoms)
-- ============================================================

abbrev BAR    : Nat := 1    -- DGRANT_BAR
abbrev IOPORT : Nat := 2    -- DGRANT_IOPORT
abbrev IRQ    : Nat := 4    -- DGRANT_IRQ
abbrev MSI    : Nat := 8    -- DGRANT_MSI
abbrev DMA    : Nat := 16   -- DGRANT_DMA
abbrev IOMMU  : Nat := 32   -- DGRANT_IOMMU

/-- Held rights as a set of right-ids (mirrors the i64 bitmask). -/
abbrev Rights := List Nat

/-- `has rs r` mirrors `grant_has`: the grant holds right `r`. -/
def has (rs : Rights) (r : Nat) : Bool := rs.contains r

/-- `revoke rs r` mirrors `grant_revoke`: clear exactly right `r`, leave the
    rest intact. -/
def revoke (rs : Rights) (r : Nat) : Rights := rs.filter (fun x => x != r)

theorem has_iff_mem (rs : Rights) (r : Nat) : has rs r = true ↔ r ∈ rs := by
  unfold has; exact List.contains_iff_mem

/-- A different right survives revocation (independence at the set level). -/
theorem mem_revoke_of_ne (rs : Rights) (r s : Nat) (hmem : r ∈ rs) (hne : r ≠ s) :
    r ∈ revoke rs s := by
  unfold revoke
  rw [List.mem_filter]
  refine ⟨hmem, ?_⟩
  rw [bne_iff_ne]; exact hne

/-- The revoked right itself is gone. -/
theorem not_mem_revoke_self (rs : Rights) (r : Nat) : ¬ r ∈ revoke rs r := by
  intro hmem
  unfold revoke at hmem
  rw [List.mem_filter] at hmem
  have h2 := hmem.2
  simp at h2

theorem has_false_of_not_mem (rs : Rights) (r : Nat) (h : ¬ r ∈ rs) :
    has rs r = false := by
  cases hc : has rs r with
  | false => rfl
  | true  => exact absurd ((has_iff_mem rs r).mp hc) h

-- ============================================================
-- § 2  DG1 — revoke independence
-- ============================================================

/-- DG1 — revoke_independence:
    revoking DMA leaves BAR and IRQ held.  Each right is an independent bit;
    clearing one does not disturb the others (device_grant.spl §7.2). -/
theorem revoke_independence (rs : Rights)
    (hbar : has rs BAR = true) (hirq : has rs IRQ = true) :
    has (revoke rs DMA) BAR = true ∧ has (revoke rs DMA) IRQ = true := by
  have hb := (has_iff_mem rs BAR).mp hbar
  have hi := (has_iff_mem rs IRQ).mp hirq
  refine ⟨?_, ?_⟩
  · exact (has_iff_mem _ _).mpr (mem_revoke_of_ne rs BAR DMA hb (by decide))
  · exact (has_iff_mem _ _).mpr (mem_revoke_of_ne rs IRQ DMA hi (by decide))

-- ============================================================
-- § 3  Revocation ordering state machine
-- ============================================================

/-- The 10-step ordered teardown sequence.  `currentStep` is the last COMPLETED
    step (0 = none, 10 = complete). -/
structure Seq where
  currentStep : Nat
  rights      : Rights
  deriving Repr

/-- `canAdvance seq step` mirrors `revocation_can_advance`: only the immediately
    following step may run, and never past step 10. -/
def canAdvance (s : Seq) (step : Nat) : Bool :=
  (step == s.currentStep + 1) && (step ≤ 10)

/-- `applyEffect rights step` mirrors `revocation_apply_effect`:
    step 3 clears DMA, step 4 clears IOMMU, step 6 clears the MMIO+IRQ handles. -/
def applyEffect (rs : Rights) (step : Nat) : Rights :=
  if step = 3 then revoke rs DMA
  else if step = 4 then revoke rs IOMMU
  else if step = 6 then revoke (revoke (revoke (revoke rs BAR) IOPORT) IRQ) MSI
  else rs

/-- `advance seq step` mirrors `revocation_advance`: out-of-order steps are
    refused and the sequence is returned unchanged. -/
def advance (s : Seq) (step : Nat) : Seq :=
  if canAdvance s step then { currentStep := step, rights := applyEffect s.rights step }
  else s

/-- DG2 — ordering_no_skip:
    an out-of-order advance (any step other than current+1) is rejected and
    leaves the sequence UNCHANGED — the ordering invariant admits no skip. -/
theorem ordering_no_skip (s : Seq) (step : Nat) (h : step ≠ s.currentStep + 1) :
    advance s step = s := by
  unfold advance canAdvance
  split
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    rw [beq_iff_eq] at hc
    exact absurd hc.1 h
  · rfl

-- ============================================================
-- § 4  DG3 — no DMA without IOMMU
-- ============================================================

/-- `canAcquireDma rights` mirrors `revocation_can_acquire_dma`: a new DMA
    mapping requires BOTH the DMA right AND the IOMMU right. -/
def canAcquireDma (rs : Rights) : Bool := has rs DMA && has rs IOMMU

/-- DG3 — no_dma_without_iommu:
    after the DMA-revoke step (step 3), a driver can no longer acquire a new DMA
    mapping — the §21 invariant "a driver without a live DMA/IOMMU grant cannot
    DMA".  `canAcquireDma` is false because the DMA right is gone. -/
theorem no_dma_without_iommu (rs : Rights) :
    canAcquireDma (applyEffect rs 3) = false := by
  have h3 : applyEffect rs 3 = revoke rs DMA := rfl
  rw [h3]
  unfold canAcquireDma
  rw [has_false_of_not_mem (revoke rs DMA) DMA (not_mem_revoke_self rs DMA)]
  exact Bool.false_and _

/-- DG3 corollary — step 4 additionally clears IOMMU, so `canAcquireDma`
    remains false after the IOMMU-removal step too. -/
theorem no_dma_after_iommu_removed (rs : Rights) :
    canAcquireDma (applyEffect rs 4) = false := by
  have h4 : applyEffect rs 4 = revoke rs IOMMU := rfl
  rw [h4]
  unfold canAcquireDma
  rw [has_false_of_not_mem (revoke rs IOMMU) IOMMU (not_mem_revoke_self rs IOMMU)]
  exact Bool.and_false _

-- Axiom audit (must report no sorryAx)
#print axioms revoke_independence
#print axioms no_dma_without_iommu

end OsEnforcement
