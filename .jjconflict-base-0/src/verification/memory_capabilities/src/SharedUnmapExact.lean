/-!
# Exact bounded model of `vmm_shared_unmap`

This is the transition used by the FV2 source validator.  It models one page
of one live region: private regions do not own shared-page references; shared
regions drop exactly one reference; the last reference writes dirty data back
and retires the resident page.  An already-dead region is an idempotent no-op.
-/

namespace MemoryCapabilities.SharedUnmapExact

structure PageState where
  live : Bool
  privateMap : Bool
  mapRefs : Nat
  resident : Bool
  dirty : Bool
  backingByte : UInt8
  pageByte : UInt8
deriving DecidableEq, Repr

def unmap (s : PageState) : PageState :=
  if !s.live then s
  else if s.privateMap then { s with live := false }
  else match s.mapRefs with
    | 0 => { s with live := false }
    | n + 1 =>
      if n = 0 then
        { s with
          live := false
          mapRefs := 0
          resident := false
          dirty := false
          backingByte := if s.dirty then s.pageByte else s.backingByte }
      else
        { s with live := false, mapRefs := n }

theorem survivor_reference_is_preserved (s : PageState) (n : Nat)
    (hlive : s.live = true) (hshared : s.privateMap = false)
    (hrefs : s.mapRefs = n + 2) :
    (unmap s).mapRefs = n + 1 ∧ (unmap s).resident = s.resident := by
  simp [unmap, hlive, hshared, hrefs]

theorem last_reference_writes_back_dirty_page (s : PageState)
    (hlive : s.live = true) (hshared : s.privateMap = false)
    (hrefs : s.mapRefs = 1) (hdirty : s.dirty = true) :
    (unmap s).mapRefs = 0 ∧
    (unmap s).resident = false ∧
    (unmap s).dirty = false ∧
    (unmap s).backingByte = s.pageByte := by
  simp [unmap, hlive, hshared, hrefs, hdirty]

theorem private_unmap_does_not_drop_shared_reference (s : PageState)
    (hlive : s.live = true) (hprivate : s.privateMap = true) :
    (unmap s).mapRefs = s.mapRefs ∧
    (unmap s).backingByte = s.backingByte := by
  simp [unmap, hlive, hprivate]

theorem repeated_unmap_is_noop (s : PageState) (hdead : s.live = false) :
    unmap s = s := by
  simp [unmap, hdead]

/-- Composite FV2 root for survivor, last-dirty, private, and repeated unmap. -/
theorem shared_unmap_refinement_bundle :
    (∀ (s : PageState) (n : Nat), s.live = true →
      s.privateMap = false → s.mapRefs = n + 2 →
      (unmap s).mapRefs = n + 1 ∧ (unmap s).resident = s.resident) ∧
    (∀ s : PageState, s.live = true → s.privateMap = false →
      s.mapRefs = 1 → s.dirty = true →
      (unmap s).mapRefs = 0 ∧ (unmap s).resident = false ∧
        (unmap s).dirty = false ∧ (unmap s).backingByte = s.pageByte) ∧
    (∀ s : PageState, s.live = true → s.privateMap = true →
      (unmap s).mapRefs = s.mapRefs ∧
        (unmap s).backingByte = s.backingByte) ∧
    (∀ s : PageState, s.live = false → unmap s = s) := by
  exact ⟨survivor_reference_is_preserved,
    last_reference_writes_back_dirty_page,
    private_unmap_does_not_drop_shared_reference,
    repeated_unmap_is_noop⟩

end MemoryCapabilities.SharedUnmapExact
