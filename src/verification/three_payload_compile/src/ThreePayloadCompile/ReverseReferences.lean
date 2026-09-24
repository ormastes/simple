import ThreePayloadCompile.Model

namespace ThreePayloadCompile

private theorem mem_filter_not_contains {α : Type} [BEq α]
    [LawfulBEq α] (item : α) (source excluded : List α) :
    item ∈ source.filter (fun value => !(excluded.contains value)) ↔
      item ∈ source ∧ item ∉ excluded := by
  constructor
  · intro hmem
    rcases List.mem_filter.mp hmem with ⟨hsource, hfilter⟩
    refine ⟨hsource, ?_⟩
    intro hexcluded
    change (!(excluded.contains item)) = true at hfilter
    have hc : excluded.contains item = true :=
      List.contains_iff_mem.mpr hexcluded
    rw [hc] at hfilter
    contradiction
  · rintro ⟨hsource, hexcluded⟩
    apply List.mem_filter.mpr
    refine ⟨hsource, ?_⟩
    change (!(excluded.contains item)) = true
    cases hc : excluded.contains item with
    | false => rfl
    | true => exact False.elim (hexcluded (List.contains_iff_mem.mp hc))

theorem reverse_delta_reconstructs (old new : List RrEdge)
    (hOld : rrUnique old) (hNew : rrUnique new) (edge : RrEdge) :
    edge ∈ applyReverseDelta old (reverseDelta old new) ↔ edge ∈ new := by
  by_cases hold : edge ∈ old <;> by_cases hnew : edge ∈ new <;>
    simp [applyReverseDelta, reverseDelta, mem_filter_not_contains,
      hold, hnew]

theorem reverse_delta_unrelated_consumer_preserved
    (global old new : List RrEdge) (q : String) (edge : RrEdge)
    (hOld : ∀ candidate ∈ old, candidate.consumerKey = q)
    (hNew : ∀ candidate ∈ new, candidate.consumerKey = q)
    (hne : edge.consumerKey ≠ q) :
    edge ∈ applyReverseDelta global (reverseDelta old new) ↔ edge ∈ global := by
  have hnotold : edge ∉ old := by
    intro hedge
    exact hne (hOld edge hedge)
  have hnotnew : edge ∉ new := by
    intro hedge
    exact hne (hNew edge hedge)
  simp [applyReverseDelta, reverseDelta, mem_filter_not_contains,
    hnotold, hnotnew]

theorem rr_mutation_nil_history_refused (newReads : List RrEdge) :
    routeRrMutation none newReads = .refusedMissingHistory := by
  rfl

theorem rr_mutation_complete_empty_history_is_explicit
    (newReads : List RrEdge) :
    routeRrMutation (some []) newReads = .staged [] newReads := by
  rfl

end ThreePayloadCompile
