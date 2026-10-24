/-
  ReverseReferenceV2 — T-RR1: the `.rr` reverse projection is the inverse of
  the sealed forward read manifests.

  Models reverse_reference_project_generation_v2
  (src/compiler/80.driver/cache/reverse_reference_projection_v2.spl) at the
  edge level: a projected edge is (subject, consumer); `@`-prefixed coverage
  markers are not edges and are not modelled. Plan:
  doc/05_design/compiler/incremental_build/cache_invalidation_formal_verification_2026-10-24.md §4.1 T-RR1.
  Bounded-exhaustive SSpec twin:
  test/00_formal_verification/compiler/reverse_reference_inverse_bounded_spec.spl
  No sorry, no axioms.
-/
namespace ReverseReferenceV2

abbrev Subj := String
abbrev Cons := String
abbrev Edge := Subj × Cons

/-- One forward manifest. `mapped = false` is a read whose producer kind has
    no reverse family (the code fails the whole build: unmapped-read-kind). -/
structure Manifest where
  consumer : Cons
  sealed   : Bool
  reads    : List (Subj × Bool)

/-- Sealed: one edge per read. Unsealed (failed/cancelled rebuild): keep the
    consumer's edges from the previous generation; no previous ⇒ fail. -/
def projectOne (prev : Option (List Edge)) (m : Manifest) : Option (List Edge) :=
  if m.sealed then
    if m.reads.all (·.2) then some (m.reads.map (fun r => (r.1, m.consumer))) else none
  else
    match prev with
    | none   => none
    | some p => some (p.filter (fun e => e.2 = m.consumer))

def project (prev : Option (List Edge)) : List Manifest → Option (List Edge)
  | []      => some []
  | m :: ms =>
    match projectOne prev m, project prev ms with
    | some a, some b => some (a ++ b)
    | _, _           => none

/-- Forward relation: consumer `c` reads subject `s` in this generation, or,
    for a consumer whose rebuild did not seal, read it in the previous one. -/
def Forward (prev : Option (List Edge)) (ms : List Manifest) (s : Subj) (c : Cons) : Prop :=
  ∃ m ∈ ms, m.consumer = c ∧
    ((m.sealed = true ∧ s ∈ m.reads.map Prod.fst) ∨
     (m.sealed = false ∧ ∃ p, prev = some p ∧ (s, c) ∈ p))

theorem projectOne_mem (prev : Option (List Edge)) (m : Manifest) (a : List Edge)
    (h : projectOne prev m = some a) (s : Subj) (c : Cons) :
    (s, c) ∈ a ↔ m.consumer = c ∧
      ((m.sealed = true ∧ s ∈ m.reads.map Prod.fst) ∨
       (m.sealed = false ∧ ∃ p, prev = some p ∧ (s, c) ∈ p)) := by
  unfold projectOne at h
  cases hs : m.sealed
  · simp [hs] at h
    cases hp : prev with
    | none => simp [hp] at h
    | some p =>
      simp [hp] at h
      subst h
      constructor
      · intro hm
        simp [List.mem_filter] at hm
        exact ⟨hm.2.symm, by simp; exact hm.1⟩
      · rintro ⟨hc, hr⟩
        simp at hr
        simp [List.mem_filter, hr, hc]
  · simp [hs] at h
    obtain ⟨_, rfl⟩ := h
    simp only [List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨r, hr, h1, h2⟩
      exact ⟨h2, Or.inl ⟨trivial, r, hr, h1⟩⟩
    · rintro ⟨hc, ⟨_, r, hr, h1⟩ | ⟨hf, _⟩⟩
      · exact ⟨r, hr, h1, hc⟩
      · cases hf

/-- T-RR1: a successful projection contains exactly the inverse of the
    forward relation — no consumer is omitted (no under-invalidation) and no
    edge is invented. -/
theorem rr_is_inverse_of_forward (prev : Option (List Edge)) (ms : List Manifest)
    (rr : List Edge) (h : project prev ms = some rr) (s : Subj) (c : Cons) :
    (s, c) ∈ rr ↔ Forward prev ms s c := by
  induction ms generalizing rr with
  | nil =>
    simp [project] at h; subst h
    simp [Forward]
  | cons m ms ih =>
    unfold project at h
    cases ha : projectOne prev m with
    | none => simp [ha] at h
    | some a =>
      cases hb : project prev ms with
      | none => simp [ha, hb] at h
      | some b =>
        simp [ha, hb] at h
        subst h
        rw [List.mem_append, projectOne_mem prev m a ha s c, ih b hb]
        unfold Forward
        simp only [List.mem_cons, exists_eq_or_imp]

/-- With every consumer sealed the projection is the exact inverse of this
    generation's reads (no dependence on the previous generation). -/
theorem rr_exact_when_all_sealed (prev : Option (List Edge)) (ms : List Manifest)
    (rr : List Edge) (h : project prev ms = some rr)
    (hall : ∀ m ∈ ms, m.sealed = true) (s : Subj) (c : Cons) :
    (s, c) ∈ rr ↔ ∃ m ∈ ms, m.consumer = c ∧ s ∈ m.reads.map Prod.fst := by
  rw [rr_is_inverse_of_forward prev ms rr h s c]
  unfold Forward
  constructor
  · rintro ⟨m, hm, hc, hr⟩
    rcases hr with ⟨_, hr⟩ | ⟨hns, _⟩
    · exact ⟨m, hm, hc, hr⟩
    · rw [hall m hm] at hns; cases hns
  · rintro ⟨m, hm, hc, hr⟩
    exact ⟨m, hm, hc, Or.inl ⟨hall m hm, hr⟩⟩

/-- An unmapped read fails the whole generation (never a silent omission). -/
theorem unmapped_read_fails (prev : Option (List Edge)) (m : Manifest) (ms : List Manifest)
    (hs : m.sealed = true) (hu : ∃ r ∈ m.reads, r.2 = false) :
    project prev (m :: ms) = none := by
  have h1 : projectOne prev m = none := by
    unfold projectOne
    obtain ⟨r, hr, hf⟩ := hu
    have : m.reads.all (·.2) = false := by
      rw [Bool.eq_false_iff]
      intro hall
      rw [List.all_eq_true] at hall
      have := hall r hr
      rw [hf] at this
      cases this
    simp [hs, this]
  simp [project, h1]

/-- A failed consumer with no previous generation fails the build instead of
    publishing "zero dependents". -/
theorem unsealed_without_previous_fails (m : Manifest) (ms : List Manifest)
    (hs : m.sealed = false) : project none (m :: ms) = none := by
  simp [project, projectOne, hs]

end ReverseReferenceV2
