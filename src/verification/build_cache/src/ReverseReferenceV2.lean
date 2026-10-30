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

/-- A sealed manifest contributes one edge per read. An unsealed
    (failed/cancelled) manifest rejects the candidate, regardless of the
    previous generation; callers preserve that historical receipt separately. -/
def projectOne (prev : Option (List Edge)) (m : Manifest) : Option (List Edge) :=
  if m.sealed then
    if m.reads.all (·.2) then some (m.reads.map (fun r => (r.1, m.consumer))) else none
  else
    none

def project (prev : Option (List Edge)) : List Manifest → Option (List Edge)
  | []      => some []
  | m :: ms =>
    match projectOne prev m, project prev ms with
    | some a, some b => some (a ++ b)
    | _, _           => none

/-- Current forward relation. `prev` remains in the signature for model
    compatibility but never supplies edges to the current projection. -/
def Forward (_prev : Option (List Edge)) (ms : List Manifest) (s : Subj) (c : Cons) : Prop :=
  ∃ m ∈ ms, m.consumer = c ∧ m.sealed = true ∧ s ∈ m.reads.map Prod.fst

theorem projectOne_mem (prev : Option (List Edge)) (m : Manifest) (a : List Edge)
    (h : projectOne prev m = some a) (s : Subj) (c : Cons) :
    (s, c) ∈ a ↔ m.consumer = c ∧ m.sealed = true ∧ s ∈ m.reads.map Prod.fst := by
  unfold projectOne at h
  cases hs : m.sealed
  · simp [hs] at h
  · simp [hs] at h
    obtain ⟨_, rfl⟩ := h
    simp [List.mem_map, Prod.mk.injEq, hs, and_assoc, and_left_comm, and_comm]

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
  · rintro ⟨m, hm, hc, _, hr⟩
    exact ⟨m, hm, hc, hr⟩
  · rintro ⟨m, hm, hc, hr⟩
    exact ⟨m, hm, hc, hall m hm, hr⟩

/-- Successful projection candidates contain only sealed current manifests. -/
theorem project_success_implies_all_sealed (prev : Option (List Edge)) (ms : List Manifest)
    (rr : List Edge) (h : project prev ms = some rr) :
    ∀ m ∈ ms, m.sealed = true := by
  induction ms generalizing rr with
  | nil => simp
  | cons m ms ih =>
    unfold project at h
    cases hp : projectOne prev m with
    | none => simp [hp] at h
    | some a =>
      have hsealed : m.sealed = true := by
        cases hs : m.sealed
        · have hn : projectOne prev m = none := by simp [projectOne, hs]
          rw [hp] at hn
          cases hn
        · rfl
      cases hr : project prev ms with
      | none => simp [hp, hr] at h
      | some b =>
        simp [hp, hr] at h
        subst rr
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hsealed
        · exact ih b hr x hx

/-- Previous-generation contents cannot affect the newly built projection. -/
theorem project_previous_independent (prev₁ prev₂ : Option (List Edge)) (ms : List Manifest) :
    project prev₁ ms = project prev₂ ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [project, projectOne, ih]

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

/-- A failed consumer rejects the candidate even when a prior receipt exists. -/
theorem unsealed_with_previous_fails (prev : Option (List Edge)) (m : Manifest) (ms : List Manifest)
    (hs : m.sealed = false) : project prev (m :: ms) = none := by
  simp [project, projectOne, hs]

/-- An unsealed manifest at any position rejects the entire candidate. -/
theorem unsealed_anywhere_fails (prev : Option (List Edge)) (ms : List Manifest)
    (m : Manifest) (hm : m ∈ ms) (hs : m.sealed = false) : project prev ms = none := by
  cases hp : project prev ms with
  | none => rfl
  | some rr =>
    have hsealed := project_success_implies_all_sealed prev ms rr hp m hm
    rw [hs] at hsealed
    cases hsealed

/-- Compatibility specialization of the general unsealed rejection theorem. -/
theorem unsealed_without_previous_fails (m : Manifest) (ms : List Manifest)
    (hs : m.sealed = false) : project none (m :: ms) = none :=
  unsealed_with_previous_fails none m ms hs

end ReverseReferenceV2
