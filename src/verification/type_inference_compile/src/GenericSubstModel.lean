/-!
Structural model of `40.mono/model/generic_subst_model.spl`.
This is a manual proof owner, not generated code. Production HIR refinement
and executable Simple/Lean correspondence are separate obligations.
-/
namespace GenericSubstModel

inductive MType where
  | var : String → MType
  | con : String → MType
  | app : String → List MType → MType
  deriving Repr

def unknown : MType := .con "?"
abbrev Subst := String → Option MType

def apply (s : Subst) : MType → MType
  | .var name => (s name).getD (.var name)
  | .con name => .con name
  | .app ctor args => .app ctor (args.map (apply s))

def Closed : MType → Prop
  | .var _ => False
  | .con name => name ≠ "?"
  | .app _ args => ∀ t ∈ args, Closed t

def ClosedRange (s : Subst) : Prop :=
  ∀ name t, s name = some t → Closed t

def Supported (s : Subst) : MType → Prop
  | .var name => ∃ t, s name = some t
  | .con name => name ≠ "?"
  | .app _ args => ∀ t ∈ args, Supported s t

def compose (outer inner : Subst) : Subst := fun name =>
  match inner name with
  | some t => some (apply outer t)
  | none => outer name

theorem apply_empty (t : MType) : apply (fun _ => none) t = t := by
  cases t with
  | var name => simp [apply]
  | con name => simp [apply]
  | app ctor args =>
    simp only [apply]
    congr 1
    apply Eq.trans (b := args.map id)
    · apply List.map_congr_left
      intro a ha
      exact apply_empty a
    · exact List.map_id args
termination_by sizeOf t

theorem apply_closed (s : Subst) (t : MType) (h : Closed t) : apply s t = t := by
  cases t with
  | var name => simp [Closed] at h
  | con name => simp [apply]
  | app ctor args =>
    simp only [apply]
    congr 1
    apply Eq.trans (b := args.map id)
    · apply List.map_congr_left
      intro a ha
      simp only [Closed] at h
      exact apply_closed s a (h a ha)
    · exact List.map_id args
termination_by sizeOf t

theorem apply_compose (outer inner : Subst) (t : MType) :
    apply (compose outer inner) t = apply outer (apply inner t) := by
  cases t with
  | var name => cases h : inner name <;> simp [apply, compose, h]
  | con name => simp [apply]
  | app ctor args =>
    simp only [apply, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact apply_compose outer inner a
termination_by sizeOf t

theorem apply_idempotent (s : Subst) (h : ClosedRange s) (t : MType) :
    apply s (apply s t) = apply s t := by
  cases t with
  | var name =>
    cases hs : s name with
    | none => simp [apply, hs]
    | some replacement => simpa [apply, hs] using apply_closed s replacement (h name replacement hs)
  | con name => simp [apply]
  | app ctor args =>
    simp only [apply, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact apply_idempotent s h a
termination_by sizeOf t

theorem apply_supported_closed (s : Subst) (hr : ClosedRange s)
    (t : MType) (ht : Supported s t) : Closed (apply s t) := by
  cases t with
  | var name =>
    simp only [Supported] at ht
    obtain ⟨replacement, hs⟩ := ht
    simpa [apply, hs] using hr name replacement hs
  | con name => simpa only [apply, Closed, Supported] using ht
  | app ctor args =>
    simp only [apply, Closed]
    simp only [Supported] at ht
    intro value hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact apply_supported_closed s hr a (ht a ha)
termination_by sizeOf t

theorem unknown_not_closed : ¬ Closed unknown := by simp [Closed, unknown]
theorem unknown_fixed (s : Subst) : apply s unknown = unknown := by simp [apply, unknown]
theorem app_owner_preserved (s : Subst) (ctor : String) (args : List MType) :
    apply s (.app ctor args) = .app ctor (args.map (apply s)) := by simp [apply]
theorem app_arity_preserved (s : Subst) (args : List MType) :
    (args.map (apply s)).length = args.length := List.length_map _

/- A bound variable can still substitute to another variable. ClosedRange
   cannot be dropped from the idempotence theorem. -/
def chain : Subst := fun name =>
  if name = "T" then some (.var "U")
  else if name = "U" then some (.con "i64") else none

theorem open_range_not_idempotent :
    apply chain (apply chain (.var "T")) ≠ apply chain (.var "T") := by
  simp [apply, chain]

/- Known constructor names do not make an unknown argument concrete. -/
theorem nested_unknown_not_closed : ¬ Closed (.app "Tuple" [unknown]) := by
  simp [Closed, unknown]

#print axioms apply_empty
#print axioms apply_closed
#print axioms apply_compose
#print axioms apply_idempotent
#print axioms apply_supported_closed
#print axioms unknown_not_closed
#print axioms unknown_fixed
#print axioms app_owner_preserved
#print axioms app_arity_preserved
#print axioms open_range_not_idempotent
#print axioms nested_unknown_not_closed

end GenericSubstModel
