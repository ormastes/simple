import Generics

/-!
# GenericsConstraints — hand-written constraints and proofs for `Generics`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `Generics` live here; the generated model lives in
`Generics.lean` and may be replaced wholesale by regeneration.
-/

namespace Generics

/- Closedness here excludes type variables. This reduced model has no unknown
   type sentinel, so this predicate does not establish production concreteness. -/
def Closed : Ty → Prop
  | .var _ => False
  | .nat | .bool | .str | .generic0 _ => True
  | .arrow a b | .generic2 _ a b => Closed a ∧ Closed b
  | .generic1 _ a => Closed a

theorem apply_closed (s : Subst) (t : Ty) (h : Closed t) :
    applySubst s t = t := by
  induction t <;> simp_all [Closed, applySubst]

def ClosedRange (s : Subst) : Prop :=
  ∀ v t, substLookup s v = some t → Closed t

/- A closed substitution range is essential: T ↦ U, U ↦ str is a
   counterexample to unconditional single-step substitution idempotence. -/
theorem apply_idempotent_of_closed_range (s : Subst) (h : ClosedRange s)
    (t : Ty) : applySubst s (applySubst s t) = applySubst s t := by
  induction t with
  | var v =>
    cases hl : substLookup s v with
    | none => simp [applySubst, hl]
    | some replacement =>
      simpa [applySubst, hl] using apply_closed s replacement (h v replacement hl)
  | _ => simp_all [applySubst]

/- Substitution preserves the nominal constructor, including nested instances.
   Production owner resolution must separately supply canonical names. -/
theorem generic1_owner_preserved (s : Subst) (name : String) (t : Ty) :
    applySubst s (.generic1 name t) = .generic1 name (applySubst s t) := rfl

theorem distinct_generic1_owners (a b : String) (x y : Ty) (h : a ≠ b) :
    Ty.generic1 a x ≠ Ty.generic1 b y := by
  intro same
  cases same
  exact h rfl

example :
    let s : Subst := [{ var := 0, ty := .var 1 }, { var := 1, ty := .str }]
    applySubst s (applySubst s (.var 0)) ≠ applySubst s (.var 0) := by
  decide

/- Print kernel dependencies in build evidence. -/
#print axioms applySubst_empty
#print axioms apply_closed
#print axioms apply_idempotent_of_closed_range
#print axioms distinct_generic1_owners

end Generics
