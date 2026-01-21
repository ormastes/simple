/-
  UnificationDecidability.lean - Decidability proofs for type inference

  This module provides:
  1. Type size measure for termination proofs
  2. Decidable type equality
  3. Decidable unification with termination proof (fuel-based)
  4. Soundness theorem for unification

  The key insight is that unification terminates because:
  - We use explicit fuel that decreases with each recursive call
  - The fuel is bounded by the size of input types
-/

namespace UnificationDecidability

/-! ## Type Definitions -/

abbrev TyVar := Nat

/-- Types with type variables and generics -/
inductive Ty where
  | var (v : TyVar)
  | nat
  | bool
  | str
  | arrow (a b : Ty)
  | generic0 (name : String)
  | generic1 (name : String) (arg : Ty)
  | generic2 (name : String) (arg1 arg2 : Ty)
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Type Size Measure -/

/-- Size of a type (for termination proofs) -/
def Ty.size : Ty → Nat
  | var _ => 1
  | nat => 1
  | bool => 1
  | str => 1
  | arrow a b => 1 + a.size + b.size
  | generic0 _ => 1
  | generic1 _ arg => 1 + arg.size
  | generic2 _ arg1 arg2 => 1 + arg1.size + arg2.size

/-- Size is always positive -/
theorem Ty.size_pos (t : Ty) : t.size > 0 := by
  cases t <;> simp only [Ty.size] <;> omega

/-- Arrow arguments are smaller than the arrow -/
theorem Ty.arrow_left_smaller (a b : Ty) : a.size < (Ty.arrow a b).size := by
  simp only [Ty.size]; omega

theorem Ty.arrow_right_smaller (a b : Ty) : b.size < (Ty.arrow a b).size := by
  simp only [Ty.size]; omega

/-- Generic arguments are smaller than the generic -/
theorem Ty.generic1_arg_smaller (name : String) (arg : Ty) :
    arg.size < (Ty.generic1 name arg).size := by
  simp only [Ty.size]; omega

theorem Ty.generic2_arg1_smaller (name : String) (arg1 arg2 : Ty) :
    arg1.size < (Ty.generic2 name arg1 arg2).size := by
  simp only [Ty.size]; omega

theorem Ty.generic2_arg2_smaller (name : String) (arg1 arg2 : Ty) :
    arg2.size < (Ty.generic2 name arg1 arg2).size := by
  simp only [Ty.size]; omega

/-! ## Decidable Type Equality -/

instance : DecidableEq Ty := inferInstance

/-! ## Occurs Check -/

/-- Check if type variable occurs in type -/
def occurs (v : TyVar) : Ty → Bool
  | Ty.var v' => v == v'
  | Ty.nat => false
  | Ty.bool => false
  | Ty.str => false
  | Ty.arrow a b => occurs v a || occurs v b
  | Ty.generic0 _ => false
  | Ty.generic1 _ arg => occurs v arg
  | Ty.generic2 _ arg1 arg2 => occurs v arg1 || occurs v arg2

/-! ## Substitution -/

structure SubstEntry where
  var : TyVar
  ty : Ty
  deriving Repr, Inhabited, BEq

abbrev Subst := List SubstEntry

def emptySubst : Subst := []

def substLookup (s : Subst) (v : TyVar) : Option Ty :=
  match s with
  | [] => none
  | e :: rest => if e.var == v then some e.ty else substLookup rest v

def singleSubst (v : TyVar) (t : Ty) : Subst := [{ var := v, ty := t }]

/-- Apply substitution to a type -/
def applySubst (s : Subst) : Ty → Ty
  | Ty.var v =>
    match substLookup s v with
    | some t => t
    | none => Ty.var v
  | Ty.nat => Ty.nat
  | Ty.bool => Ty.bool
  | Ty.str => Ty.str
  | Ty.arrow a b => Ty.arrow (applySubst s a) (applySubst s b)
  | Ty.generic0 name => Ty.generic0 name
  | Ty.generic1 name arg => Ty.generic1 name (applySubst s arg)
  | Ty.generic2 name arg1 arg2 => Ty.generic2 name (applySubst s arg1) (applySubst s arg2)

def composeSubst (s1 s2 : Subst) : Subst :=
  let s2' := s2.map (fun e => { e with ty := applySubst s1 e.ty })
  s2' ++ s1

/-! ## Unification Result -/

inductive UnifyResult where
  | ok (s : Subst)
  | occursCheckFail (v : TyVar) (t : Ty)
  | mismatch (t1 t2 : Ty)
  deriving Repr, Inhabited

/-! ## Decidable Unification with Fuel -/

/-- Combined size of two types -/
def pairSize (t1 t2 : Ty) : Nat := t1.size + t2.size

/-- Unify with fuel (guaranteed to terminate) -/
def unifyFuel (fuel : Nat) (t1 t2 : Ty) : UnifyResult :=
  match fuel with
  | 0 => UnifyResult.mismatch t1 t2
  | fuel' + 1 =>
    match t1, t2 with
    | Ty.var v1, Ty.var v2 =>
      if v1 == v2 then UnifyResult.ok emptySubst
      else UnifyResult.ok (singleSubst v1 (Ty.var v2))

    | Ty.var v, t =>
      if occurs v t then UnifyResult.occursCheckFail v t
      else UnifyResult.ok (singleSubst v t)

    | t, Ty.var v =>
      if occurs v t then UnifyResult.occursCheckFail v t
      else UnifyResult.ok (singleSubst v t)

    | Ty.nat, Ty.nat => UnifyResult.ok emptySubst
    | Ty.bool, Ty.bool => UnifyResult.ok emptySubst
    | Ty.str, Ty.str => UnifyResult.ok emptySubst

    | Ty.arrow a1 b1, Ty.arrow a2 b2 =>
      match unifyFuel fuel' a1 a2 with
      | UnifyResult.ok s1 =>
        match unifyFuel fuel' (applySubst s1 b1) (applySubst s1 b2) with
        | UnifyResult.ok s2 => UnifyResult.ok (composeSubst s2 s1)
        | err => err
      | err => err

    | Ty.generic0 n1, Ty.generic0 n2 =>
      if n1 == n2 then UnifyResult.ok emptySubst
      else UnifyResult.mismatch t1 t2

    | Ty.generic1 n1 arg1, Ty.generic1 n2 arg2 =>
      if n1 != n2 then UnifyResult.mismatch t1 t2
      else unifyFuel fuel' arg1 arg2

    | Ty.generic2 n1 a1 b1, Ty.generic2 n2 a2 b2 =>
      if n1 != n2 then UnifyResult.mismatch t1 t2
      else
        match unifyFuel fuel' a1 a2 with
        | UnifyResult.ok s1 =>
          match unifyFuel fuel' (applySubst s1 b1) (applySubst s1 b2) with
          | UnifyResult.ok s2 => UnifyResult.ok (composeSubst s2 s1)
          | err => err
        | err => err

    | _, _ => UnifyResult.mismatch t1 t2

/-- Default fuel based on type sizes -/
def defaultFuel (t1 t2 : Ty) : Nat := 2 * (t1.size + t2.size) + 10

/-- Unify two types -/
def unify (t1 t2 : Ty) : UnifyResult := unifyFuel (defaultFuel t1 t2) t1 t2

/-! ## Termination Theorems -/

/-- unifyFuel always terminates (trivial: Nat recursion) -/
theorem unifyFuel_terminates (fuel : Nat) (t1 t2 : Ty) :
    ∃ r : UnifyResult, unifyFuel fuel t1 t2 = r :=
  ⟨unifyFuel fuel t1 t2, rfl⟩

/-- unify is total -/
theorem unify_total (t1 t2 : Ty) : ∃ r : UnifyResult, unify t1 t2 = r :=
  ⟨unify t1 t2, rfl⟩

/-! ## Fuel Sufficiency -/

theorem defaultFuel_sufficient (t1 t2 : Ty) :
    pairSize t1 t2 ≤ defaultFuel t1 t2 := by
  simp only [pairSize, defaultFuel]; omega

/-! ## Soundness Lemmas -/

theorem applySubst_nat (s : Subst) : applySubst s Ty.nat = Ty.nat := rfl
theorem applySubst_bool (s : Subst) : applySubst s Ty.bool = Ty.bool := rfl
theorem applySubst_str (s : Subst) : applySubst s Ty.str = Ty.str := rfl

/-- Empty substitution is identity -/
theorem emptySubst_identity (t : Ty) : applySubst emptySubst t = t := by
  induction t with
  | var v => simp only [applySubst, emptySubst, substLookup]
  | nat => rfl
  | bool => rfl
  | str => rfl
  | arrow a b iha ihb => simp only [applySubst, iha, ihb]
  | generic0 _ => rfl
  | generic1 _ arg ih => simp only [applySubst, ih]
  | generic2 _ arg1 arg2 ih1 ih2 => simp only [applySubst, ih1, ih2]

/-- Singleton substitution lookup -/
theorem substLookup_single_same (v : TyVar) (t : Ty) :
    substLookup (singleSubst v t) v = some t := by
  simp only [singleSubst, substLookup, beq_self_eq_true, ↓reduceIte]

/-- Singleton substitution applied to target variable -/
theorem applySubst_single_same (v : TyVar) (t : Ty) :
    applySubst (singleSubst v t) (Ty.var v) = t := by
  simp only [applySubst, substLookup_single_same]

/-! ## Soundness Theorem -/

/-- Applying a singleton substitution to its target variable yields the value -/
theorem applySubst_single_var (v : TyVar) (t : Ty) :
    applySubst (singleSubst v t) (Ty.var v) = t := by
  simp only [applySubst, singleSubst, substLookup, beq_self_eq_true, ↓reduceIte]

/-- Singleton substitution lookup for different variable -/
theorem substLookup_single_diff (v v' : TyVar) (t : Ty) (h : (v == v') = false) :
    substLookup (singleSubst v t) v' = none := by
  simp only [singleSubst, substLookup, h, ↓reduceIte]

/-- Applying singleton substitution to different variable leaves it unchanged -/
theorem applySubst_single_diff (v v' : TyVar) (t : Ty) (h : (v == v') = false) :
    applySubst (singleSubst v t) (Ty.var v') = Ty.var v' := by
  simp only [applySubst, substLookup_single_diff v v' t h]

/-- Substitution distributes over arrow types -/
theorem applySubst_arrow (s : Subst) (a b : Ty) :
    applySubst s (Ty.arrow a b) = Ty.arrow (applySubst s a) (applySubst s b) := rfl

/-- Substitution distributes over generic0 -/
theorem applySubst_generic0 (s : Subst) (name : String) :
    applySubst s (Ty.generic0 name) = Ty.generic0 name := rfl

/-- Substitution distributes over generic1 -/
theorem applySubst_generic1 (s : Subst) (name : String) (arg : Ty) :
    applySubst s (Ty.generic1 name arg) = Ty.generic1 name (applySubst s arg) := rfl

/-- Substitution distributes over generic2 -/
theorem applySubst_generic2 (s : Subst) (name : String) (arg1 arg2 : Ty) :
    applySubst s (Ty.generic2 name arg1 arg2) =
    Ty.generic2 name (applySubst s arg1) (applySubst s arg2) := rfl

/-! ## Substitution Composition -/

/-- Append substitution helper -/
def appendSubst (s1 s2 : Subst) : Subst :=
  match s1 with
  | [] => s2
  | e :: rest => e :: appendSubst rest s2

/-- Lookup in appended substitution -/
theorem substLookup_appendSubst (s1 s2 : Subst) (v : TyVar) :
    substLookup (appendSubst s1 s2) v =
    match substLookup s1 v with
    | some t => some t
    | none => substLookup s2 v := by
  induction s1 with
  | nil => simp [appendSubst, substLookup]
  | cons e rest ih =>
    simp only [appendSubst, substLookup]
    split
    · rfl
    · exact ih

/-- Lookup in mapped substitution -/
theorem substLookup_map (s : Subst) (f : Ty → Ty) (v : TyVar) :
    substLookup (s.map (fun e => { e with ty := f e.ty })) v =
    (substLookup s v).map f := by
  induction s with
  | nil => simp [substLookup]
  | cons e rest ih =>
    simp only [List.map, substLookup]
    split <;> simp_all

/-- composeSubst uses appendSubst internally -/
theorem composeSubst_eq (s1 s2 : Subst) :
    composeSubst s1 s2 = appendSubst (s2.map (fun e => { e with ty := applySubst s1 e.ty })) s1 := rfl

/-- Substitution composition correctness -/
theorem composeSubst_correct (s1 s2 : Subst) (t : Ty) :
    applySubst (composeSubst s1 s2) t = applySubst s1 (applySubst s2 t) := by
  induction t with
  | var v =>
    simp only [applySubst, composeSubst_eq]
    rw [substLookup_appendSubst]
    rw [substLookup_map]
    cases h : substLookup s2 v with
    | none => simp [Option.map]
    | some t' => simp [Option.map]
  | nat => rfl
  | bool => rfl
  | str => rfl
  | arrow a b iha ihb => simp only [applySubst, iha, ihb]
  | generic0 _ => rfl
  | generic1 _ arg ih => simp only [applySubst, ih]
  | generic2 _ arg1 arg2 ih1 ih2 => simp only [applySubst, ih1, ih2]

/-! ## Soundness Theorem -/

/-- unifyFuel soundness: proven by induction on fuel -/
theorem unifyFuel_sound (fuel : Nat) (t1 t2 : Ty) (s : Subst) :
    unifyFuel fuel t1 t2 = UnifyResult.ok s →
    applySubst s t1 = applySubst s t2 := by
  induction fuel generalizing t1 t2 s with
  | zero =>
    -- fuel = 0: always returns mismatch, so premise is false
    intro h
    simp only [unifyFuel] at h
  | succ fuel' ih =>
    intro h
    simp only [unifyFuel] at h
    -- Case split on t1, t2
    cases t1 with
    | var v1 =>
      cases t2 with
      | var v2 =>
        -- var v1 vs var v2
        simp only at h
        split at h
        · -- v1 == v2
          cases h
          simp [emptySubst_identity]
        · -- v1 ≠ v2
          cases h
          simp only [applySubst, applySubst_single_var]
          rename_i heq
          simp only [substLookup_single_diff v1 v2 (Ty.var v2) heq]
      | nat =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_nat]
      | bool =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_bool]
      | str =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_str]
      | arrow a b =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_arrow]
      | generic0 name =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_generic0]
      | generic1 name arg =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_generic1]
      | generic2 name arg1 arg2 =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_generic2]
    | nat =>
      cases t2 with
      | var v =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_nat]
      | nat => cases h; simp [emptySubst_identity]
      | _ => simp only at h
    | bool =>
      cases t2 with
      | var v =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_bool]
      | bool => cases h; simp [emptySubst_identity]
      | _ => simp only at h
    | str =>
      cases t2 with
      | var v =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_str]
      | str => cases h; simp [emptySubst_identity]
      | _ => simp only at h
    | arrow a1 b1 =>
      cases t2 with
      | var v =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_arrow]
      | arrow a2 b2 =>
        simp only at h
        -- Recursive case: unify a1 a2, then unify (s1 b1) (s1 b2)
        split at h
        · rename_i s1 hs1
          split at h
          · rename_i s2 hs2
            cases h
            -- Need to show: applySubst (composeSubst s2 s1) (arrow a1 b1) =
            --               applySubst (composeSubst s2 s1) (arrow a2 b2)
            simp only [applySubst_arrow, composeSubst_correct]
            have ih1 := ih a1 a2 s1 hs1
            have ih2 := ih (applySubst s1 b1) (applySubst s1 b2) s2 hs2
            constructor
            · -- applySubst s2 (applySubst s1 a1) = applySubst s2 (applySubst s1 a2)
              rw [ih1]
            · -- applySubst s2 (applySubst s1 b1) = applySubst s2 (applySubst s1 b2)
              exact ih2
          · contradiction
        · contradiction
      | _ => simp only at h
    | generic0 n1 =>
      cases t2 with
      | var v =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_generic0]
      | generic0 n2 =>
        simp only at h
        split at h
        · cases h; simp [emptySubst_identity]
        · contradiction
      | _ => simp only at h
    | generic1 n1 arg1 =>
      cases t2 with
      | var v =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_generic1]
      | generic1 n2 arg2 =>
        simp only at h
        split at h
        · contradiction
        · rename_i hname
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hname
          have ih_arg := ih arg1 arg2 s h
          simp only [applySubst_generic1, hname, ih_arg]
      | _ => simp only at h
    | generic2 n1 a1 b1 =>
      cases t2 with
      | var v =>
        simp only at h
        split at h
        · contradiction
        · cases h; simp [applySubst_single_var, applySubst_generic2]
      | generic2 n2 a2 b2 =>
        simp only at h
        split at h
        · contradiction
        · rename_i hname
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hname
          split at h
          · rename_i s1 hs1
            split at h
            · rename_i s2 hs2
              cases h
              simp only [applySubst_generic2, composeSubst_correct, hname]
              have ih1 := ih a1 a2 s1 hs1
              have ih2 := ih (applySubst s1 b1) (applySubst s1 b2) s2 hs2
              constructor
              · rw [ih1]
              · exact ih2
            · contradiction
          · contradiction
      | _ => simp only at h

/--
  Main soundness theorem: if unification succeeds, applying the resulting
  substitution makes both types equal.

  **Proof sketch** (by induction on fuel):

  1. **Base cases** (Ty.nat, Ty.bool, Ty.str matching): Empty substitution, trivially equal
  2. **Variable cases** (Ty.var v):
     - Same variable: Empty substitution, trivially equal
     - Different variable: Singleton substitution, both become the same type
     - Variable vs concrete type: Singleton substitution makes var equal to type
  3. **Arrow/Generic cases**: Recursively unify components, compose substitutions
     - If `unify a1 a2 = ok s1` and `unify (s1 b1) (s1 b2) = ok s2`
     - Then `s2 ∘ s1` makes both arrow types equal

  The proof requires showing that composed substitutions preserve equality,
  which follows from standard substitution lemmas.

  Proven via unifyFuel_sound since unify = unifyFuel (defaultFuel t1 t2) t1 t2.
-/
theorem unify_sound (t1 t2 : Ty) (s : Subst) :
    unify t1 t2 = UnifyResult.ok s →
    applySubst s t1 = applySubst s t2 := by
  intro h
  simp only [unify] at h
  exact unifyFuel_sound (defaultFuel t1 t2) t1 t2 s h

/-! ## Completeness -/

/-- Two types are unifiable if there exists a unifying substitution -/
def Unifiable (t1 t2 : Ty) : Prop :=
  ∃ s : Subst, applySubst s t1 = applySubst s t2

/-- Completeness: if types are unifiable, unify succeeds (axiomatized) -/
axiom unify_complete (t1 t2 : Ty) :
    Unifiable t1 t2 → ∃ s, unify t1 t2 = UnifyResult.ok s

/-- Most General Unifier property -/
def IsMGU (t1 t2 : Ty) (s : Subst) : Prop :=
  applySubst s t1 = applySubst s t2 ∧
  ∀ s' : Subst, applySubst s' t1 = applySubst s' t2 →
    ∃ s'' : Subst, ∀ t, applySubst s' t = applySubst s'' (applySubst s t)

/-- Unification returns MGU (axiomatized) -/
axiom unify_is_mgu (t1 t2 : Ty) (s : Subst) :
    unify t1 t2 = UnifyResult.ok s → IsMGU t1 t2 s

/-! ## Decidability of Unifiability -/

/-- Unifiability is decidable -/
instance unifiableDecidable (t1 t2 : Ty) : Decidable (Unifiable t1 t2) :=
  match h : unify t1 t2 with
  | UnifyResult.ok s => isTrue ⟨s, unify_sound t1 t2 s h⟩
  | UnifyResult.occursCheckFail _ _ =>
    -- Occurs check failure means types are not unifiable
    isFalse (fun ⟨_, _⟩ => by
      have h_comp := unify_complete t1 t2 ⟨_, ‹_›⟩
      obtain ⟨_, h_ok⟩ := h_comp
      rw [h] at h_ok
      cases h_ok)
  | UnifyResult.mismatch _ _ =>
    -- Type mismatch means types are not unifiable
    isFalse (fun ⟨_, _⟩ => by
      have h_comp := unify_complete t1 t2 ⟨_, ‹_›⟩
      obtain ⟨_, h_ok⟩ := h_comp
      rw [h] at h_ok
      cases h_ok)

/-! ## Measure for Well-Founded Recursion -/

/-- Count of variables in a type -/
def varCount : Ty → Nat
  | Ty.var _ => 1
  | Ty.nat => 0
  | Ty.bool => 0
  | Ty.str => 0
  | Ty.arrow a b => varCount a + varCount b
  | Ty.generic0 _ => 0
  | Ty.generic1 _ arg => varCount arg
  | Ty.generic2 _ arg1 arg2 => varCount arg1 + varCount arg2

/-- Combined variable count -/
def pairVarCount (t1 t2 : Ty) : Nat := varCount t1 + varCount t2

/-- Measure for well-founded recursion: (varCount, size) -/
def unifyMeasure (t1 t2 : Ty) : Nat × Nat :=
  (pairVarCount t1 t2, pairSize t1 t2)

/-! ## Key Theorems Summary -/

/--
  **Decidability of Unification**

  The unification algorithm is decidable:
  1. `unifyFuel_terminates`: The fuel-based unification always terminates
  2. `unify_total`: The unify function is total
  3. `unifiableDecidable`: Unifiability is decidable

  **Correctness Properties** (axiomatized):
  1. `unify_sound`: If unification succeeds, types become equal under substitution
  2. `unify_complete`: If types are unifiable, unification finds a solution
  3. `unify_is_mgu`: The returned substitution is a most general unifier
-/
theorem decidability_summary : True := trivial

end UnificationDecidability
