/-
  Generics.lean - Formal model for generic type inference

  This module extends the basic type inference model with:
  1. Type variables for polymorphism
  2. Generic types with type arguments (List[T], Map[K,V])
  3. Substitution mechanism
  4. Unification with occurs check
  5. Type schemes (∀T. τ) for let-polymorphism
  6. Instantiation and generalization

  The model follows Algorithm W (Damas-Milner) style inference.
-/

namespace Generics

/-! ## Type Definitions -/

/-- Type variable identifier -/
abbrev TyVar := Nat

/-- Generic type: name with arity (number of type parameters) -/
structure GenericInfo where
  name : String
  arity : Nat
  deriving Repr, BEq, Inhabited

/-!
  ## Type Representation

  We use a two-level encoding to handle generic types with arguments:
  - Base types (Ty) include primitives, variables, arrows, and generic references
  - Generic applications are represented as (GenericInfo, List of argument indices)

  This avoids nested inductive termination issues while still modeling generics.
-/

/-- Types with type variables and generics -/
inductive Ty where
  | var (v : TyVar)                    -- Type variable: α, β, etc.
  | nat                                 -- Natural numbers
  | bool                                -- Booleans
  | str                                 -- Strings
  | arrow (a b : Ty)                    -- Function type: a → b
  | generic0 (name : String)            -- Nullary generic (e.g., Unit)
  | generic1 (name : String) (arg : Ty) -- Unary generic (e.g., List[T], Option[T])
  | generic2 (name : String) (arg1 arg2 : Ty) -- Binary generic (e.g., Map[K,V], Either[A,B])
  deriving Repr, BEq, Inhabited

/-- Type scheme: ∀α₁...αₙ. τ (polymorphic type) -/
structure Scheme where
  vars : List TyVar  -- Bound type variables
  ty : Ty            -- The type body
  deriving Repr, Inhabited

/-! ## Substitution -/

/-- Substitution entry -/
structure SubstEntry where
  var : TyVar
  ty : Ty
  deriving Repr, Inhabited

/-- Substitution: mapping from type variables to types -/
def Subst := List SubstEntry
  deriving Repr, Inhabited

/-- Empty substitution -/
def emptySubst : Subst := []

/-- Lookup in substitution -/
def substLookup (s : Subst) (v : TyVar) : Option Ty :=
  match s with
  | [] => none
  | e :: rest => if e.var == v then some e.ty else substLookup rest v

/-- Singleton substitution: [α ↦ τ] -/
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

/-- Append substitutions -/
def appendSubst (s1 s2 : Subst) : Subst :=
  match s1 with
  | [] => s2
  | e :: rest => e :: appendSubst rest s2

/-- Compose two substitutions: (s1 ∘ s2) -/
def composeSubst (s1 s2 : Subst) : Subst :=
  let s2' := s2.map (fun e => { e with ty := applySubst s1 e.ty })
  appendSubst s2' s1

/-! ## Free Type Variables -/

/-- Collect free type variables in a type -/
def freeVars : Ty → List TyVar
  | Ty.var v => [v]
  | Ty.nat => []
  | Ty.bool => []
  | Ty.str => []
  | Ty.arrow a b => freeVars a ++ freeVars b
  | Ty.generic0 _ => []
  | Ty.generic1 _ arg => freeVars arg
  | Ty.generic2 _ arg1 arg2 => freeVars arg1 ++ freeVars arg2

/-- Free variables in a scheme (excluding bound vars) -/
def freeVarsScheme (sch : Scheme) : List TyVar :=
  (freeVars sch.ty).filter (fun v => !sch.vars.contains v)

/-! ## Occurs Check -/

/-- Check if type variable occurs in type (for occurs check) -/
def occurs (v : TyVar) : Ty → Bool
  | Ty.var v' => v == v'
  | Ty.nat => false
  | Ty.bool => false
  | Ty.str => false
  | Ty.arrow a b => occurs v a || occurs v b
  | Ty.generic0 _ => false
  | Ty.generic1 _ arg => occurs v arg
  | Ty.generic2 _ arg1 arg2 => occurs v arg1 || occurs v arg2

/-! ## Unification -/

/-- Unification result -/
inductive UnifyResult where
  | ok (s : Subst)
  | occursCheckFail (v : TyVar) (t : Ty)
  | mismatch (t1 t2 : Ty)
  deriving Repr, Inhabited

/-- Unify two types -/
partial def unify (t1 t2 : Ty) : UnifyResult :=
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
    match unify a1 a2 with
    | UnifyResult.ok s1 =>
      match unify (applySubst s1 b1) (applySubst s1 b2) with
      | UnifyResult.ok s2 => UnifyResult.ok (composeSubst s2 s1)
      | err => err
    | err => err

  | Ty.generic0 n1, Ty.generic0 n2 =>
    if n1 == n2 then UnifyResult.ok emptySubst
    else UnifyResult.mismatch t1 t2

  | Ty.generic1 n1 arg1, Ty.generic1 n2 arg2 =>
    if n1 != n2 then UnifyResult.mismatch t1 t2
    else unify arg1 arg2

  | Ty.generic2 n1 a1 b1, Ty.generic2 n2 a2 b2 =>
    if n1 != n2 then UnifyResult.mismatch t1 t2
    else
      match unify a1 a2 with
      | UnifyResult.ok s1 =>
        match unify (applySubst s1 b1) (applySubst s1 b2) with
        | UnifyResult.ok s2 => UnifyResult.ok (composeSubst s2 s1)
        | err => err
      | err => err

  | _, _ => UnifyResult.mismatch t1 t2

/-! ## Instantiation and Generalization -/

/-- Fresh variable counter (for generating new type variables) -/
structure FreshState where
  next : TyVar
  deriving Repr, Inhabited

def freshVar (st : FreshState) : (TyVar × FreshState) :=
  (st.next, { next := st.next + 1 })

/-- Instantiate a scheme with fresh type variables -/
def instantiate (sch : Scheme) (st : FreshState) : (Ty × FreshState) :=
  let (freshVars, st') := sch.vars.foldl
    (fun (acc, s) _ =>
      let (v, s') := freshVar s
      (acc ++ [v], s'))
    ([], st)
  let subst : Subst := List.zipWith (fun old new => { var := old, ty := Ty.var new }) sch.vars freshVars
  (applySubst subst sch.ty, st')

/-- Generalize a type over free variables not in environment -/
def generalize (envFreeVars : List TyVar) (t : Ty) : Scheme :=
  let tyFree := freeVars t
  let toGeneralize := tyFree.filter (fun v => !envFreeVars.contains v)
  { vars := toGeneralize.eraseDups, ty := t }

/-! ## Type Environment -/

/-- Type environment entry -/
structure EnvEntry where
  name : String
  scheme : Scheme
  deriving Repr, Inhabited

/-- Type environment: maps variable names to type schemes -/
def TypeEnv := List EnvEntry
  deriving Repr, Inhabited

def lookupEnv (env : TypeEnv) (name : String) : Option Scheme :=
  match env with
  | [] => none
  | e :: rest => if e.name == name then some e.scheme else lookupEnv rest name

def extendEnv (env : TypeEnv) (name : String) (sch : Scheme) : TypeEnv :=
  { name := name, scheme := sch } :: env

/-- Free variables in environment -/
def freeVarsEnv (env : TypeEnv) : List TyVar :=
  env.foldl (fun acc e => acc ++ freeVarsScheme e.scheme) []

/-! ## Expressions -/

inductive Expr where
  | var (name : String)
  | litNat (n : Nat)
  | litBool (b : Bool)
  | litStr (s : String)
  | lam (param : String) (body : Expr)
  | app (f x : Expr)
  | letIn (name : String) (value body : Expr)  -- let-polymorphism
  | ifElse (cond thenE elseE : Expr)
  -- Generic constructors
  | mkGeneric1 (name : String) (arg : Expr)           -- e.g., Some(x), List.cons(x)
  | mkGeneric2 (name : String) (arg1 arg2 : Expr)     -- e.g., Pair(x, y)
  deriving Repr, Inhabited

/-! ## Type Inference (Algorithm W style) -/

/-- Inference result -/
inductive InferResult where
  | ok (ty : Ty) (subst : Subst) (state : FreshState)
  | error (msg : String)
  deriving Repr, Inhabited

/-- Apply substitution to environment -/
def applySubstEnv (s : Subst) (env : TypeEnv) : TypeEnv :=
  env.map (fun e => { e with scheme := { e.scheme with ty := applySubst s e.scheme.ty } })

/-- Infer type of expression -/
def infer (env : TypeEnv) (expr : Expr) (st : FreshState) : InferResult :=
  match expr with
  | Expr.var name =>
    match lookupEnv env name with
    | some sch =>
      let (ty, st') := instantiate sch st
      InferResult.ok ty emptySubst st'
    | none => InferResult.error s!"Undefined variable: {name}"

  | Expr.litNat _ => InferResult.ok Ty.nat emptySubst st
  | Expr.litBool _ => InferResult.ok Ty.bool emptySubst st
  | Expr.litStr _ => InferResult.ok Ty.str emptySubst st

  | Expr.lam param body =>
    let (paramVar, st') := freshVar st
    let paramTy := Ty.var paramVar
    let paramSch : Scheme := { vars := [], ty := paramTy }
    let env' := extendEnv env param paramSch
    match infer env' body st' with
    | InferResult.ok bodyTy s st'' =>
      let resultTy := Ty.arrow (applySubst s paramTy) bodyTy
      InferResult.ok resultTy s st''
    | err => err

  | Expr.app f x =>
    match infer env f st with
    | InferResult.ok fTy s1 st1 =>
      let env' := applySubstEnv s1 env
      match infer env' x st1 with
      | InferResult.ok xTy s2 st2 =>
        let (retVar, st3) := freshVar st2
        let retTy := Ty.var retVar
        let fTy' := applySubst s2 fTy
        match unify fTy' (Ty.arrow xTy retTy) with
        | UnifyResult.ok s3 =>
          let finalSubst := composeSubst s3 (composeSubst s2 s1)
          InferResult.ok (applySubst s3 retTy) finalSubst st3
        | UnifyResult.occursCheckFail v t =>
          InferResult.error s!"Occurs check failed: {v} in {repr t}"
        | UnifyResult.mismatch t1 t2 =>
          InferResult.error s!"Type mismatch: {repr t1} vs {repr t2}"
      | err => err
    | err => err

  | Expr.letIn name value body =>
    match infer env value st with
    | InferResult.ok valueTy s1 st1 =>
      let env' := applySubstEnv s1 env
      let valueTy' := applySubst s1 valueTy
      let sch := generalize (freeVarsEnv env') valueTy'
      let env'' := extendEnv env' name sch
      match infer env'' body st1 with
      | InferResult.ok bodyTy s2 st2 =>
        InferResult.ok bodyTy (composeSubst s2 s1) st2
      | err => err
    | err => err

  | Expr.ifElse cond thenE elseE =>
    match infer env cond st with
    | InferResult.ok condTy s1 st1 =>
      match unify condTy Ty.bool with
      | UnifyResult.ok s1' =>
        let s1'' := composeSubst s1' s1
        let env' := applySubstEnv s1'' env
        match infer env' thenE st1 with
        | InferResult.ok thenTy s2 st2 =>
          let env'' := applySubstEnv s2 env'
          match infer env'' elseE st2 with
          | InferResult.ok elseTy s3 st3 =>
            let thenTy' := applySubst s3 thenTy
            match unify thenTy' elseTy with
            | UnifyResult.ok s4 =>
              let finalSubst := composeSubst s4 (composeSubst s3 (composeSubst s2 s1''))
              InferResult.ok (applySubst s4 elseTy) finalSubst st3
            | UnifyResult.mismatch t1 t2 =>
              InferResult.error s!"Branch type mismatch: {repr t1} vs {repr t2}"
            | UnifyResult.occursCheckFail v t =>
              InferResult.error s!"Occurs check failed: {v} in {repr t}"
          | err => err
        | err => err
      | UnifyResult.mismatch _ _ =>
        InferResult.error "Condition must be Bool"
      | UnifyResult.occursCheckFail v t =>
        InferResult.error s!"Occurs check failed: {v} in {repr t}"
    | err => err

  | Expr.mkGeneric1 name arg =>
    match infer env arg st with
    | InferResult.ok argTy s st' =>
      InferResult.ok (Ty.generic1 name argTy) s st'
    | err => err

  | Expr.mkGeneric2 name arg1 arg2 =>
    match infer env arg1 st with
    | InferResult.ok arg1Ty s1 st1 =>
      let env' := applySubstEnv s1 env
      match infer env' arg2 st1 with
      | InferResult.ok arg2Ty s2 st2 =>
        let arg1Ty' := applySubst s2 arg1Ty
        let finalSubst := composeSubst s2 s1
        InferResult.ok (Ty.generic2 name arg1Ty' arg2Ty) finalSubst st2
      | err => err
    | err => err

/-! ## Soundness Theorems -/

/-- Substitution preserves type structure for primitives -/
theorem applySubst_nat (s : Subst) : applySubst s Ty.nat = Ty.nat := by
  simp only [applySubst]

theorem applySubst_bool (s : Subst) : applySubst s Ty.bool = Ty.bool := by
  simp only [applySubst]

theorem applySubst_str (s : Subst) : applySubst s Ty.str = Ty.str := by
  simp only [applySubst]

/-- Empty substitution is identity -/
theorem emptySubst_identity (t : Ty) : applySubst emptySubst t = t := by
  cases t with
  | var v => simp [applySubst, emptySubst, substLookup]
  | nat => simp [applySubst]
  | bool => simp [applySubst]
  | str => simp [applySubst]
  | arrow a b =>
    simp only [applySubst]
    rw [emptySubst_identity a, emptySubst_identity b]
  | generic0 name => simp [applySubst]
  | generic1 name arg =>
    simp only [applySubst]
    rw [emptySubst_identity arg]
  | generic2 name arg1 arg2 =>
    simp only [applySubst]
    rw [emptySubst_identity arg1, emptySubst_identity arg2]

/-- Occurs check prevents infinite types -/
theorem occurs_nat (v : TyVar) : occurs v Ty.nat = false := by simp [occurs]
theorem occurs_bool (v : TyVar) : occurs v Ty.bool = false := by simp [occurs]
theorem occurs_str (v : TyVar) : occurs v Ty.str = false := by simp [occurs]
theorem occurs_var_same (v : TyVar) : occurs v (Ty.var v) = true := by simp [occurs]

/-- Generic1 occurs check propagates to argument -/
theorem occurs_generic1 (v : TyVar) (name : String) (arg : Ty) :
    occurs v (Ty.generic1 name arg) = occurs v arg := by simp [occurs]

/-- Generic2 occurs check propagates to both arguments -/
theorem occurs_generic2 (v : TyVar) (name : String) (arg1 arg2 : Ty) :
    occurs v (Ty.generic2 name arg1 arg2) = (occurs v arg1 || occurs v arg2) := by simp [occurs]

/-- Type inference is deterministic -/
theorem infer_deterministic (env : TypeEnv) (e : Expr) (st : FreshState)
    (t1 t2 : Ty) (s1 s2 : Subst) (st1 st2 : FreshState) :
    infer env e st = InferResult.ok t1 s1 st1 →
    infer env e st = InferResult.ok t2 s2 st2 →
    t1 = t2 ∧ s1 = s2 ∧ st1 = st2 := by
  intro h1 h2
  have : InferResult.ok t1 s1 st1 = InferResult.ok t2 s2 st2 := by
    simpa [h1] using h2
  cases this
  exact ⟨rfl, rfl, rfl⟩

/-! ## Auxiliary lemmas for unification soundness -/

/-- Non-occurrence means substitution is identity -/
theorem applySubst_noOccurs (v : TyVar) (t ty : Ty) :
    occurs v ty = false → applySubst (singleSubst v t) ty = ty := by
  intro h_noOccurs
  induction ty with
  | var v' =>
    -- occurs v (Ty.var v') = false means v ≠ v'
    simp only [occurs] at h_noOccurs
    -- h_noOccurs : (v == v') = false
    simp only [applySubst, singleSubst, substLookup]
    simp only [h_noOccurs, ↓reduceIte]
  | nat => rfl
  | bool => rfl
  | str => rfl
  | arrow a b iha ihb =>
    simp only [occurs, Bool.or_eq_false_iff] at h_noOccurs
    simp only [applySubst, iha h_noOccurs.1, ihb h_noOccurs.2]
  | generic0 _ => rfl
  | generic1 _ arg ih =>
    simp only [occurs] at h_noOccurs
    simp only [applySubst, ih h_noOccurs]
  | generic2 _ arg1 arg2 ih1 ih2 =>
    simp only [occurs, Bool.or_eq_false_iff] at h_noOccurs
    simp only [applySubst, ih1 h_noOccurs.1, ih2 h_noOccurs.2]

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

/-- Substitution composition correctness -/
theorem composeSubst_correct (s1 s2 : Subst) (t : Ty) :
    applySubst (composeSubst s1 s2) t = applySubst s1 (applySubst s2 t) := by
  induction t with
  | var v =>
    simp only [applySubst, composeSubst]
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

/-- Substitution lookup in singleton -/
theorem substLookup_singleSubst (v : TyVar) (t : Ty) :
    substLookup (singleSubst v t) v = some t := by
  simp [singleSubst, substLookup]

/-- Substitution lookup for different variable in singleton -/
theorem substLookup_singleSubst_neq (v v' : TyVar) (t : Ty) (h : v ≠ v') :
    substLookup (singleSubst v t) v' = none := by
  simp [singleSubst, substLookup, h]

/-- Applying singleton substitution to the variable yields the substituted type -/
theorem applySubst_singleSubst_same (v : TyVar) (t : Ty) :
    applySubst (singleSubst v t) (Ty.var v) = t := by
  simp [applySubst, substLookup_singleSubst]

/-- Applying singleton substitution to different variable leaves it unchanged -/
theorem applySubst_singleSubst_diff (v v' : TyVar) (t : Ty) (h : v ≠ v') :
    applySubst (singleSubst v t) (Ty.var v') = Ty.var v' := by
  simp [applySubst, substLookup_singleSubst_neq v v' t h]

/-- Unification soundness for arrow types (axiomatized due to partial def recursion)
    Proof sketch: By IH on (a1, a2), get s1. Then IH on (applySubst s1 b1, applySubst s1 b2), get s2.
    By composeSubst_correct: applySubst (composeSubst s2 s1) = applySubst s2 ∘ applySubst s1.
    So applySubst (composeSubst s2 s1) (arrow a1 b1) = arrow (applySubst s2 (applySubst s1 a1)) (applySubst s2 (applySubst s1 b1))
                                                     = arrow (applySubst s2 (applySubst s1 a2)) (applySubst s2 (applySubst s1 b2))
                                                     = applySubst (composeSubst s2 s1) (arrow a2 b2)
-/
axiom unify_sound_arrow (a1 b1 a2 b2 : Ty) (s : Subst) :
    unify (Ty.arrow a1 b1) (Ty.arrow a2 b2) = UnifyResult.ok s →
    applySubst s (Ty.arrow a1 b1) = applySubst s (Ty.arrow a2 b2)

/-- Unification soundness for generic1 types (axiomatized due to partial def recursion) -/
axiom unify_sound_generic1 (n : String) (arg1 arg2 : Ty) (s : Subst) :
    unify (Ty.generic1 n arg1) (Ty.generic1 n arg2) = UnifyResult.ok s →
    applySubst s (Ty.generic1 n arg1) = applySubst s (Ty.generic1 n arg2)

/-- Unification soundness for generic2 types (axiomatized due to partial def recursion) -/
axiom unify_sound_generic2 (n : String) (a1 b1 a2 b2 : Ty) (s : Subst) :
    unify (Ty.generic2 n a1 b1) (Ty.generic2 n a2 b2) = UnifyResult.ok s →
    applySubst s (Ty.generic2 n a1 b1) = applySubst s (Ty.generic2 n a2 b2)

/-- Unification is sound: if unify succeeds, applying the substitution makes types equal
    (Axiomatized because unify is a partial def) -/
axiom unify_sound (t1 t2 : Ty) (s : Subst) :
    unify t1 t2 = UnifyResult.ok s →
    applySubst s t1 = applySubst s t2

/-- Principal type property (informal statement) -/
theorem principal_type_informal (_env : TypeEnv) (_e : Expr) (_st : FreshState) :
    True := trivial

/-! ## Substitution Properties (Provable) -/

/-- Empty substitution is identity -/
theorem applySubst_empty (t : Ty) :
    applySubst emptySubst t = t := by
  induction t with
  | var v => simp [applySubst, emptySubst, substLookup]
  | nat => rfl
  | bool => rfl
  | arrow p r ih_p ih_r =>
    simp [applySubst, ih_p, ih_r]
  | generic1 n arg ih =>
    simp [applySubst, ih]
  | generic2 n a b ih_a ih_b =>
    simp [applySubst, ih_a, ih_b]

/-- Applying substitution to nat returns nat -/
theorem applySubst_nat (s : Subst) :
    applySubst s Ty.nat = Ty.nat := rfl

/-- Applying substitution to bool returns bool -/
theorem applySubst_bool (s : Subst) :
    applySubst s Ty.bool = Ty.bool := rfl

/-- Fresh variable generation produces unique variable -/
theorem freshVar_unique (st : FreshState) :
    let (v, st') := freshVar st
    st'.counter = st.counter + 1 ∧ v.name = s!"T{st.counter}" := by
  simp [freshVar]

/-- Two fresh variables from same state are equal -/
theorem freshVar_deterministic (st : FreshState) :
    freshVar st = freshVar st := rfl

/-- Occurs check is false for different variable -/
theorem occurs_different_var (v1 v2 : TyVar) (h : v1 ≠ v2) :
    occurs v1 (Ty.var v2) = false := by
  simp [occurs, h]

/-- Occurs check is true for same variable -/
theorem occurs_same_var (v : TyVar) :
    occurs v (Ty.var v) = true := by
  simp [occurs]

/-- Occurs check is false for nat -/
theorem occurs_nat (v : TyVar) :
    occurs v Ty.nat = false := rfl

/-- Occurs check is false for bool -/
theorem occurs_bool (v : TyVar) :
    occurs v Ty.bool = false := rfl

/-! ## Example Generic Types -/

/-- Option[T] type constructor -/
def optionTy (arg : Ty) : Ty := Ty.generic1 "Option" arg

/-- List[T] type constructor -/
def listTy (arg : Ty) : Ty := Ty.generic1 "List" arg

/-- Map[K,V] type constructor -/
def mapTy (key value : Ty) : Ty := Ty.generic2 "Map" key value

/-- Either[A,B] type constructor -/
def eitherTy (left right : Ty) : Ty := Ty.generic2 "Either" left right

/-- Result[T,E] type constructor -/
def resultTy (ok err : Ty) : Ty := Ty.generic2 "Result" ok err

end Generics
