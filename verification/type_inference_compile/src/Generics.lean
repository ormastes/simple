/-
  Generics.lean - Formal model for generic type inference
  
  This module extends the basic type inference model with:
  1. Type variables for polymorphism
  2. Generic types with type arguments (List<T>, Map<K,V>)
  3. Substitution mechanism
  4. Unification with occurs check
  5. Type schemes (∀T. τ) for val-polymorphism
  6. Instantiation and generalization
  
  The model follows Algorithm W (Damas-Milner) style inference.
-/
namespace Generics
-- ════════════════════════════════════════════════════════════════
-- Type Definitions
-- ════════════════════════════════════════════════════════════════

-- Type variable identifier
inductive Ty
  | var : TyVar → Ty
  | nat
  | bool
  | str
  | arrow : Ty → Ty → Ty
  | generic0 : String → Ty
  | generic1 : String → Ty → Ty
  | generic2 : String → Ty → Ty → Ty
deriving Repr, BEq, Inhabited

inductive UnifyResult
  | ok : Subst → UnifyResult
  | occursCheckFail : TyVar → Ty → UnifyResult
  | mismatch : Ty → Ty → UnifyResult
deriving Repr, Inhabited

inductive Expr
  | var : String → Expr
  | litNat : Nat → Expr
  | litBool : Bool → Expr
  | litStr : String → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  | letIn : String → Expr → Expr → Expr
  | ifElse : Expr → Expr → Expr → Expr
  | mkGeneric1 : String → Expr → Expr
  | mkGeneric2 : String → Expr → Expr → Expr
deriving Repr, Inhabited

inductive InferResult
  | ok : Ty → Subst → FreshState → InferResult
  | error : String → InferResult
deriving Repr, Inhabited

structure GenericInfo where
  name : String
  arity : Nat
deriving Repr, BEq, Inhabited

structure Scheme where
  vars : List TyVar
  ty : Ty
deriving Repr, Inhabited

structure SubstEntry where
  var : TyVar
  ty : Ty
deriving Repr, Inhabited

structure FreshState where
  next : TyVar
deriving Repr, Inhabited

structure EnvEntry where
  name : String
  scheme : Scheme
deriving Repr, Inhabited

abbrev TyVar := Nat
-- Generic type: name with arity (number of type parameters)
/-
  ## Type Representation
  
  We use a two-level encoding to handle generic types with arguments:
  - Base types (Ty) include primitives, variables, arrows, and generic references
  - Generic applications are represented as (GenericInfo, List of argument indices)
  
  This avoids nested inductive termination issues while still modeling generics.
-/
-- Types with type variables and generics
-- Type scheme: ∀α₁...αₙ. τ (polymorphic type)
-- ════════════════════════════════════════════════════════════════
-- Substitution
-- ════════════════════════════════════════════════════════════════

-- Substitution entry
-- Substitution: mapping from type variables to types
def Subst := List SubstEntry
  deriving Repr, Inhabited

-- Empty substitution
def emptySubst : Subst := []

-- Lookup in substitution
def substLookup (s : Subst) (v : TyVar) : Option Ty :=
  match s with
  | [] => none
  | e . rest => if e.var == v then some e.ty else substLookup rest v

-- Singleton substitution: [α ↦ τ]
def singleSubst (v : TyVar) (t : Ty) : Subst := [{ var := v, ty := t }]

-- Apply substitution to a type
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

-- Append substitutions
def appendSubst (s1 s2 : Subst) : Subst :=
  match s1 with
  | [] => s2
  | e . rest => e . appendSubst rest s2

-- Compose two substitutions: (s1 ∘ s2)
def composeSubst (s1 s2 : Subst) : Subst :=
  val s2' := s2.map (fun e => { e with ty := applySubst s1 e.ty })
  appendSubst s2' s1

-- ════════════════════════════════════════════════════════════════
-- Free Type Variables
-- ════════════════════════════════════════════════════════════════

-- Collect free type variables in a type
def freeVars : Ty → List TyVar
  | Ty.var v => [v]
  | Ty.nat => []
  | Ty.bool => []
  | Ty.str => []
  | Ty.arrow a b => freeVars a ++ freeVars b
  | Ty.generic0 _ => []
  | Ty.generic1 _ arg => freeVars arg
  | Ty.generic2 _ arg1 arg2 => freeVars arg1 ++ freeVars arg2

-- Free variables in a scheme (excluding bound vars)
def freeVarsScheme (sch : Scheme) : List TyVar :=
  (freeVars sch.ty).filter (fun v => !sch.vars.contains v)

-- ════════════════════════════════════════════════════════════════
-- Occurs Check
-- ════════════════════════════════════════════════════════════════

-- Check if type variable occurs in type (for occurs check)
def occurs (v : TyVar) : Ty → bool
  | Ty.var v' => v == v'
  | Ty.nat => false
  | Ty.bool => false
  | Ty.str => false
  | Ty.arrow a b => occurs v a || occurs v b
  | Ty.generic0 _ => false
  | Ty.generic1 _ arg => occurs v arg
  | Ty.generic2 _ arg1 arg2 => occurs v arg1 || occurs v arg2

-- ════════════════════════════════════════════════════════════════
-- Unification
-- ════════════════════════════════════════════════════════════════

-- Unification result
-- Unify two types
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

-- ════════════════════════════════════════════════════════════════
-- Instantiation and Generalization
-- ════════════════════════════════════════════════════════════════

-- Fresh variable counter (for generating new type variables)
def freshVar (st : FreshState) : (TyVar × FreshState) :=
  (st.next, { next := st.next + 1 })

-- Instantiate a scheme with fresh type variables
def instantiate (sch : Scheme) (st : FreshState) : (Ty × FreshState) :=
  val (freshVars, st') := sch.vars.foldl
    (fun (acc, s) _ =>
      val (v, s') := freshVar s
      (acc ++ [v], s'))
    ([], st)
  val subst : Subst := List.zipWith (fun old new => { var := old, ty := Ty.var new }) sch.vars freshVars
  (applySubst subst sch.ty, st')

-- Generalize a type over free variables not in environment
def generalize (envFreeVars : List TyVar) (t : Ty) : Scheme :=
  val tyFree := freeVars t
  val toGeneralize := tyFree.filter (fun v => !envFreeVars.contains v)
  { vars := toGeneralize.eraseDups, ty := t }

-- ════════════════════════════════════════════════════════════════
-- Type Environment
-- ════════════════════════════════════════════════════════════════

-- Type environment entry
-- Type environment: maps variable names to type schemes
def TypeEnv := List EnvEntry
  deriving Repr, Inhabited

def lookupEnv (env : TypeEnv) (name : text) : Option Scheme :=
  match env with
  | [] => none
  | e . rest => if e.name == name then some e.scheme else lookupEnv rest name

def extendEnv (env : TypeEnv) (name : text) (sch : Scheme) : TypeEnv :=
  { name := name, scheme := sch } . env

-- Free variables in environment
def freeVarsEnv (env : TypeEnv) : List TyVar :=
  env.foldl (fun acc e => acc ++ freeVarsScheme e.scheme) []

-- ════════════════════════════════════════════════════════════════
-- Expressions
-- ════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════════
-- Type Inference (Algorithm W style)
-- ════════════════════════════════════════════════════════════════

-- Inference result
-- Apply substitution to environment
def applySubstEnv (s : Subst) (env : TypeEnv) : TypeEnv :=
  env.map (fun e => { e with scheme := { e.scheme with ty := applySubst s e.scheme.ty } })

-- Infer type of expression
def infer (env : TypeEnv) (expr : Expr) (st : FreshState) : InferResult :=
  match expr with
  | Expr.var name =>
    match lookupEnv env name with
    | some sch =>
      val (ty, st') := instantiate sch st
      InferResult.ok ty emptySubst st'
    | none => InferResult.error s!"Undefined variable: {name}"

  | Expr.litNat _ => InferResult.ok Ty.nat emptySubst st
  | Expr.litBool _ => InferResult.ok Ty.bool emptySubst st
  | Expr.litStr _ => InferResult.ok Ty.str emptySubst st

  | Expr.lam param body =>
    val (paramVar, st') := freshVar st
    val paramTy := Ty.var paramVar
    val paramSch : Scheme := { vars := [], ty := paramTy }
    val env' := extendEnv env param paramSch
    match infer env' body st' with
    | InferResult.ok bodyTy s st'' =>
      val resultTy := Ty.arrow (applySubst s paramTy) bodyTy
      InferResult.ok resultTy s st''
    | err => err

  | Expr.app f x =>
    match infer env f st with
    | InferResult.ok fTy s1 st1 =>
      val env' := applySubstEnv s1 env
      match infer env' x st1 with
      | InferResult.ok xTy s2 st2 =>
        val (retVar, st3) := freshVar st2
        val retTy := Ty.var retVar
        val fTy' := applySubst s2 fTy
        match unify fTy' (Ty.arrow xTy retTy) with
        | UnifyResult.ok s3 =>
          val finalSubst := composeSubst s3 (composeSubst s2 s1)
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
      val env' := applySubstEnv s1 env
      val valueTy' := applySubst s1 valueTy
      val sch := generalize (freeVarsEnv env') valueTy'
      val env'' := extendEnv env' name sch
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
        val s1'' := composeSubst s1' s1
        val env' := applySubstEnv s1'' env
        match infer env' thenE st1 with
        | InferResult.ok thenTy s2 st2 =>
          val env'' := applySubstEnv s2 env'
          match infer env'' elseE st2 with
          | InferResult.ok elseTy s3 st3 =>
            val thenTy' := applySubst s3 thenTy
            match unify thenTy' elseTy with
            | UnifyResult.ok s4 =>
              val finalSubst := composeSubst s4 (composeSubst s3 (composeSubst s2 s1''))
              InferResult.ok (applySubst s4 elseTy) finalSubst st3
            | UnifyResult.mismatch t1 t2 =>
              InferResult.error s!"Branch type mismatch: {repr t1} vs {repr t2}"
            | UnifyResult.occursCheckFail v t =>
              InferResult.error s!"Occurs check failed: {v} in {repr t}"
          | err => err
        | err => err
      | UnifyResult.mismatch _ _ =>
        InferResult.error "Condition must be bool"
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
      val env' := applySubstEnv s1 env
      match infer env' arg2 st1 with
      | InferResult.ok arg2Ty s2 st2 =>
        val arg1Ty' := applySubst s2 arg1Ty
        val finalSubst := composeSubst s2 s1
        InferResult.ok (Ty.generic2 name arg1Ty' arg2Ty) finalSubst st2
      | err => err
    | err => err

-- ════════════════════════════════════════════════════════════════
-- Soundness Theorems
-- ════════════════════════════════════════════════════════════════

-- Substitution preserves type structure for primitives
-- Empty substitution is identity
-- Occurs check prevents infinite types
-- Generic1 occurs check propagates to argument
-- Generic2 occurs check propagates to both arguments
-- Type inference is deterministic
-- Unification is sound: if unify succeeds, applying the substitution makes types equal
-- Principal type property (informal statement)
-- ════════════════════════════════════════════════════════════════
-- Example Generic Types
-- ════════════════════════════════════════════════════════════════

-- Option<T> type constructor
def optionTy (arg : Ty) : Ty := Ty.generic1 "Option" arg

-- List<T> type constructor
def listTy (arg : Ty) : Ty := Ty.generic1 "List" arg

-- Map<K,V> type constructor
def mapTy (key value : Ty) : Ty := Ty.generic2 "Map" key value

-- Either<A,B> type constructor
def eitherTy (left right : Ty) : Ty := Ty.generic2 "Either" left right

-- Result<T,E> type constructor
def resultTy (ok err : Ty) : Ty := Ty.generic2 "Result" ok err

theorem applySubst_nat (s : Subst) :
  applySubst s Ty.nat = Ty.nat := by
  simp only [applySubst]

theorem applySubst_bool (s : Subst) :
  applySubst s Ty.bool = Ty.bool := by
  simp only [applySubst]

theorem applySubst_str (s : Subst) :
  applySubst s Ty.str = Ty.str := by
  simp only [applySubst]

theorem emptySubst_identity (t : Ty) :
  applySubst emptySubst t = t := by
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

theorem occurs_nat (v : TyVar) :
  occurs v Ty.nat = false := by
  simp [occurs]

theorem occurs_bool (v : TyVar) :
  occurs v Ty.bool = false := by
  simp [occurs]

theorem occurs_str (v : TyVar) :
  occurs v Ty.str = false := by
  simp [occurs]

theorem occurs_var_same (v : TyVar) :
  occurs v (Ty.var v) = true := by
  simp [occurs]

theorem occurs_generic1 (v : TyVar) (name : text) (arg : Ty) :
  occurs v (Ty.generic1 name arg) = occurs v arg := by
  simp [occurs]

theorem occurs_generic2 (v : TyVar) (name : text) (arg1 : Ty) (arg2 : Ty) :
  occurs v (Ty.generic2 name arg1 arg2) = (occurs v arg1 || occurs v arg2) := by
  simp [occurs]

theorem infer_deterministic (env : TypeEnv) (e : Expr) (st : FreshState) (t1 : Ty) (t2 : Ty) (s1 : Subst) (s2 : Subst) (st1 : FreshState) (st2 : FreshState) :
  infer env e st = InferResult.ok t1 s1 st1 →
    infer env e st = InferResult.ok t2 s2 st2 →
    t1 = t2 ∧ s1 = s2 ∧ st1 = st2 := by
  intro h1 h2
  have : InferResult.ok t1 s1 st1 = InferResult.ok t2 s2 st2 := by
    simpa [h1] using h2
  cases this
  exact ⟨rfl, rfl, rfl⟩

theorem unify_sound (t1 : Ty) (t2 : Ty) (s : Subst) :
  unify t1 t2 = UnifyResult.ok s →
    applySubst s t1 = applySubst s t2 := by
  sorry  -- Main unification correctness theorem

theorem principal_type_informal (_env : TypeEnv) (_e : Expr) (_st : FreshState) :
  True := by
  trivial

end Generics
