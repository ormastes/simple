/-
  Generics.lean - Reduced formal model for generic type inference
  
  This generator emits a small valid Lean model for polymorphic types,
  substitution, simple schemes, and environment operations.
-/
namespace Generics
inductive Ty
  | var : Nat → Ty
  | nat
  | bool
  | str
  | arrow : Ty → Ty → Ty
  | generic0 : String → Ty
  | generic1 : String → Ty → Ty
  | generic2 : String → Ty → Ty → Ty
deriving Repr, DecidableEq, BEq, Inhabited

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

abbrev TyVar := Nat

structure Scheme where
  vars : List TyVar
  ty : Ty
  deriving Repr, Inhabited

structure SubstEntry where
  var : TyVar
  ty : Ty
  deriving Repr, Inhabited

abbrev Subst := List SubstEntry
def emptySubst : Subst := []

structure FreshState where
  next : Nat
  deriving Repr, Inhabited

structure EnvEntry where
  name : String
  scheme : Scheme
  deriving Repr, Inhabited

abbrev TypeEnv := List EnvEntry

def substLookup (s : Subst) (v : TyVar) : Option Ty :=
  match s.find? (fun e => e.var == v) with
  | some e => some e.ty
  | none => none

def singleSubst (v : TyVar) (t : Ty) : Subst := [{ var := v, ty := t }]

def applySubst (s : Subst) : Ty → Ty
  | Ty.var v => match substLookup s v with | some t => t | none => Ty.var v
  | Ty.nat => Ty.nat
  | Ty.bool => Ty.bool
  | Ty.str => Ty.str
  | Ty.arrow a b => Ty.arrow (applySubst s a) (applySubst s b)
  | Ty.generic0 n => Ty.generic0 n
  | Ty.generic1 n a => Ty.generic1 n (applySubst s a)
  | Ty.generic2 n a b => Ty.generic2 n (applySubst s a) (applySubst s b)

def composeSubst (s1 s2 : Subst) : Subst :=
  s1 ++ s2.map (fun e => { e with ty := applySubst s1 e.ty })

def freeVars : Ty → List TyVar
  | Ty.var v => [v]
  | Ty.nat => []
  | Ty.bool => []
  | Ty.str => []
  | Ty.arrow a b => freeVars a ++ freeVars b
  | Ty.generic0 _ => []
  | Ty.generic1 _ a => freeVars a
  | Ty.generic2 _ a b => freeVars a ++ freeVars b

def freeVarsScheme (sch : Scheme) : List TyVar :=
  (freeVars sch.ty).filter (fun v => !(sch.vars.contains v))

def occurs (v : TyVar) : Ty → Bool
  | Ty.var v' => decide (v = v')
  | Ty.nat => false
  | Ty.bool => false
  | Ty.str => false
  | Ty.arrow a b => occurs v a || occurs v b
  | Ty.generic0 _ => false
  | Ty.generic1 _ a => occurs v a
  | Ty.generic2 _ a b => occurs v a || occurs v b

inductive UnifyResult
  | ok : Subst → UnifyResult
  | occursCheckFail : TyVar → Ty → UnifyResult
  | mismatch : Ty → Ty → UnifyResult
deriving Repr, Inhabited

inductive InferResult
  | ok : Ty → Subst → FreshState → InferResult
  | error : String → InferResult
deriving Repr, Inhabited

def unify (t1 t2 : Ty) : UnifyResult :=
  if t1 == t2 then UnifyResult.ok emptySubst
  else match t1, t2 with
    | Ty.var v, t => if occurs v t then UnifyResult.occursCheckFail v t else UnifyResult.ok (singleSubst v t)
    | t, Ty.var v => if occurs v t then UnifyResult.occursCheckFail v t else UnifyResult.ok (singleSubst v t)
    | _, _ => UnifyResult.mismatch t1 t2

def freshVar (st : FreshState) : (TyVar × FreshState) :=
  (st.next, { next := st.next + 1 })

def instantiate (sch : Scheme) (st : FreshState) : (Ty × FreshState) :=
  (sch.ty, st)

def generalize (envFreeVars : List TyVar) (t : Ty) : Scheme :=
  { vars := (freeVars t).filter (fun v => !(envFreeVars.contains v)), ty := t }

def lookupEnv (env : TypeEnv) (name : String) : Option Scheme :=
  match env.find? (fun e => e.name == name) with
  | some e => some e.scheme
  | none => none

def extendEnv (env : TypeEnv) (name : String) (sch : Scheme) : TypeEnv :=
  { name := name, scheme := sch } :: env

def freeVarsEnv (env : TypeEnv) : List TyVar :=
  env.foldl (fun acc e => acc ++ freeVarsScheme e.scheme) []

def applySubstEnv (s : Subst) (env : TypeEnv) : TypeEnv :=
  env.map (fun e => { e with scheme := { e.scheme with ty := applySubst s e.scheme.ty } })

def infer (env : TypeEnv) (expr : Expr) (st : FreshState) : InferResult :=
  match expr with
  | Expr.var name =>
      match lookupEnv env name with
      | some sch => let (ty, st') := instantiate sch st; InferResult.ok ty emptySubst st'
      | none => InferResult.error "Undefined variable"
  | Expr.litNat _ => InferResult.ok Ty.nat emptySubst st
  | Expr.litBool _ => InferResult.ok Ty.bool emptySubst st
  | Expr.litStr _ => InferResult.ok Ty.str emptySubst st
  | Expr.lam _ _ => let (v, st') := freshVar st; InferResult.ok (Ty.arrow (Ty.var v) (Ty.var v)) emptySubst st'
  | Expr.app _ _ => let (v, st') := freshVar st; InferResult.ok (Ty.var v) emptySubst st'
  | Expr.letIn name _ body => infer (extendEnv env name (generalize (freeVarsEnv env) Ty.nat)) body st
  | Expr.ifElse _ t _ => infer env t st
  | Expr.mkGeneric1 name _ => InferResult.ok (Ty.generic1 name Ty.nat) emptySubst st
  | Expr.mkGeneric2 name _ _ => InferResult.ok (Ty.generic2 name Ty.nat Ty.nat) emptySubst st

theorem applySubst_empty (t : Ty) :
  applySubst emptySubst t = t := by
  induction t with
  | var v => simp [applySubst, emptySubst, substLookup]
  | nat => rfl
  | bool => rfl
  | str => rfl
  | arrow a b iha ihb => simp [applySubst, iha, ihb]
  | generic0 n => rfl
  | generic1 n a iha => simp [applySubst, iha]
  | generic2 n a b iha ihb => simp [applySubst, iha, ihb]

theorem occurs_nat_false (v : TyVar) :
  occurs v Ty.nat = false := by
  rfl

theorem occurs_bool_false (v : TyVar) :
  occurs v Ty.bool = false := by
  rfl

theorem occurs_str_false (v : TyVar) :
  occurs v Ty.str = false := by
  rfl

theorem occurs_var_true (v : TyVar) :
  occurs v (Ty.var v) = true := by
  simp [occurs]

theorem instantiate_preserves_shape (sch : Scheme) (st : FreshState) :
  (instantiate sch st).fst = sch.ty := by
  rfl

theorem generalize_preserves_type (envFreeVars : List TyVar) (t : Ty) :
  (generalize envFreeVars t).ty = t := by
  rfl

theorem infer_lit_nat (env : TypeEnv) (st : FreshState) (n : Nat) :
  infer env (Expr.litNat n) st = InferResult.ok Ty.nat emptySubst st := by
  rfl

theorem infer_lit_bool (env : TypeEnv) (st : FreshState) (b : Bool) :
  infer env (Expr.litBool b) st = InferResult.ok Ty.bool emptySubst st := by
  rfl

theorem infer_lit_str (env : TypeEnv) (st : FreshState) (s : String) :
  infer env (Expr.litStr s) st = InferResult.ok Ty.str emptySubst st := by
  rfl

end Generics
