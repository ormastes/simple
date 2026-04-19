/-
  ============================================================================
  AUTO-GENERATED - DO NOT EDIT MANUALLY
  ============================================================================
  Generated from: simple/std_lib/src/verification/regenerate/async_effect_inference.spl
  ============================================================================
-/

/-
  Async/Sync effect inference model for Simple.
  This file intentionally keeps the model small and structural.
-/

namespace AsyncEffectInference
-- Effect annotation for functions
-- Suspension operators in the language
-- Expression with effect tracking
inductive Effect
  | sync
  | async
deriving DecidableEq, Repr, BEq

inductive SuspensionOp
  | suspendAssign
  | suspendIf
  | suspendWhile
  | suspendFor
  | suspendAnd
  | suspendOr
deriving DecidableEq, Repr, BEq

inductive Expr
  | lit : Nat → Expr
  | var : String → Expr
  | binOp : Expr → Expr → Expr
  | call : String → List Expr → Expr
  | suspend : SuspensionOp → Expr → Expr
  | lambda : Expr → Expr
  | ifExpr : Expr → Expr → Expr → Expr
deriving Repr, DecidableEq

structure FnDecl where
  name : String
  body : Expr
  explicitEffect : Option Effect
  deriving Repr, DecidableEq

def Env := String → Option Effect

-- Check if expression contains any suspension operator
def containsSuspension : Expr → Bool
  | Expr.lit _ => false
  | Expr.var _ => false
  | Expr.binOp a b => containsSuspension a || containsSuspension b
  | Expr.call _ args => args.any containsSuspension
  | Expr.suspend _ _ => true
  | Expr.lambda body => containsSuspension body
  | Expr.ifExpr c t e => containsSuspension c || containsSuspension t || containsSuspension e

-- Infer effect of expression given environment
def inferExprEffect (env : Env) : Expr → Effect
  | Expr.lit _ => Effect.sync
  | Expr.var _ => Effect.sync
  | Expr.binOp a b =>
      if inferExprEffect env a == Effect.async || inferExprEffect env b == Effect.async then Effect.async else Effect.sync
  | Expr.call fn args =>
      let fnEffect := match env fn with
        | some eff => eff
        | none => Effect.sync
      let argsAsync := args.any (fun e => inferExprEffect env e == Effect.async)
      if fnEffect == Effect.async || argsAsync then Effect.async else Effect.sync
  | Expr.suspend _ _ => Effect.async
  | Expr.lambda body => inferExprEffect env body
  | Expr.ifExpr c t e =>
      if inferExprEffect env c == Effect.async || inferExprEffect env t == Effect.async || inferExprEffect env e == Effect.async then Effect.async else Effect.sync

-- Infer effect of function declaration
def inferFnEffect (env : Env) (fn : FnDecl) : Effect :=
  match fn.explicitEffect with
  | some eff => eff
  | none => inferExprEffect env fn.body

-- Validate sync constraint: sync function must not contain suspension
def validateSyncConstraint (fn : FnDecl) : Bool :=
  match fn.explicitEffect with
  | some Effect.sync => !(containsSuspension fn.body)
  | _ => true

inductive Ty
  | i32
  | string
  | bool
  | promise (inner : Ty)
  | fn (param : Ty) (ret : Ty)
  | generic (name : String)
  deriving DecidableEq, Repr, BEq

def transformReturnType (eff : Effect) (retType : Ty) : Ty :=
  match eff, retType with
  | Effect.async, Ty.promise _ => retType
  | Effect.async, t => Ty.promise t
  | Effect.sync, t => t

def shouldInsertAwait (expectedType : Ty) (actualType : Ty) : Bool :=
  match expectedType, actualType with
  | t, Ty.promise inner => t == inner
  | _, _ => false

def canUnwrapPromise (promiseType : Ty) (targetType : Ty) : Bool :=
  match promiseType with
  | Ty.promise inner => inner == targetType
  | _ => false

def buildEnv (fns : List FnDecl) : Env :=
  fun name => (fns.find? (fun f => f.name == name)).map (inferFnEffect (fun _ => none))

def inferMutualEffects (fns : List FnDecl) : Env :=
  buildEnv fns

def syncExample : FnDecl := {
  name := "double"
  body := Expr.binOp (Expr.var "x") (Expr.lit 2)
  explicitEffect := none
}

def asyncExample : FnDecl := {
  name := "fetchUser"
  body := Expr.suspend SuspensionOp.suspendAssign (Expr.call "http_get" [Expr.var "url"])
  explicitEffect := none
}

def explicitSyncExample : FnDecl := {
  name := "compute"
  body := Expr.binOp (Expr.var "x") (Expr.var "x")
  explicitEffect := some Effect.sync
}

example : shouldInsertAwait Ty.i32 (Ty.promise Ty.i32) = true := by
  simp [shouldInsertAwait]

example : transformReturnType Effect.async Ty.i32 = Ty.promise Ty.i32 := by
  simp [transformReturnType]

example : transformReturnType Effect.async (Ty.promise Ty.string) = Ty.promise Ty.string := by
  simp [transformReturnType]

#check effect_deterministic
#check suspension_implies_async
#check sync_safety
#check async_propagation
#check lit_is_sync
#check async_returns_promise
#check sync_no_promise_wrap
#check no_double_wrap
#check await_inference_sound
#check promise_unwrap_correct

theorem effect_deterministic (env : Env) (e : Expr) :
  ∃! eff : Effect, inferExprEffect env e = eff := by
  refine ⟨inferExprEffect env e, rfl, ?_⟩
  intro y hy
  simpa [hy]

theorem suspension_implies_async (env : Env) (op : SuspensionOp) (e : Expr) :
  inferExprEffect env (Expr.suspend op e) = Effect.async := by
  simp [inferExprEffect]

theorem sync_safety (fn : FnDecl) :
  fn.explicitEffect = some Effect.sync → validateSyncConstraint fn = true → containsSuspension fn.body = false := by
  intro h_explicit h_valid
  simp [validateSyncConstraint, h_explicit] at h_valid
  exact h_valid

theorem async_propagation (env : Env) (fn_name : String) (args : List Expr) :
  env fn_name = some Effect.async → inferExprEffect env (Expr.call fn_name args) = Effect.async := by
  intro h_async
  simp [inferExprEffect, h_async]

theorem lit_is_sync (env : Env) (n : Nat) :
  inferExprEffect env (Expr.lit n) = Effect.sync := by
  simp [inferExprEffect]

theorem async_returns_promise (retType : Ty) :
  transformReturnType Effect.async retType = Ty.promise retType ∨ (∃ t, retType = Ty.promise t ∧ transformReturnType Effect.async retType = retType) := by
  cases retType with
  | promise inner => right; exact ⟨inner, rfl, by simp [transformReturnType]⟩
  | _ => left; simp [transformReturnType]

theorem sync_no_promise_wrap (retType : Ty) :
  transformReturnType Effect.sync retType = retType := by
  cases retType <;> simp [transformReturnType]

theorem no_double_wrap (t : Ty) :
  transformReturnType Effect.async (Ty.promise t) = Ty.promise t := by
  simp [transformReturnType]

theorem await_inference_sound (t : Ty) (inner : Ty) :
  shouldInsertAwait t (Ty.promise inner) = true → t = inner := by
  intro h
  simp [shouldInsertAwait] at h
  exact h

theorem promise_unwrap_correct (inner : Ty) (target : Ty) :
  canUnwrapPromise (Ty.promise inner) target = true → inner = target := by
  intro h
  simp [canUnwrapPromise] at h
  exact h

end AsyncEffectInference
