/-
  ============================================================================
  AUTO-GENERATED - DO NOT EDIT MANUALLY
  ============================================================================
  Generated from: simple/std_lib/src/verification/regenerate/async_effect_inference.spl
  To regenerate: ./target/debug/simple simple/std_lib/src/verification/regenerate/__init__.spl
  ============================================================================
-/

/-
  Async/Sync Effect Inference Model for Simple Language

  This module models the automatic inference of async/sync effects
  based on function body analysis. Key properties:

  1. Effect Determinism: Each function has exactly one inferred effect
  2. Effect Propagation: Calling async function makes caller async
  3. Suspension Detection: ~=, if~, while~ operators indicate async
  4. Sync Safety: sync-annotated functions cannot contain suspension
  5. Promise Wrapping: Async functions implicitly return Promise<T>
  6. Await Inference: Promise<T> → T assignment inserts implicit await
  7. No Double-Wrap: Explicit Promise<T> return prevents wrapping

  Generated from: simple/std_lib/src/verification/regenerate/async_effect_inference.spl
-/

namespace AsyncEffectInference
-- Effect annotation for functions
-- Suspension operators in the language
-- Expression with effect tracking
-- Function declaration with optional explicit effect annotation
inductive Effect
  | sync
  | async
deriving DecidableEq, Repr

inductive SuspensionOp
  | suspendAssign
  | suspendIf
  | suspendWhile
  | suspendFor
  | suspendAnd
  | suspendOr
deriving DecidableEq, Repr

inductive Expr
  | lit : Nat → Expr
  | var : String → Expr
  | binOp : Expr → Expr → Expr
  | call : String → List Expr → Expr
  | suspend : SuspensionOp → Expr → Expr
  | lambda : Expr → Expr
  | ifExpr : Expr → Expr → Expr → Expr
deriving Repr

structure FnDecl where
  name : text
  body : Expr
  explicitEffect : Option Effect  -- None = infer, Some = explicit
  deriving Repr

-- Environment mapping function names to their effects
def Env := text → Option Effect

-- Check if expression contains any suspension operator
def containsSuspension : Expr → bool
  | Expr.lit _ => false
  | Expr.var _ => false
  | Expr.binOp a b => containsSuspension a || containsSuspension b
  | Expr.call _ args => args.any containsSuspension
  | Expr.suspend _ _ => true  -- Suspension found!
  | Expr.lambda body => containsSuspension body
  | Expr.ifExpr c t e => containsSuspension c || containsSuspension t || containsSuspension e

-- Infer effect of expression given environment
partial def inferExprEffect (env : Env) : Expr → Effect
  | Expr.lit _ => Effect.sync
  | Expr.var _ => Effect.sync
  | Expr.binOp a b =>
    match inferExprEffect env a, inferExprEffect env b with
    | Effect.async, _ => Effect.async
    | _, Effect.async => Effect.async
    | _, _ => Effect.sync
  | Expr.call fn args =>
    -- Check if called function is async
    val fnEffect := match env fn with
      | some eff => eff
      | none => Effect.sync
    val argsAsync := args.any (fun e => inferExprEffect env e == Effect.async)
    if fnEffect == Effect.async || argsAsync then Effect.async else Effect.sync
  | Expr.suspend _ _ => Effect.async  -- Suspension always async
  | Expr.lambda body => inferExprEffect env body
  | Expr.ifExpr c t e =>
    match inferExprEffect env c, inferExprEffect env t, inferExprEffect env e with
    | Effect.async, _, _ => Effect.async
    | _, Effect.async, _ => Effect.async
    | _, _, Effect.async => Effect.async
    | _, _, _ => Effect.sync

-- Infer effect of function declaration
def inferFnEffect (env : Env) (fn : FnDecl) : Effect :=
  match fn.explicitEffect with
  | some eff => eff  -- Explicit annotation takes precedence
  | none => inferExprEffect env fn.body

-- Validate sync constraint: sync function must not contain suspension
def validateSyncConstraint (fn : FnDecl) : bool :=
  match fn.explicitEffect with
  | some Effect.sync => !containsSuspension fn.body
  | _ => true

-- Effect is deterministic: inference yields exactly one effect
-- Suspension implies async: any suspension operator makes expression async
-- Sync safety: if validateSyncConstraint passes, no suspension in body
-- Effect propagation: calling async function in body makes caller async
-- Literals are always sync
-- Type representation in the type system
inductive Type
  | i32
  | string
  | bool
  | promise (inner : Type)
  | fn (param : Type) (ret : Type)
  | generic (name : text)
  deriving DecidableEq, Repr

-- Transform return type based on effect: async wraps in Promise<T>
def transformReturnType (eff : Effect) (retType : Type) : Type :=
  match eff, retType with
  | Effect.async, Type.promise _ => retType  -- Already Promise, no double-wrap
  | Effect.async, t => Type.promise t  -- Wrap in Promise
  | Effect.sync, t => t  -- No wrapping for sync

-- Check if implicit await should be inserted based on type mismatch
def shouldInsertAwait (expectedType : Type) (actualType : Type) : bool :=
  match expectedType, actualType with
  | t, Type.promise inner => t == inner  -- Promise<T> → T needs await
  | _, _ => false

-- Check if Promise<T> can be unwrapped to T
def canUnwrapPromise (promiseType : Type) (targetType : Type) : bool :=
  match promiseType with
  | Type.promise inner => inner == targetType
  | _ => false

-- Async functions implicitly wrap return type in Promise
-- Sync functions return types unchanged
-- Promise<T> is not wrapped again to Promise<Promise<T>>
-- Await inference is sound: only inserts when types match
-- Promise can be unwrapped to its inner type
-- Build environment from list of function declarations
def buildEnv (fns : List FnDecl) : Env :=
  fun name => (fns.find? (fun f => f.name == name)).map (inferFnEffect (fun _ => none))

-- Fixed-point iteration for mutually recursive functions
partial def inferMutualEffects (fns : List FnDecl) (maxIter : Nat := 100) : Env :=
  val rec iterate (env : Env) (n : Nat) : Env :=
    if n == 0 then env
    else
      val newEnv : Env := fun name =>
        match fns.find? (fun f => f.name == name) with
        | some fn => some (inferFnEffect env fn)
        | none => env name
      -- Check for fixed point
      val changed := fns.any (fun fn => newEnv fn.name != env fn.name)
      if changed then iterate newEnv (n - 1) else newEnv
  iterate (fun _ => none) maxIter

-- Example: sync function
def syncExample : FnDecl := \{
  name := "double"
  body := Expr.binOp (Expr.var "x") (Expr.lit 2)
  explicitEffect := none
\}

-- Example: async function with suspension
def asyncExample : FnDecl := \{
  name := "fetchUser"
  body := Expr.suspend SuspensionOp.suspendAssign (Expr.call "http_get" <Expr.var "url">)
  explicitEffect := none
\}

-- Example: explicit sync constraint
def explicitSyncExample : FnDecl := \{
  name := "compute"
  body := Expr.binOp (Expr.var "x") (Expr.var "x")
  explicitEffect := some Effect.sync
\}

-- Example: type-driven await inference
example : shouldInsertAwait Type.i32 (Type.promise Type.i32) = true := by
  simp [shouldInsertAwait]

-- Example: Promise wrapping for async function
example : transformReturnType Effect.async Type.i32 = Type.promise Type.i32 := by
  simp [transformReturnType]

-- Example: No double-wrap for explicit Promise return
example : transformReturnType Effect.async (Type.promise Type.string) = Type.promise Type.string := by
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
  exists inferExprEffect env e
  simp only [and_iff_right]
  intros y hy
  exact hy.symm

theorem suspension_implies_async (env : Env) (op : SuspensionOp) (e : Expr) :
  inferExprEffect env (Expr.suspend op e) = Effect.async := by
  simp [inferExprEffect]

theorem sync_safety (fn : FnDecl) :
  fn.explicitEffect = some Effect.sync → validateSyncConstraint fn = true → !containsSuspension fn.body = true := by
  intro h_explicit h_valid
  simp [validateSyncConstraint, h_explicit] at h_valid
  exact h_valid

theorem async_propagation (env : Env) (fn_name : text) (args : List Expr) :
  env fn_name = some Effect.async → inferExprEffect env (Expr.call fn_name args) = Effect.async := by
  intro h_async
  simp [inferExprEffect, h_async]

theorem lit_is_sync (env : Env) (n : Nat) :
  inferExprEffect env (Expr.lit n) = Effect.sync := by
  simp [inferExprEffect]

theorem async_returns_promise (retType : Type) :
  transformReturnType Effect.async retType = Type.promise retType ∨ (∃ t, retType = Type.promise t ∧ transformReturnType Effect.async retType = retType) := by
  cases retType with
  | promise _ => right; exists _; simp [transformReturnType]
  | _ => left; simp [transformReturnType]

theorem sync_no_promise_wrap (retType : Type) :
  transformReturnType Effect.sync retType = retType := by
  cases retType <;> simp [transformReturnType]

theorem no_double_wrap (t : Type) :
  transformReturnType Effect.async (Type.promise t) = Type.promise t := by
  simp [transformReturnType]

theorem await_inference_sound (t : Type) (inner : Type) :
  shouldInsertAwait t (Type.promise inner) = true → t = inner := by
  intro h
  simp [shouldInsertAwait] at h
  exact h

theorem promise_unwrap_correct (inner : Type) (target : Type) :
  canUnwrapPromise (Type.promise inner) target = true → inner = target := by
  intro h
  simp [canUnwrapPromise] at h
  exact h

end AsyncEffectInference
