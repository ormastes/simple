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

  Generated from: simple/std_lib/src/verification/regenerate/async_effect_inference.spl
-/

namespace AsyncEffectInference

/-- Effect annotation for functions -/
inductive Effect
  | sync   -- Non-suspending, direct return T
  | async  -- May suspend, returns Promise[T]
  deriving DecidableEq, Repr

/-- Suspension operators in the language -/
inductive SuspensionOp
  | suspendAssign      -- ~=
  | suspendIf          -- if~
  | suspendWhile       -- while~
  | suspendFor         -- for~
  | suspendAnd         -- and~
  | suspendOr          -- or~
  deriving DecidableEq, Repr

/-- Expression with effect tracking -/
inductive Expr
  | lit (n : Nat)                           -- Literal (sync)
  | var (name : String)                      -- Variable reference
  | binOp (a b : Expr)                       -- Binary operation
  | call (fn : String) (args : List Expr)    -- Function call
  | suspend (op : SuspensionOp) (e : Expr)   -- Suspension operator
  | lambda (body : Expr)                     -- Lambda expression
  | ifExpr (cond : Expr) (t e : Expr)        -- If expression
  deriving Repr

/-- Function declaration with optional explicit effect annotation -/
structure FnDecl where
  name : String
  body : Expr
  explicitEffect : Option Effect  -- None = infer, Some = explicit
  deriving Repr

/-- Environment mapping function names to their effects -/
def Env := String → Option Effect

/-- Check if expression contains any suspension operator -/
def containsSuspension : Expr → Bool
  | Expr.lit _ => false
  | Expr.var _ => false
  | Expr.binOp a b => containsSuspension a || containsSuspension b
  | Expr.call _ args => args.any containsSuspension
  | Expr.suspend _ _ => true  -- Suspension found!
  | Expr.lambda body => containsSuspension body
  | Expr.ifExpr c t e => containsSuspension c || containsSuspension t || containsSuspension e

/-- Infer effect of expression given environment -/
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
    let fnEffect := match env fn with
      | some eff => eff
      | none => Effect.sync
    let argsAsync := args.any (fun e => inferExprEffect env e == Effect.async)
    if fnEffect == Effect.async || argsAsync then Effect.async else Effect.sync
  | Expr.suspend _ _ => Effect.async  -- Suspension always async
  | Expr.lambda body => inferExprEffect env body
  | Expr.ifExpr c t e =>
    match inferExprEffect env c, inferExprEffect env t, inferExprEffect env e with
    | Effect.async, _, _ => Effect.async
    | _, Effect.async, _ => Effect.async
    | _, _, Effect.async => Effect.async
    | _, _, _ => Effect.sync

/-- Infer effect of function declaration -/
def inferFnEffect (env : Env) (fn : FnDecl) : Effect :=
  match fn.explicitEffect with
  | some eff => eff  -- Explicit annotation takes precedence
  | none => inferExprEffect env fn.body

/-- Validate sync constraint: sync function must not contain suspension -/
def validateSyncConstraint (fn : FnDecl) : Bool :=
  match fn.explicitEffect with
  | some Effect.sync => !containsSuspension fn.body
  | _ => true

/-- Effect is deterministic: inference yields exactly one effect -/
theorem effect_deterministic (env : Env) (e : Expr) :
    ∃! eff : Effect, inferExprEffect env e = eff := by
  exists inferExprEffect env e
  simp only [and_iff_right]
  intros y hy
  exact hy.symm

/-- Suspension implies async: any suspension operator makes expression async -/
theorem suspension_implies_async (env : Env) (op : SuspensionOp) (e : Expr) :
    inferExprEffect env (Expr.suspend op e) = Effect.async := by
  simp [inferExprEffect]

/-- Sync safety: if validateSyncConstraint passes, no suspension in body -/
theorem sync_safety (fn : FnDecl) :
    fn.explicitEffect = some Effect.sync →
    validateSyncConstraint fn = true →
    !containsSuspension fn.body = true := by
  intro h_explicit h_valid
  simp [validateSyncConstraint, h_explicit] at h_valid
  exact h_valid

/-- Effect propagation: calling async function in body makes caller async -/
theorem async_propagation (env : Env) (fn_name : String) (args : List Expr) :
    env fn_name = some Effect.async →
    inferExprEffect env (Expr.call fn_name args) = Effect.async := by
  intro h_async
  simp [inferExprEffect, h_async]

/-- Literals are always sync -/
theorem lit_is_sync (env : Env) (n : Nat) :
    inferExprEffect env (Expr.lit n) = Effect.sync := by
  simp [inferExprEffect]

/-- Build environment from list of function declarations -/
def buildEnv (fns : List FnDecl) : Env :=
  fun name => (fns.find? (fun f => f.name == name)).map (inferFnEffect (fun _ => none))

/-- Fixed-point iteration for mutually recursive functions -/
partial def inferMutualEffects (fns : List FnDecl) (maxIter : Nat := 100) : Env :=
  let rec iterate (env : Env) (n : Nat) : Env :=
    if n == 0 then env
    else
      let newEnv : Env := fun name =>
        match fns.find? (fun f => f.name == name) with
        | some fn => some (inferFnEffect env fn)
        | none => env name
      -- Check for fixed point
      let changed := fns.any (fun fn => newEnv fn.name != env fn.name)
      if changed then iterate newEnv (n - 1) else newEnv
  iterate (fun _ => none) maxIter

/-- Example: sync function -/
def syncExample : FnDecl := {
  name := "double"
  body := Expr.binOp (Expr.var "x") (Expr.lit 2)
  explicitEffect := none
}

/-- Example: async function with suspension -/
def asyncExample : FnDecl := {
  name := "fetchUser"
  body := Expr.suspend SuspensionOp.suspendAssign (Expr.call "http_get" [Expr.var "url"])
  explicitEffect := none
}

/-- Example: explicit sync constraint -/
def explicitSyncExample : FnDecl := {
  name := "compute"
  body := Expr.binOp (Expr.var "x") (Expr.var "x")
  explicitEffect := some Effect.sync
}

#check effect_deterministic
#check suspension_implies_async
#check sync_safety
#check async_propagation

end AsyncEffectInference
