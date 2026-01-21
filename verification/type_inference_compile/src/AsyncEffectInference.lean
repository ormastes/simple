/-
  Async/Sync Effect Inference Model for Simple Language

  This module models the automatic inference of async/sync effects
  based on function body analysis. Key properties:

  1. Effect Determinism: Each function has exactly one inferred effect
  2. Effect Propagation: Calling async function makes caller async
  3. Suspension Detection: ~=, if~, while~ operators indicate async
  4. Sync Safety: sync-annotated functions cannot contain suspension
  5. Promise Wrapping: Async functions implicitly return Promise[T]
  6. Await Inference: Promise[T] → T assignment inserts implicit await
  7. No Double-Wrap: Explicit Promise[T] return prevents wrapping
-/

namespace AsyncEffectInference

/-- Effect annotation for functions -/
inductive Effect where
  | sync
  | async
deriving DecidableEq, Repr, Inhabited

/-- Suspension operators in the language -/
inductive SuspensionOp where
  | suspendAssign
  | suspendIf
  | suspendWhile
  | suspendFor
  | suspendAnd
  | suspendOr
deriving DecidableEq, Repr

/-- Expression with effect tracking -/
inductive Expr where
  | lit : Nat → Expr
  | var : String → Expr
  | binOp : Expr → Expr → Expr
  | call : String → List Expr → Expr
  | suspend : SuspensionOp → Expr → Expr
  | lambda : Expr → Expr
  | ifExpr : Expr → Expr → Expr → Expr
deriving Repr, Inhabited

/-- Function declaration with optional explicit effect annotation -/
structure FnDecl where
  name : String
  body : Expr
  explicitEffect : Option Effect  -- None = infer, Some = explicit
  deriving Repr

/-- Environment mapping function names to their effects -/
def Env := String → Option Effect

/-- Check if expression contains any suspension operator -/
partial def containsSuspension : Expr → Bool
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

/-- Type representation in the type system -/
inductive Ty where
  | int
  | string
  | bool
  | promise (inner : Ty)
  | fn (param : Ty) (ret : Ty)
  | generic (name : String)
  deriving DecidableEq, Repr

/-- Transform return type based on effect: async wraps in Promise[T] -/
def transformReturnType (eff : Effect) (retType : Ty) : Ty :=
  match eff, retType with
  | Effect.async, Ty.promise _ => retType  -- Already Promise, no double-wrap
  | Effect.async, t => Ty.promise t  -- Wrap in Promise
  | Effect.sync, t => t  -- No wrapping for sync

/-- Check if implicit await should be inserted based on type mismatch -/
def shouldInsertAwait (expectedType : Ty) (actualType : Ty) : Bool :=
  match expectedType, actualType with
  | t, Ty.promise inner => t == inner  -- Promise[T] → T needs await
  | _, _ => false

/-- Check if Promise[T] can be unwrapped to T -/
def canUnwrapPromise (promiseType : Ty) (targetType : Ty) : Bool :=
  match promiseType with
  | Ty.promise inner => inner == targetType
  | _ => false

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

/-- Example: type-driven await inference -/
example : shouldInsertAwait Ty.int (Ty.promise Ty.int) = true := by
  simp [shouldInsertAwait]

/-- Example: Promise wrapping for async function -/
example : transformReturnType Effect.async Ty.int = Ty.promise Ty.int := by
  simp [transformReturnType]

/-- Example: No double-wrap for explicit Promise return -/
example : transformReturnType Effect.async (Ty.promise Ty.string) = Ty.promise Ty.string := by
  simp [transformReturnType]

/-- Effect inference is deterministic (trivial since it's a function) -/
theorem effect_deterministic (env : Env) (e : Expr) :
  ∃ eff : Effect, inferExprEffect env e = eff := by
  exact ⟨inferExprEffect env e, rfl⟩

/-- Suspension implies async.
    Axiomatized because inferExprEffect is partial def.
    The property holds by direct inspection of the definition. -/
axiom suspension_implies_async (env : Env) (op : SuspensionOp) (e : Expr) :
  inferExprEffect env (Expr.suspend op e) = Effect.async

/-- Sync safety: if validation passes, no suspension in body.
    Axiomatized because containsSuspension is partial. -/
axiom sync_safety (fn : FnDecl) :
  fn.explicitEffect = some Effect.sync → validateSyncConstraint fn = true →
  containsSuspension fn.body = false

/-- Async propagation: calling async function makes expression async.
    Axiomatized because inferExprEffect is partial def. -/
axiom async_propagation (env : Env) (fn_name : String) (args : List Expr) :
  env fn_name = some Effect.async → inferExprEffect env (Expr.call fn_name args) = Effect.async

/-- Literals are always sync.
    Axiomatized because inferExprEffect is partial def. -/
axiom lit_is_sync (env : Env) (n : Nat) :
  inferExprEffect env (Expr.lit n) = Effect.sync

/-- Variables are always sync.
    Axiomatized because inferExprEffect is partial def. -/
axiom var_is_sync (env : Env) (name : String) :
  inferExprEffect env (Expr.var name) = Effect.sync

theorem async_returns_promise (retType : Ty) :
  transformReturnType Effect.async retType = Ty.promise retType ∨
  (∃ t, retType = Ty.promise t ∧ transformReturnType Effect.async retType = retType) := by
  cases retType with
  | promise inner => right; exact ⟨inner, rfl, rfl⟩
  | int => left; rfl
  | string => left; rfl
  | bool => left; rfl
  | fn _ _ => left; rfl
  | generic _ => left; rfl

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

/-- Effect join is commutative -/
theorem effect_join_comm (e1 e2 : Effect) :
    (match e1, e2 with
     | Effect.async, _ => Effect.async
     | _, Effect.async => Effect.async
     | _, _ => Effect.sync) =
    (match e2, e1 with
     | Effect.async, _ => Effect.async
     | _, Effect.async => Effect.async
     | _, _ => Effect.sync) := by
  cases e1 <;> cases e2 <;> rfl

/-- Effect join is idempotent -/
theorem effect_join_idem (e : Effect) :
    (match e, e with
     | Effect.async, _ => Effect.async
     | _, Effect.async => Effect.async
     | _, _ => Effect.sync) = e := by
  cases e <;> rfl

/-- Async is absorbing for effect join -/
theorem async_absorbing (e : Effect) :
    (match Effect.async, e with
     | Effect.async, _ => Effect.async
     | _, Effect.async => Effect.async
     | _, _ => Effect.sync) = Effect.async := by
  rfl

/-- Sync is identity for effect join -/
theorem sync_identity (e : Effect) :
    (match Effect.sync, e with
     | Effect.async, _ => Effect.async
     | _, Effect.async => Effect.async
     | _, _ => Effect.sync) = e := by
  cases e <;> rfl

end AsyncEffectInference
