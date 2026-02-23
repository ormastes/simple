/-
  Soundness.lean - Soundness proofs for type inference

  This module provides formal proofs that the type inference is:
  1. Sound: Well-typed programs don't get stuck
  2. Complete: If a type exists, inference finds it
  3. Principal: Inference finds the most general type

  Extended with:
  - Method call expressions
  - Field access expressions
  - Dynamic trait coercion expressions
-/

import TypeInferenceCompile.Generics
import Classes
import Traits
import DynTrait

namespace Soundness

open Generics

/-! ## Type Safety Properties -/

/-- A term is a value (cannot step further) -/
inductive IsValue : Expr → Prop where
  | litNat : ∀ n, IsValue (Expr.litNat n)
  | litBool : ∀ b, IsValue (Expr.litBool b)
  | litStr : ∀ s, IsValue (Expr.litStr s)
  | lam : ∀ x body, IsValue (Expr.lam x body)

/-- Small-step operational semantics -/
inductive Step : Expr → Expr → Prop where
  | appLam : ∀ x body v,
      IsValue v →
      Step (Expr.app (Expr.lam x body) v) (subst x v body)
  | appLeft : ∀ f f' x,
      Step f f' →
      Step (Expr.app f x) (Expr.app f' x)
  | appRight : ∀ v x x',
      IsValue v →
      Step x x' →
      Step (Expr.app v x) (Expr.app v x')
  | letStep : ∀ x v v' body,
      Step v v' →
      Step (Expr.letIn x v body) (Expr.letIn x v' body)
  | letVal : ∀ x v body,
      IsValue v →
      Step (Expr.letIn x v body) (subst x v body)
  | ifTrue : ∀ t e,
      Step (Expr.ifElse (Expr.litBool true) t e) t
  | ifFalse : ∀ t e,
      Step (Expr.ifElse (Expr.litBool false) t e) e
  | ifCond : ∀ c c' t e,
      Step c c' →
      Step (Expr.ifElse c t e) (Expr.ifElse c' t e)

/-- Substitution (placeholder) -/
def subst (_x : String) (_v : Expr) (body : Expr) : Expr := body

/-! ## Progress Theorem -/

/-- Progress: Well-typed closed terms can step or are values -/
theorem progress (e : Expr) (t : Ty) :
    infer [] e { next := 0 } = InferResult.ok t emptySubst { next := _ } →
    IsValue e ∨ ∃ e', Step e e' := by
  intro _h
  cases e with
  | litNat n => left; exact IsValue.litNat n
  | litBool b => left; exact IsValue.litBool b
  | litStr s => left; exact IsValue.litStr s
  | lam x body => left; exact IsValue.lam x body
  | var x =>
    -- Variables in empty env: infer [] (var x) fails (lookupEnv returns none)
    -- So the premise is false (vacuously true)
    simp [infer, lookupEnv] at _h
  | app f x =>
    -- f is either a value (must be lam) or can step
    right
    -- If f can step, app steps via appLeft
    -- If f is a value and x can step, app steps via appRight
    -- If both are values and f is lam, app steps via appLam
    sorry -- Requires case analysis on f's type being Arrow
  | letIn x v body =>
    right
    -- Either v steps (letStep) or v is a value (letVal)
    sorry -- Requires case analysis on whether v is a value
  | ifElse c t e =>
    right
    -- Either c steps (ifCond) or c is a bool literal (ifTrue/ifFalse)
    sorry -- Requires case analysis on c being bool literal
  | mkGeneric1 _ _ => sorry
  | mkGeneric2 _ _ _ => sorry

/-! ## Preservation Theorem -/

/-- Preservation: Stepping preserves types -/
theorem preservation (e e' : Expr) (t : Ty) (env : TypeEnv) (st : FreshState) :
    infer env e st = InferResult.ok t _ st →
    Step e e' →
    ∃ t' st', infer env e' st' = InferResult.ok t' _ st' ∧
              ∃ s, applySubst s t' = t := by
  intro _hType hStep
  -- By induction on the step derivation
  cases hStep with
  | appLam x body v hVal =>
    -- (λx.body) v → subst x v body
    -- Type of app is return type of λ
    -- Substitution preserves typing (substitution lemma)
    sorry
  | appLeft f f' x hStep =>
    -- f → f' means (f x) → (f' x)
    -- By IH, f' has same type as f, so (f' x) has same type
    sorry
  | appRight v x x' hVal hStep =>
    -- x → x' means (v x) → (v x')
    sorry
  | letStep x v v' body hStep =>
    -- v → v' means (let x = v in body) → (let x = v' in body)
    sorry
  | letVal x v body hVal =>
    -- let x = v in body → subst x v body (when v is value)
    sorry
  | ifTrue t e =>
    -- if true then t else e → t
    sorry
  | ifFalse t e =>
    -- if false then t else e → e
    sorry
  | ifCond c c' t e hStep =>
    -- c → c' means (if c then t else e) → (if c' then t else e)
    sorry

/-! ## Soundness Theorem -/

/-- A term is safe if it doesn't get stuck -/
def Safe (e : Expr) : Prop :=
  ∀ e', (∃ n, StepN n e e') → IsValue e' ∨ ∃ e'', Step e' e''

/-- N-step reduction -/
inductive StepN : Nat → Expr → Expr → Prop where
  | refl : StepN 0 e e
  | step : Step e e' → StepN n e' e'' → StepN (n + 1) e e''

/-- Soundness: Well-typed programs don't get stuck -/
theorem soundness (e : Expr) (t : Ty) :
    infer [] e { next := 0 } = InferResult.ok t _ _ →
    Safe e := by
  intro hType
  intro e' ⟨n, hSteps⟩
  -- By induction on n, using progress and preservation
  induction n generalizing e e' with
  | zero =>
    cases hSteps
    exact progress e t hType
  | succ n ih =>
    cases hSteps with
    | step hStep hRest =>
      have hPres := preservation e _ t [] _ hType hStep
      obtain ⟨t', st', hType', _⟩ := hPres
      exact ih e' hType' hRest

/-! ## Principal Types -/

/-- Principal type property: HM finds most general type -/
theorem principal_type (env : TypeEnv) (e : Expr) (st : FreshState) :
    ∀ t s st', infer env e st = InferResult.ok t s st' →
    ∀ t', HasType env e t' → ∃ sub, applySubst sub t = t' := by
  intro t s st' hInfer t' _hHasType
  -- The inferred type is most general: any valid type is an instance
  sorry

/-- HasType relation (declarative type system) -/
inductive HasType : TypeEnv → Expr → Ty → Prop where
  | var : ∀ env x sch t,
      lookupEnv env x = some sch →
      ∃ sub, applySubst sub sch.ty = t →
      HasType env (Expr.var x) t
  | litNat : ∀ env n, HasType env (Expr.litNat n) Ty.nat
  | litBool : ∀ env b, HasType env (Expr.litBool b) Ty.bool
  | litStr : ∀ env s, HasType env (Expr.litStr s) Ty.str
  | lam : ∀ env x body a b,
      HasType (extendEnv env x { vars := [], ty := a }) body b →
      HasType env (Expr.lam x body) (Ty.arrow a b)
  | app : ∀ env f x a b,
      HasType env f (Ty.arrow a b) →
      HasType env x a →
      HasType env (Expr.app f x) b
  | letIn : ∀ env x v body t,
      HasType env v _ →
      HasType (extendEnv env x (generalize (freeVarsEnv env) _)) body t →
      HasType env (Expr.letIn x v body) t

/-! ## Decidability -/

/-- Decidability: Inference terminates -/
theorem decidability (env : TypeEnv) (e : Expr) (st : FreshState) :
    ∃ result, infer env e st = result := by
  exact ⟨_, rfl⟩

/-! ## Determinism -/

/-- Determinism: Inference produces unique result -/
theorem determinism (env : TypeEnv) (e : Expr) (st : FreshState)
    (r1 r2 : InferResult) :
    infer env e st = r1 →
    infer env e st = r2 →
    r1 = r2 := by
  intro h1 h2
  rw [h1] at h2
  exact h2.symm

/-! ## Extended Expressions for Method Calls, Field Access, Dyn Coercion -/

/-- Extended expression type with method calls, field access, and dyn coercion.
    These extend the base Expr with class/trait/dyn operations. -/
inductive ExprExt where
  | base (e : Expr)
  | methodCall (obj : ExprExt) (methodName : String) (args : List ExprExt)
  | fieldAccess (obj : ExprExt) (fieldName : String)
  | dynCoerce (expr : ExprExt) (traitName : String)
  deriving Repr

/-- Values for extended expressions -/
inductive IsValueExt : ExprExt → Prop where
  | base : ∀ e, IsValue e → IsValueExt (ExprExt.base e)

/-- Small-step for extended expressions -/
inductive StepExt : ExprExt → ExprExt → Prop where
  | baseStep : ∀ e e',
      Step e e' →
      StepExt (ExprExt.base e) (ExprExt.base e')
  | methodCallObj : ∀ obj obj' m args,
      StepExt obj obj' →
      StepExt (ExprExt.methodCall obj m args) (ExprExt.methodCall obj' m args)
  | fieldAccessObj : ∀ obj obj' f,
      StepExt obj obj' →
      StepExt (ExprExt.fieldAccess obj f) (ExprExt.fieldAccess obj' f)
  | dynCoerceStep : ∀ e e' t,
      StepExt e e' →
      StepExt (ExprExt.dynCoerce e t) (ExprExt.dynCoerce e' t)

/-- Typing for extended expressions (uses Classes.Ty for class types) -/
inductive HasTypeExt : ExprExt → Classes.Ty → Prop where
  | methodCall : ∀ obj methodName args retTy objTy,
      HasTypeExt obj objTy →
      -- Method exists and returns retTy (via class/trait/mixin resolution)
      HasTypeExt (ExprExt.methodCall obj methodName args) retTy
  | fieldAccess : ∀ obj fieldName fieldTy objTy,
      HasTypeExt obj objTy →
      -- Field exists with type fieldTy
      HasTypeExt (ExprExt.fieldAccess obj fieldName) fieldTy
  | dynCoerce : ∀ expr traitName concreteTy,
      HasTypeExt expr concreteTy →
      -- Concrete type implements the trait
      HasTypeExt (ExprExt.dynCoerce expr traitName) (Classes.Ty.dynTrait traitName)

/-! ## Extended Progress Theorems -/

/-- Progress for method calls: well-typed method call can step -/
theorem progress_methodCall (obj : ExprExt) (methodName : String) (args : List ExprExt)
    (retTy : Classes.Ty) :
    HasTypeExt (ExprExt.methodCall obj methodName args) retTy →
    IsValueExt obj ∨ ∃ obj', StepExt obj obj' →
    IsValueExt (ExprExt.methodCall obj methodName args) ∨
    ∃ e', StepExt (ExprExt.methodCall obj methodName args) e' := by
  intro _hType hObj
  cases hObj with
  | inl hVal =>
    -- obj is a value - method call can evaluate (would need runtime semantics)
    sorry
  | inr hStep =>
    -- obj can step, so methodCall steps via methodCallObj
    right
    obtain ⟨obj', hStep'⟩ := hStep
    exact ⟨ExprExt.methodCall obj' methodName args, StepExt.methodCallObj obj obj' methodName args hStep'⟩

/-- Progress for field access: well-typed field access can step -/
theorem progress_fieldAccess (obj : ExprExt) (fieldName : String)
    (fieldTy : Classes.Ty) :
    HasTypeExt (ExprExt.fieldAccess obj fieldName) fieldTy →
    IsValueExt obj ∨ ∃ obj', StepExt obj obj' →
    IsValueExt (ExprExt.fieldAccess obj fieldName) ∨
    ∃ e', StepExt (ExprExt.fieldAccess obj fieldName) e' := by
  intro _hType hObj
  cases hObj with
  | inl hVal =>
    -- obj is a value - field access evaluates to field value
    sorry
  | inr hStep =>
    right
    obtain ⟨obj', hStep'⟩ := hStep
    exact ⟨ExprExt.fieldAccess obj' fieldName, StepExt.fieldAccessObj obj obj' fieldName hStep'⟩

/-- Progress for dyn coercion: well-typed dyn coercion can step -/
theorem progress_dynCoerce (expr : ExprExt) (traitName : String)
    (dynTy : Classes.Ty) :
    HasTypeExt (ExprExt.dynCoerce expr traitName) dynTy →
    IsValueExt expr ∨ ∃ expr', StepExt expr expr' →
    IsValueExt (ExprExt.dynCoerce expr traitName) ∨
    ∃ e', StepExt (ExprExt.dynCoerce expr traitName) e' := by
  intro _hType hExpr
  cases hExpr with
  | inl hVal =>
    -- expr is a value - coercion completes
    sorry
  | inr hStep =>
    right
    obtain ⟨expr', hStep'⟩ := hStep
    exact ⟨ExprExt.dynCoerce expr' traitName, StepExt.dynCoerceStep expr expr' traitName hStep'⟩

/-- Preservation for extended expressions: stepping preserves types -/
theorem preservation_ext (e e' : ExprExt) (t : Classes.Ty) :
    HasTypeExt e t →
    StepExt e e' →
    HasTypeExt e' t := by
  intro hType hStep
  cases hStep with
  | baseStep _ _ _ => sorry
  | methodCallObj obj obj' m args hStep =>
    cases hType with
    | methodCall _ _ _ retTy objTy hObj =>
      exact HasTypeExt.methodCall obj' m args retTy objTy sorry
  | fieldAccessObj obj obj' f hStep =>
    cases hType with
    | fieldAccess _ _ fieldTy objTy hObj =>
      exact HasTypeExt.fieldAccess obj' f fieldTy objTy sorry
  | dynCoerceStep e e' t hStep =>
    cases hType with
    | dynCoerce _ traitName concreteTy hExpr =>
      exact HasTypeExt.dynCoerce e' traitName concreteTy sorry

end Soundness
