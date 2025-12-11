namespace TypeInferenceCompile

/-- Simple expression language to model inference.
    Extended with Str type for practical string handling. -/
inductive Ty
  | nat
  | bool
  | str
  | arrow (a b : Ty)
  deriving DecidableEq, Repr

inductive Expr
  | litNat (n : Nat)
  | litBool (b : Bool)
  | litStr (s : String)
  | add (a b : Expr)
  | concat (a b : Expr)  -- string concatenation
  | ifElse (c t e : Expr)
  | lam (body : Expr)
  | app (f x : Expr)
  deriving Repr

/-- A partial inference judgment; returns `none` on mismatch. -/
def infer : Expr → Option Ty
  | Expr.litNat _ => some Ty.nat
  | Expr.litBool _ => some Ty.bool
  | Expr.litStr _ => some Ty.str
  | Expr.add a b => do
      let ta ← infer a
      let tb ← infer b
      match ta, tb with
      | Ty.nat, Ty.nat => pure Ty.nat
      -- Explicit: addition only works on nat
      | Ty.bool, _ | Ty.str, _ | Ty.arrow _ _, _ => none
      | _, Ty.bool | _, Ty.str | _, Ty.arrow _ _ => none
  | Expr.concat a b => do
      let ta ← infer a
      let tb ← infer b
      match ta, tb with
      | Ty.str, Ty.str => pure Ty.str
      -- Explicit: concatenation only works on str
      | Ty.nat, _ | Ty.bool, _ | Ty.arrow _ _, _ => none
      | _, Ty.nat | _, Ty.bool | _, Ty.arrow _ _ => none
  | Expr.ifElse c t e => do
      let tc ← infer c
      match tc with
      | Ty.bool =>
          let τt ← infer t
          let τe ← infer e
          if τt = τe then pure τt else none
      -- Explicit: condition must be bool
      | Ty.nat => none
      | Ty.str => none
      | Ty.arrow _ _ => none
  | Expr.lam body => do
      let τ ← infer body
      pure (Ty.arrow Ty.nat τ) -- toy rule: lambda abstracts a Nat argument
  | Expr.app f x => do
      let tf ← infer f
      match tf with
      | Ty.arrow a b =>
          let τx ← infer x
          if τx = a then pure b else none
      -- Explicit: only arrow types can be applied
      | Ty.nat => none
      | Ty.bool => none
      | Ty.str => none

/-- Determinism: inference yields at most one type. -/
theorem infer_deterministic (e : Expr) (t₁ t₂ : Ty) :
    infer e = some t₁ → infer e = some t₂ → t₁ = t₂ := by
  intro h1 h2
  have : some t₁ = some t₂ := by simpa [h1] using h2
  cases this
  rfl

end TypeInferenceCompile
