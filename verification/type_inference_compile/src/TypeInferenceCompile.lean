namespace TypeInferenceCompile

/-- Simple expression language to model inference. -/
inductive Ty
  | nat
  | bool
  | arrow (a b : Ty)
  deriving DecidableEq, Repr

inductive Expr
  | litNat (n : Nat)
  | litBool (b : Bool)
  | add (a b : Expr)
  | ifElse (c t e : Expr)
  | lam (body : Expr)
  | app (f x : Expr)
  deriving Repr

/-- A partial inference judgment; returns `none` on mismatch. -/
def infer : Expr → Option Ty
  | Expr.litNat _ => some Ty.nat
  | Expr.litBool _ => some Ty.bool
  | Expr.add a b => do
      let ta ← infer a
      let tb ← infer b
      match ta, tb with
      | Ty.nat, Ty.nat => pure Ty.nat
      | _, _ => none
  | Expr.ifElse c t e => do
      let tc ← infer c
      match tc with
      | Ty.bool =>
          let τt ← infer t
          let τe ← infer e
          if τt = τe then pure τt else none
      | _ => none
  | Expr.lam body => do
      let τ ← infer body
      pure (Ty.arrow Ty.nat τ) -- toy rule: lambda abstracts a Nat argument
  | Expr.app f x => do
      let tf ← infer f
      match tf with
      | Ty.arrow a b =>
          let τx ← infer x
          if τx = a then pure b else none
      | _ => none

/-- Determinism: inference yields at most one type. -/
theorem infer_deterministic (e : Expr) (t₁ t₂ : Ty) :
    infer e = some t₁ → infer e = some t₂ → t₁ = t₂ := by
  intro h1 h2
  have : some t₁ = some t₂ := by simpa [h1] using h2
  cases this
  rfl

end TypeInferenceCompile
