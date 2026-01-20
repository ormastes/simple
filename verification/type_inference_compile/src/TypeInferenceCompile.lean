namespace TypeInferenceCompile

/-- Simple expression language to model inference.
    Extended with Str type for practical string handling. -/
inductive Ty
  | nat
  | bool
  | str
  | generic (name : String) (args : List Ty)
  | arrow (a b : Ty)
  deriving Repr

inductive Expr
  | litNat (n : Nat)
  | litBool (b : Bool)
  | litStr (s : String)
  | add (a b : Expr)
  | concat (a b : Expr)  -- string concatenation
  | generic (name : String) (args : List Expr)
  | ifElse (c t e : Expr)
  | lam (body : Expr)
  | app (f x : Expr)
deriving Repr

mutual
  partial def tyEq : Ty → Ty → Bool
    | Ty.nat, Ty.nat => true
    | Ty.bool, Ty.bool => true
    | Ty.str, Ty.str => true
    | Ty.generic name args, Ty.generic name' args' =>
      if _h_name : name = name' then
        listEq args args'
      else
        false
    | Ty.arrow a b, Ty.arrow a' b' => tyEq a a' && tyEq b b'
    | _, _ => false

  partial def listEq : List Ty → List Ty → Bool
    | [], [] => true
    | hd :: tl, hd' :: tl' =>
      if tyEq hd hd' then listEq tl tl' else false
    | _, _ => false
end

/-- A partial inference judgment; returns `none` on mismatch. -/
def infer : Expr → Option Ty
  | Expr.litNat _ => some Ty.nat
  | Expr.litBool _ => some Ty.bool
  | Expr.litStr _ => some Ty.str
  | Expr.generic name args =>
    let rec inferList : List Expr → Option (List Ty)
      | [] => some []
      | hd :: tl =>
        match infer hd, inferList tl with
        | some hd_ty, some tl_tys => some (hd_ty :: tl_tys)
        | _, _ => none
    match inferList args with
    | some arg_tys => some (Ty.generic name arg_tys)
    | none => none
  | Expr.add a b => do
      let ta ← infer a
      let tb ← infer b
      match ta, tb with
      | Ty.nat, Ty.nat => pure Ty.nat
      | _, _ => none
  | Expr.concat a b => do
      let ta ← infer a
      let tb ← infer b
      match ta, tb with
      | Ty.str, Ty.str => pure Ty.str
      | _, _ => none
  | Expr.ifElse c t e => do
      let tc ← infer c
      match tc with
      | Ty.bool =>
        let τt ← infer t
        let τe ← infer e
        if tyEq τt τe then pure τt else none
      | _ => none
  | Expr.lam body => do
      let τ ← infer body
      pure (Ty.arrow Ty.nat τ)
  | Expr.app f x => do
      let tf ← infer f
      match tf with
      | Ty.arrow a b =>
        let τx ← infer x
        if tyEq τx a then pure b else none
      | _ => none

/-- Determinism: inference yields at most one type. -/
theorem infer_deterministic (e : Expr) (t₁ t₂ : Ty) :
    infer e = some t₁ → infer e = some t₂ → t₁ = t₂ := by
  intro h1 h2
  have : some t₁ = some t₂ := by simpa [h1] using h2
  cases this
  rfl

end TypeInferenceCompile
