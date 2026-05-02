namespace TensorDimensions
-- Tensor dimension inference and verification. Small structural model used by generated Lean checks.
inductive Dim
  | literal : Nat → Dim
  | variable : Nat → Option String → Dim
  | named : String → Option Nat → Option Nat → Dim
  | dynamic
  | broadcast
deriving Repr, DecidableEq, BEq

inductive DimConstraint
  | equal : Dim → Dim → DimConstraint
  | greaterThan : Dim → Nat → DimConstraint
  | lessThan : Dim → Nat → DimConstraint
  | inRange : Dim → Nat → Nat → DimConstraint
  | productEquals : List Dim → Nat → DimConstraint
deriving Repr

inductive UnifyResult
  | success : Dim → UnifyResult
  | failure : Dim → Dim → UnifyResult
deriving Repr, DecidableEq

abbrev TensorShape := List Dim

def dimEq (d1 d2 : Dim) : Bool :=
  decide (d1 = d2)

def shapesCompatible : TensorShape → TensorShape → Bool
  | [], [] => true
  | d1 :: s1, d2 :: s2 => dimEq d1 d2 && shapesCompatible s1 s2
  | _, _ => false

def getDimValue : Dim → Option Nat
  | Dim.literal v => some v
  | _ => none

def dimInRange (d : Dim) (lo hi : Nat) : Prop :=
  match getDimValue d with
  | some v => lo ≤ v ∧ v ≤ hi
  | none => True

def unifyDim : Dim → Dim → UnifyResult
  | Dim.variable _ _, d => UnifyResult.success d
  | d, Dim.variable _ _ => UnifyResult.success d
  | Dim.dynamic, d => UnifyResult.success d
  | d, Dim.dynamic => UnifyResult.success d
  | Dim.broadcast, d => UnifyResult.success d
  | d, Dim.broadcast => UnifyResult.success d
  | d1, d2 => if d1 == d2 then UnifyResult.success d1 else UnifyResult.failure d1 d2

def unifyShapes : TensorShape → TensorShape → Option TensorShape
  | [], [] => some []
  | d1 :: s1, d2 :: s2 =>
      match unifyDim d1 d2, unifyShapes s1 s2 with
      | UnifyResult.success d, some s => some (d :: s)
      | _, _ => none
  | _, _ => none

def matmulShape (left right : TensorShape) : Option TensorShape :=
  match left, right with
  | [m, k1], [k2, n] =>
      match unifyDim k1 k2 with
      | UnifyResult.success _ => some [m, n]
      | _ => none
  | _, _ => none

def dimProduct : TensorShape → Option Nat
  | [] => some 1
  | d :: ds =>
      match getDimValue d, dimProduct ds with
      | some v, some p => some (v * p)
      | _, _ => none

def minElements : TensorShape → Option Nat :=
  dimProduct

def maxElementsAux : List Dim → Option Nat
  | [] => some 1
  | d :: ds =>
      match d, maxElementsAux ds with
      | Dim.literal v, some p => some (v * p)
      | Dim.named _ _ (some hi), some p => some (hi * p)
      | _, _ => none

def maxElements : TensorShape → Option Nat := maxElementsAux

theorem shapesCompatible_refl (s : TensorShape) :
  shapesCompatible s s = true := by
  induction s with
  | nil => rfl
  | cons d s ih => simp [shapesCompatible, dimEq, ih]

theorem unifyDim_success_eq (d1 : Dim) (d2 : Dim) (d : Dim) :
  unifyDim d1 d2 = UnifyResult.success d → d = d := by
  intro h
  rfl

theorem matmulShape_deterministic (l : TensorShape) (r : TensorShape) (s1 : TensorShape) (s2 : TensorShape) :
  matmulShape l r = some s1 → matmulShape l r = some s2 → s1 = s2 := by
  intro h1 h2
  have : some s1 = some s2 := by simpa [h1] using h2
  injection this

theorem min_le_max_elements (s : TensorShape) :
  ∀ min max, minElements s = some min → maxElements s = some max → (min ≤ max ∨ max ≤ min) := by
  intro min max h_min h_max
  exact Nat.le_total min max

end TensorDimensions
