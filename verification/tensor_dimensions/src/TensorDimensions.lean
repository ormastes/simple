namespace TensorDimensions
-- Tensor dimension inference and verification.
--     Provides compile-time dimension tracking with range constraints.
inductive Dim
  | literal : Nat → Dim
  | variable : Nat → Option String → Dim
  | named : String → Option Nat → Option Nat → Dim
  | dynamic
  | broadcast
deriving Repr, DecidableEq

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
deriving Repr

abbrev TensorShape := List Dim

-- Check if two dimensions are equal (for unification).
def dimEq : Dim → Dim → bool
  | Dim.literal v1, Dim.literal v2 => v1 = v2
  | Dim.variable id1 _, Dim.variable id2 _ => id1 = id2
  | Dim.named n1 _ _, Dim.named n2 _ _ => n1 = n2
  | Dim.dynamic, Dim.dynamic => true
  | Dim.broadcast, Dim.broadcast => true
  | _, _ => false

-- Check if two shapes are compatible (same rank, compatible dims).
def shapesCompatible : TensorShape → TensorShape → bool
  | [], [] => true
  | d1 . s1, d2 . s2 => dimEq d1 d2 && shapesCompatible s1 s2
  | _, _ => false

-- Get concrete value from dimension if literal.
def getDimValue : Dim → Option ℕ
  | Dim.literal v => some v
  | _ => none

-- Check if dimension satisfies range constraint.
def dimInRange (d : Dim) (lo hi : ℕ) : Prop :=
  match getDimValue d with
  | some v => lo ≤ v ∧ v ≤ hi
  | none => True  -- Dynamic dims always satisfy

-- Result of dimension unification.
-- Unify two dimensions, returning unified dim or error.
def unifyDim : Dim → Dim → UnifyResult
  -- Same literal
  | Dim.literal v1, Dim.literal v2 =>
    if v1 = v2 then UnifyResult.success (Dim.literal v1)
    else UnifyResult.failure (Dim.literal v1) (Dim.literal v2)
  -- Variable binds to anything
  | Dim.variable _ _, d => UnifyResult.success d
  | d, Dim.variable _ _ => UnifyResult.success d
  -- Dynamic matches anything
  | Dim.dynamic, d => UnifyResult.success d
  | d, Dim.dynamic => UnifyResult.success d
  -- Broadcast rules
  | Dim.broadcast, Dim.literal 1 => UnifyResult.success (Dim.literal 1)
  | Dim.literal 1, Dim.broadcast => UnifyResult.success (Dim.literal 1)
  | Dim.broadcast, d => UnifyResult.success d
  | d, Dim.broadcast => UnifyResult.success d
  -- Named dims with same name
  | Dim.named n1 lo1 hi1, Dim.named n2 lo2 hi2 =>
    if n1 = n2 then UnifyResult.success (Dim.named n1 lo1 hi1)
    else UnifyResult.failure (Dim.named n1 lo1 hi1) (Dim.named n2 lo2 hi2)
  -- Default: failure
  | d1, d2 => UnifyResult.failure d1 d2

-- Unify two shapes dimension by dimension.
def unifyShapes : TensorShape → TensorShape → Option TensorShape
  | [], [] => some []
  | d1 . s1, d2 . s2 =>
    match unifyDim d1 d2, unifyShapes s1 s2 with
    | UnifyResult.success d, some s => some (d . s)
    | _, _ => none
  | _, _ => none

-- Infer shape of matrix multiplication [M,K] @ [K,N] -> [M,N].
def matmulShape (left right : TensorShape) : Option TensorShape :=
  match left, right with
  | [m, k1], [k2, n] =>
    match unifyDim k1 k2 with
    | UnifyResult.success _ => some [m, n]
    | UnifyResult.failure _ _ => none
  | _, _ => none

-- Shape compatibility is reflexive.
-- Successful unification implies dimension equality.
-- Matmul shape inference is deterministic.
-- Product of dimensions helper.
def dimProduct : TensorShape → Option ℕ
  | [] => some 1
  | d . ds =>
    match getDimValue d, dimProduct ds with
    | some v, some p => some (v * p)
    | _, _ => none

-- Minimum memory for shape (in elements).
def minElements : TensorShape → Option ℕ :=
  dimProduct

-- Maximum memory for shape (using range upper bounds).
def maxElementsAux : List Dim → Option ℕ
  | [] => some 1
  | d . ds =>
    match d, maxElementsAux ds with
    | Dim.literal v, some p => some (v * p)
    | Dim.named _ _ (some hi), some p => some (hi * p)
    | _, _ => none

def maxElements : TensorShape → Option ℕ := maxElementsAux

-- Min elements ≤ max elements when both exist.
theorem shapesCompatible_refl (s : TensorShape) :
  shapesCompatible s s = true := by
  induction s with
  | nil => rfl
  | cons d s' ih => simp [shapesCompatible, dimEq]; exact ih

theorem unifyDim_success_eq (d1 : Dim) (d2 : Dim) (d : Dim) :
  unifyDim d1 d2 = UnifyResult.success d → dimEq d1 d ∨ dimEq d2 d := by
  intro h
  cases d1 <;> cases d2 <;> simp [unifyDim] at h <;> try (left; simp [dimEq]; rfl) <;> try (right; simp [dimEq]; rfl)

theorem matmulShape_deterministic (l : TensorShape) (r : TensorShape) (s1 : TensorShape) (s2 : TensorShape) :
  matmulShape l r = some s1 → matmulShape l r = some s2 → s1 = s2 := by
  intro h1 h2
  have : some s1 = some s2 := by simpa [h1] using h2
  cases this
  rfl

theorem min_le_max_elements (s : TensorShape) :
  ∀ min max, minElements s = some min → maxElements s = some max → min ≤ max := by
  intro min max h_min h_max
  sorry  -- Requires induction on s with product monotonicity

end TensorDimensions
