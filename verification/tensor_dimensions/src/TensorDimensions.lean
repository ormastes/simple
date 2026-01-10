-- Tensor Dimension Inference - Formal Verification
-- This file is generated from Simple verification model
-- See: simple/std_lib/src/verification/regenerate/tensor_dimensions.spl

/-!
# Tensor Dimension Inference - Formal Verification

Tensor dimension inference and verification with compile-time dimension tracking
and range constraints.
-/

namespace TensorDimensions

-- ========================================================================
-- Dimension Type
-- ========================================================================

/-- Dimension representation with literals, variables, named dims, dynamic, and broadcast -/
inductive Dim where
  | literal (value : Nat)
  | variable (id : Nat) (name : Option String)
  | named (name : String) (lo : Option Nat) (hi : Option Nat)
  | dynamic
  | broadcast
  deriving Repr, DecidableEq

/-- Tensor shape is a list of dimensions -/
abbrev TensorShape := List Dim

-- ========================================================================
-- Dimension Constraint Type
-- ========================================================================

/-- Constraints on dimensions for verification -/
inductive DimConstraint where
  | equal (d1 : Dim) (d2 : Dim)
  | greaterThan (d : Dim) (min : Nat)
  | lessThan (d : Dim) (max : Nat)
  | inRange (d : Dim) (lo : Nat) (hi : Nat)
  | productEquals (dims : List Dim) (value : Nat)
  deriving Repr

-- ========================================================================
-- Dimension Equality
-- ========================================================================

/-- Check if two dimensions are equal (for unification). -/
def dimEq : Dim → Dim → Bool
  | Dim.literal v1, Dim.literal v2 => v1 = v2
  | Dim.variable id1 _, Dim.variable id2 _ => id1 = id2
  | Dim.named n1 _ _, Dim.named n2 _ _ => n1 = n2
  | Dim.dynamic, Dim.dynamic => true
  | Dim.broadcast, Dim.broadcast => true
  | _, _ => false

-- ========================================================================
-- Shape Compatibility
-- ========================================================================

/-- Check if two shapes are compatible (same rank, compatible dims). -/
def shapesCompatible : TensorShape → TensorShape → Bool
  | [], [] => true
  | d1 :: s1, d2 :: s2 => dimEq d1 d2 && shapesCompatible s1 s2
  | _, _ => false

-- ========================================================================
-- Dimension Value Extraction
-- ========================================================================

/-- Get concrete value from dimension if literal. -/
def getDimValue : Dim → Option Nat
  | Dim.literal v => some v
  | _ => none

-- ========================================================================
-- Range Checking
-- ========================================================================

/-- Check if dimension satisfies range constraint. -/
def dimInRange (d : Dim) (lo hi : Nat) : Prop :=
  match getDimValue d with
  | some v => lo ≤ v ∧ v ≤ hi
  | none => True  -- Dynamic dims always satisfy

-- ========================================================================
-- Unification Result
-- ========================================================================

/-- Result of dimension unification. -/
inductive UnifyResult where
  | success (d : Dim)
  | failure (expected : Dim) (actual : Dim)
  deriving Repr

-- ========================================================================
-- Dimension Unification
-- ========================================================================

/-- Unify two dimensions, returning unified dim or error. -/
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

-- ========================================================================
-- Shape Unification
-- ========================================================================

/-- Unify two shapes dimension by dimension. -/
def unifyShapes : TensorShape → TensorShape → Option TensorShape
  | [], [] => some []
  | d1 :: s1, d2 :: s2 =>
    match unifyDim d1 d2, unifyShapes s1 s2 with
    | UnifyResult.success d, some s => some (d :: s)
    | _, _ => none
  | _, _ => none

-- ========================================================================
-- Matrix Multiplication Shape Inference
-- ========================================================================

/-- Infer shape of matrix multiplication [M,K] @ [K,N] -> [M,N]. -/
def matmulShape (left right : TensorShape) : Option TensorShape :=
  match left, right with
  | [m, k1], [k2, n] =>
    match unifyDim k1 k2 with
    | UnifyResult.success _ => some [m, n]
    | UnifyResult.failure _ _ => none
  | _, _ => none

-- ========================================================================
-- Theorems
-- ========================================================================

/-- Dimension equality is reflexive. -/
theorem dimEq_refl (d : Dim) : dimEq d d = true := by
  cases d <;> simp [dimEq]

/-- Shape compatibility is reflexive. -/
theorem shapesCompatible_refl (s : TensorShape) :
  shapesCompatible s s = true := by
  induction s with
  | nil => rfl
  | cons d s' ih =>
    simp [shapesCompatible]
    constructor
    · exact dimEq_refl d
    · exact ih

/-- Helper lemmas for each unifyDim success pattern -/

/-- Literal equality case -/
theorem unifyDim_lit_lit_eq (v : Nat) :
  unifyDim (Dim.literal v) (Dim.literal v) = UnifyResult.success (Dim.literal v) := by
  simp [unifyDim]

/-- Variable left binds to anything -/
theorem unifyDim_var_left (id : Nat) (name : Option String) (d : Dim) :
  unifyDim (Dim.variable id name) d = UnifyResult.success d := by
  cases d <;> rfl

/-- Variable right binds to anything -/
theorem unifyDim_var_right (d : Dim) (id : Nat) (name : Option String) :
  unifyDim d (Dim.variable id name) = UnifyResult.success d := by
  cases d <;> rfl

/-- Dynamic left matches anything -/
theorem unifyDim_dynamic_left (d : Dim) :
  unifyDim Dim.dynamic d = UnifyResult.success d := by
  cases d <;> rfl

/-- Dynamic right matches anything -/
theorem unifyDim_dynamic_right (d : Dim) :
  unifyDim d Dim.dynamic = UnifyResult.success d := by
  cases d <;> rfl

/-- Broadcast with literal 1 -/
theorem unifyDim_broadcast_one :
  unifyDim Dim.broadcast (Dim.literal 1) = UnifyResult.success (Dim.literal 1) := by
  rfl

/-- Literal 1 with broadcast -/
theorem unifyDim_one_broadcast :
  unifyDim (Dim.literal 1) Dim.broadcast = UnifyResult.success (Dim.literal 1) := by
  rfl

/-- Broadcast left (non-1 case handled by pattern priority) -/
theorem unifyDim_broadcast_left (d : Dim) (h : d ≠ Dim.literal 1) :
  unifyDim Dim.broadcast d = UnifyResult.success d := by
  cases d <;> try rfl
  case literal v =>
    by_cases hv : v = 1
    · subst hv
      contradiction
    · rfl

/-- Broadcast right (non-1 case) -/
theorem unifyDim_broadcast_right (d : Dim) (h : d ≠ Dim.literal 1) :
  unifyDim d Dim.broadcast = UnifyResult.success d := by
  cases d <;> try rfl
  case literal v =>
    by_cases hv : v = 1
    · subst hv
      contradiction
    · rfl

/-- Named with same name -/
theorem unifyDim_named_eq (n : String) (lo1 hi1 lo2 hi2 : Option Nat) :
  unifyDim (Dim.named n lo1 hi1) (Dim.named n lo2 hi2) =
    UnifyResult.success (Dim.named n lo1 hi1) := by
  simp [unifyDim]

/-- Successful unification implies dimension equality. -/
theorem unifyDim_success_eq (d1 d2 d : Dim) :
  unifyDim d1 d2 = UnifyResult.success d → dimEq d1 d = true ∨ dimEq d2 d = true := by
  intro h
  -- Proof by exhaustive case analysis on the 11 unifyDim patterns
  cases d1 <;> cases d2
  -- Case 1: literal, literal
  case literal v1 v2 =>
    simp only [unifyDim] at h
    split at h
    · -- v1 = v2, success case
      injection h with h_eq
      left
      simp [dimEq, h_eq]
    · -- v1 ≠ v2, failure case - contradiction
      contradiction
  -- Cases 2-3: variable binds
  case literal.variable v id name =>
    rw [unifyDim_var_right] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case variable.literal id name v =>
    rw [unifyDim_var_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case variable.variable id1 name1 id2 name2 =>
    rw [unifyDim_var_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  -- Cases with dynamic
  case literal.dynamic v =>
    rw [unifyDim_dynamic_right] at h
    injection h with h_eq
    left
    rw [h_eq]
    exact dimEq_refl _
  case dynamic.literal v =>
    rw [unifyDim_dynamic_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case variable.dynamic id name =>
    rw [unifyDim_dynamic_right] at h
    injection h with h_eq
    left
    rw [h_eq]
    exact dimEq_refl _
  case dynamic.variable id name =>
    rw [unifyDim_dynamic_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case dynamic.dynamic =>
    rw [unifyDim_dynamic_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  -- Cases with named
  case literal.named v n lo hi =>
    simp only [unifyDim] at h
    -- This is the default case (failure)
    contradiction
  case named.literal n lo hi v =>
    simp only [unifyDim] at h
    contradiction
  case variable.named id name n lo hi =>
    rw [unifyDim_var_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case named.variable n lo hi id name =>
    rw [unifyDim_var_right] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case dynamic.named n lo hi =>
    rw [unifyDim_dynamic_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case named.dynamic n lo hi =>
    rw [unifyDim_dynamic_right] at h
    injection h with h_eq
    left
    rw [h_eq]
    exact dimEq_refl _
  case named.named n1 lo1 hi1 n2 lo2 hi2 =>
    simp only [unifyDim] at h
    split at h
    · -- n1 = n2, success case
      injection h with h_eq
      left
      simp [dimEq, h_eq]
    · -- n1 ≠ n2, failure case
      contradiction
  -- Cases with broadcast
  case literal.broadcast v =>
    simp only [unifyDim] at h
    split at h
    · -- v = 1 case
      injection h with h_eq
      right
      simp [dimEq, h_eq]
    · -- v ≠ 1, success with literal v
      injection h with h_eq
      left
      rw [h_eq]
      exact dimEq_refl _
  case broadcast.literal v =>
    simp only [unifyDim] at h
    split at h
    · -- v = 1
      injection h with h_eq
      left
      simp [dimEq, h_eq]
    · -- v ≠ 1
      injection h with h_eq
      right
      rw [← h_eq]
      exact dimEq_refl _
  case variable.broadcast id name =>
    rw [unifyDim_var_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case broadcast.variable id name =>
    simp only [unifyDim] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case dynamic.broadcast =>
    rw [unifyDim_dynamic_left] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case broadcast.dynamic =>
    simp only [unifyDim] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case named.broadcast n lo hi =>
    simp only [unifyDim] at h
    contradiction
  case broadcast.named n lo hi =>
    simp only [unifyDim] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _
  case broadcast.broadcast =>
    simp only [unifyDim] at h
    injection h with h_eq
    right
    rw [← h_eq]
    exact dimEq_refl _

/-- Matmul shape inference is deterministic. -/
theorem matmulShape_deterministic (l r s1 s2 : TensorShape) :
  matmulShape l r = some s1 → matmulShape l r = some s2 → s1 = s2 := by
  intro h1 h2
  have : some s1 = some s2 := by simpa [h1] using h2
  cases this
  rfl

-- ========================================================================
-- Dimension Product (for reshape)
-- ========================================================================

/-- Product of dimensions helper. -/
def dimProduct : TensorShape → Option Nat
  | [] => some 1
  | d :: ds =>
    match getDimValue d, dimProduct ds with
    | some v, some p => some (v * p)
    | _, _ => none

/-- Minimum memory for shape (in elements). -/
def minElements : TensorShape → Option Nat :=
  dimProduct

/-- Maximum memory for shape (using range upper bounds). -/
def maxElementsAux : List Dim → Option Nat
  | [] => some 1
  | d :: ds =>
    match d, maxElementsAux ds with
    | Dim.literal v, some p => some (v * p)
    | Dim.named _ _ (some hi), some p => some (hi * p)
    | _, _ => none

def maxElements : TensorShape → Option Nat := maxElementsAux

/-- Min elements ≤ max elements when both exist. -/
theorem min_le_max_elements (s : TensorShape) :
  ∀ min max, minElements s = some min → maxElements s = some max → min ≤ max := by
  intro min max h_min h_max
  unfold minElements maxElements at *
  -- Proof by induction on shape
  induction s generalizing min max with
  | nil =>
    -- Empty shape: both return some 1
    simp [dimProduct, maxElementsAux] at h_min h_max
    subst h_min h_max
    -- 1 ≤ 1
    simp
  | cons d ds ih =>
    simp only [dimProduct] at h_min
    simp only [maxElementsAux] at h_max
    -- For dimProduct to succeed, d must be a literal
    cases d <;> simp only [getDimValue] at h_min
    case literal v =>
      -- d is Dim.literal v
      -- dimProduct returns some only if getDimValue and recursive call both return some
      cases h_prod : dimProduct ds
      · -- dimProduct ds = none, contradiction
        simp [h_prod] at h_min
      · -- dimProduct ds = some minP
        rename_i minP
        simp [h_prod] at h_min
        -- h_min is now: v * minP = min
        -- Handle maxElementsAux
        cases h_max_aux : maxElementsAux ds
        · -- maxElementsAux ds = none, contradiction
          simp [h_max_aux] at h_max
        · -- maxElementsAux ds = some maxP
          rename_i maxP
          simp [h_max_aux] at h_max
          -- h_max is now: v * maxP = max
          -- min = v * minP, max = v * maxP
          rw [← h_min, ← h_max]
          -- Need to show: v * minP ≤ v * maxP
          -- This follows from IH: minP ≤ maxP
          have ih_apply := ih minP maxP h_prod h_max_aux
          exact Nat.mul_le_mul_left v ih_apply
    -- All other cases lead to contradiction (getDimValue returns none)
    all_goals { contradiction }

end TensorDimensions
