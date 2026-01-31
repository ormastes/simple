/-
  Pattern Matching Exhaustiveness Verification

  This module formalizes the pattern matching exhaustiveness checking algorithm
  for the Simple language.

  ## References

  - Maranget (2007): "Warnings for pattern matching"
  - Simple Language Specification: Pattern Matching
-/

namespace PatternExhaustiveness

/-! ## Type Definitions -/

/-- Constructor identifier -/
structure CtorId where
  name : String
  arity : Nat
  deriving DecidableEq, Repr

-- Manual BEq instance with explicit definition
instance : BEq CtorId where
  beq c1 c2 := c1.name == c2.name && c1.arity == c2.arity

-- Helper lemma for CtorId equality
theorem CtorId.beq_refl (c : CtorId) : (c == c) = true := by
  simp only [BEq.beq, Bool.and_self]
  rfl

/-- Type definition (algebraic data type) -/
structure TypeDef where
  name : String
  constructors : List CtorId
  deriving Repr

/-- Pattern AST -/
inductive Pattern where
  | wildcard : Pattern                                    -- _
  | variable : String → Pattern                           -- x
  | constructor : CtorId → List Pattern → Pattern         -- Ctor(p1, p2, ...)
  | literal : Int → Pattern                               -- 42
  | orPattern : Pattern → Pattern → Pattern               -- p1 | p2
  deriving Repr, BEq

/-- Value (for semantics) -/
inductive Value where
  | constr : CtorId → List Value → Value
  | int : Int → Value
  deriving Repr

/-! ## Coverage and Exhaustiveness -/

/-- A pattern list covers all constructors of a type -/
def coversAllConstructors (patterns : List Pattern) (typeDef : TypeDef) : Bool :=
  typeDef.constructors.all fun ctor =>
    patterns.any fun p =>
      match p with
      | Pattern.wildcard => true
      | Pattern.variable _ => true
      | Pattern.constructor pCtor _ => pCtor == ctor
      | Pattern.orPattern p1 p2 =>
          (match p1 with | Pattern.constructor c _ => c == ctor | _ => false) ||
          (match p2 with | Pattern.constructor c _ => c == ctor | _ => false)
      | _ => false

/-- Pattern is useful given previous patterns (syntactic check) -/
def syntacticallyUseful (previous : List Pattern) (p : Pattern) : Bool :=
  match p with
  | Pattern.wildcard => previous.all fun prev =>
      match prev with
      | Pattern.wildcard => false
      | Pattern.variable _ => false
      | _ => true
  | Pattern.variable _ => previous.all fun prev =>
      match prev with
      | Pattern.wildcard => false
      | Pattern.variable _ => false
      | _ => true
  | Pattern.constructor ctor _ => previous.all fun prev =>
      match prev with
      | Pattern.wildcard => false
      | Pattern.variable _ => false
      | Pattern.constructor prevCtor _ => prevCtor != ctor
      | _ => true
  | Pattern.literal n => previous.all fun prev =>
      match prev with
      | Pattern.wildcard => false
      | Pattern.variable _ => false
      | Pattern.literal m => n != m
      | _ => true
  | Pattern.orPattern p1 p2 =>
      syntacticallyUseful previous p1 || syntacticallyUseful previous p2

/-! ## Exhaustiveness Checking Algorithm -/

/-- Check if patterns are exhaustive for a type -/
def isExhaustive (patterns : List Pattern) (typeDef : TypeDef) : Bool :=
  patterns.any (fun p => p == Pattern.wildcard) ||
  patterns.any (fun p => match p with | Pattern.variable _ => true | _ => false) ||
  coversAllConstructors patterns typeDef

/-- Check if a pattern is redundant -/
def isRedundant (previous : List Pattern) (p : Pattern) : Bool :=
  !syntacticallyUseful previous p

/-! ## Key Theorems -/

/-- If wildcard is in patterns, all constructors are covered -/
theorem wildcard_covers_all (patterns : List Pattern) (typeDef : TypeDef)
    (h : Pattern.wildcard ∈ patterns) :
    coversAllConstructors patterns typeDef = true := by
  unfold coversAllConstructors
  rw [List.all_eq_true]
  intro ctor _
  rw [List.any_eq_true]
  exact ⟨Pattern.wildcard, h, rfl⟩

/-- If variable is in patterns, all constructors are covered -/
theorem variable_covers_all (patterns : List Pattern) (x : String) (typeDef : TypeDef)
    (h : Pattern.variable x ∈ patterns) :
    coversAllConstructors patterns typeDef = true := by
  unfold coversAllConstructors
  rw [List.all_eq_true]
  intro ctor _
  rw [List.any_eq_true]
  exact ⟨Pattern.variable x, h, rfl⟩

/-- Wildcard after wildcard is redundant -/
theorem wildcard_redundant_after_wildcard (patterns : List Pattern)
    (h : Pattern.wildcard ∈ patterns) :
    syntacticallyUseful patterns Pattern.wildcard = false := by
  unfold syntacticallyUseful
  rw [List.all_eq_false]
  exact ⟨Pattern.wildcard, h, by native_decide⟩

/-- Wildcard after variable is redundant -/
theorem wildcard_redundant_after_variable (patterns : List Pattern) (x : String)
    (h : Pattern.variable x ∈ patterns) :
    syntacticallyUseful patterns Pattern.wildcard = false := by
  unfold syntacticallyUseful
  rw [List.all_eq_false]
  refine ⟨Pattern.variable x, h, ?_⟩
  intro h_eq
  cases h_eq

/-- Same constructor twice is redundant -/
theorem constructor_redundant (patterns : List Pattern) (ctor : CtorId) (pats1 pats2 : List Pattern)
    (h : Pattern.constructor ctor pats1 ∈ patterns) :
    syntacticallyUseful patterns (Pattern.constructor ctor pats2) = false := by
  unfold syntacticallyUseful
  rw [List.all_eq_false]
  refine ⟨Pattern.constructor ctor pats1, h, ?_⟩
  -- The match reduces to (ctor != ctor) which is false, so ¬false=true is trivial
  simp only [bne, Bool.not_eq_true']
  intro h_eq
  have h_true : (ctor == ctor) = true := CtorId.beq_refl ctor
  rw [h_true] at h_eq
  cases h_eq

/-- Same literal twice is redundant -/
theorem literal_redundant (patterns : List Pattern) (n : Int)
    (h : Pattern.literal n ∈ patterns) :
    syntacticallyUseful patterns (Pattern.literal n) = false := by
  unfold syntacticallyUseful
  rw [List.all_eq_false]
  refine ⟨Pattern.literal n, h, ?_⟩
  -- The match reduces to (n != n) which is false, so ¬false=true is trivial
  simp only [bne, Bool.not_eq_true']
  intro h_eq
  have h_true : (n == n) = true := beq_self_eq_true n
  rw [h_true] at h_eq
  cases h_eq

/-- Exhaustive check: wildcard implies exhaustive -/
theorem wildcard_implies_exhaustive (patterns : List Pattern) (typeDef : TypeDef)
    (h : Pattern.wildcard ∈ patterns) :
    isExhaustive patterns typeDef = true := by
  unfold isExhaustive
  simp only [Bool.or_eq_true, List.any_eq_true]
  left; left
  exact ⟨Pattern.wildcard, h, by native_decide⟩

/-- Variable implies exhaustive -/
theorem variable_implies_exhaustive (patterns : List Pattern) (x : String) (typeDef : TypeDef)
    (h : Pattern.variable x ∈ patterns) :
    isExhaustive patterns typeDef = true := by
  unfold isExhaustive
  simp only [Bool.or_eq_true, List.any_eq_true]
  left; right
  refine ⟨Pattern.variable x, h, ?_⟩
  rfl

/-- Redundancy is conservative: if syntactically not useful, it's redundant -/
theorem redundant_if_not_useful (previous : List Pattern) (p : Pattern)
    (h : syntacticallyUseful previous p = false) :
    isRedundant previous p = true := by
  unfold isRedundant
  simp [h]

/-! ## Examples -/

-- Example: Option type
def optionType : TypeDef := {
  name := "Option"
  constructors := [
    { name := "Some", arity := 1 },
    { name := "None", arity := 0 }
  ]
}

-- Wildcard is exhaustive
example : isExhaustive [Pattern.wildcard] optionType = true := by native_decide

-- Some and None patterns are exhaustive
example : isExhaustive [
    Pattern.constructor { name := "Some", arity := 1 } [Pattern.wildcard],
    Pattern.constructor { name := "None", arity := 0 } []
  ] optionType = true := by native_decide

-- Just Some is not exhaustive (missing None)
example : isExhaustive [
    Pattern.constructor { name := "Some", arity := 1 } [Pattern.wildcard]
  ] optionType = false := by native_decide

-- Same constructor twice is redundant
example : isRedundant [
    Pattern.constructor { name := "Some", arity := 1 } [Pattern.wildcard]
  ] (Pattern.constructor { name := "Some", arity := 1 } [Pattern.variable "x"]) = true := by
  native_decide

end PatternExhaustiveness
