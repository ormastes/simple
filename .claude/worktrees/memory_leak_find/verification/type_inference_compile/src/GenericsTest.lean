/-
  GenericsTest.lean - Tests for generic type inference model
-/

import Generics

open Generics

/-! ## Test Cases -/

-- Test 1: Simple identity function should be polymorphic
#eval do
  let st : FreshState := { next := 0 }
  -- λx. x : ∀α. α → α
  let idExpr := Expr.lam "x" (Expr.var "x")
  match infer [] idExpr st with
  | InferResult.ok ty _ _ => IO.println s!"identity type: {repr ty}"
  | InferResult.error msg => IO.println s!"Error: {msg}"

-- Test 2: Let-polymorphism
#eval do
  let st : FreshState := { next := 0 }
  -- let id = λx. x in (id 42)
  let expr := Expr.letIn "id" (Expr.lam "x" (Expr.var "x"))
    (Expr.app (Expr.var "id") (Expr.litNat 42))
  match infer [] expr st with
  | InferResult.ok ty _ _ => IO.println s!"let-poly result: {repr ty}"
  | InferResult.error msg => IO.println s!"Error: {msg}"

-- Test 3: Occurs check should catch infinite types
#eval do
  let st : FreshState := { next := 0 }
  -- λx. x x  -- Should fail occurs check
  let omega := Expr.lam "x" (Expr.app (Expr.var "x") (Expr.var "x"))
  match infer [] omega st with
  | InferResult.ok ty _ _ => IO.println s!"omega type (unexpected): {repr ty}"
  | InferResult.error msg => IO.println s!"Correctly rejected: {msg}"

-- Test 4: Basic unification with generics
#eval do
  -- Unify List[α] with List[Nat]
  let t1 := Ty.generic1 "List" (Ty.var 0)
  let t2 := Ty.generic1 "List" Ty.nat
  match unify t1 t2 with
  | UnifyResult.ok s =>
    IO.println s!"Unified List! subst={repr s}"
  | UnifyResult.mismatch _ _ => IO.println "Mismatch"
  | UnifyResult.occursCheckFail v t => IO.println s!"Occurs: {v} in {repr t}"

-- Test 5: Unification with Map[K,V]
#eval do
  -- Unify Map[α, β] with Map[Str, Nat]
  let t1 := Ty.generic2 "Map" (Ty.var 0) (Ty.var 1)
  let t2 := Ty.generic2 "Map" Ty.str Ty.nat
  match unify t1 t2 with
  | UnifyResult.ok s =>
    IO.println s!"Unified Map! subst={repr s}"
  | UnifyResult.mismatch _ _ => IO.println "Mismatch"
  | UnifyResult.occursCheckFail v t => IO.println s!"Occurs: {v} in {repr t}"

-- Test 6: Generic type mismatch (List vs Option)
#eval do
  let t1 := Ty.generic1 "List" Ty.nat
  let t2 := Ty.generic1 "Option" Ty.nat
  match unify t1 t2 with
  | UnifyResult.ok _ => IO.println "Unified (unexpected)"
  | UnifyResult.mismatch _ _ => IO.println "Correctly rejected: List ≠ Option"
  | UnifyResult.occursCheckFail _ _ => IO.println "Occurs check"

-- Test 7: Create Option[T] expression
#eval do
  let st : FreshState := { next := 0 }
  -- Some(42) : Option[Nat]
  let expr := Expr.mkGeneric1 "Option" (Expr.litNat 42)
  match infer [] expr st with
  | InferResult.ok ty _ _ => IO.println s!"Some(42) type: {repr ty}"
  | InferResult.error msg => IO.println s!"Error: {msg}"

-- Test 8: Create Map[K,V] expression
#eval do
  let st : FreshState := { next := 0 }
  -- Pair("key", 42) : Map[Str, Nat] (conceptually)
  let expr := Expr.mkGeneric2 "Pair" (Expr.litStr "key") (Expr.litNat 42)
  match infer [] expr st with
  | InferResult.ok ty _ _ => IO.println s!"Pair type: {repr ty}"
  | InferResult.error msg => IO.println s!"Error: {msg}"

-- Test 9: Nested generics - Option[List[Nat]]
#eval do
  let st : FreshState := { next := 0 }
  -- Some(List.cons(42))
  let inner := Expr.mkGeneric1 "List" (Expr.litNat 42)
  let expr := Expr.mkGeneric1 "Option" inner
  match infer [] expr st with
  | InferResult.ok ty _ _ => IO.println s!"Option[List[Nat]]: {repr ty}"
  | InferResult.error msg => IO.println s!"Error: {msg}"

-- Test 10: If-then-else with generic return type
#eval do
  let st : FreshState := { next := 0 }
  -- if true then Some(42) else Some(0)
  let expr := Expr.ifElse
    (Expr.litBool true)
    (Expr.mkGeneric1 "Option" (Expr.litNat 42))
    (Expr.mkGeneric1 "Option" (Expr.litNat 0))
  match infer [] expr st with
  | InferResult.ok ty _ _ => IO.println s!"if-then-else Option: {repr ty}"
  | InferResult.error msg => IO.println s!"Error: {msg}"

-- Test 11: Let-poly with generics
#eval do
  let st : FreshState := { next := 0 }
  -- let wrap = λx. Some(x) in (wrap 42, wrap true)
  -- This tests that `wrap` gets polymorphic type ∀α. α → Option[α]
  let wrap := Expr.lam "x" (Expr.mkGeneric1 "Option" (Expr.var "x"))
  let expr := Expr.letIn "wrap" wrap
    (Expr.app (Expr.var "wrap") (Expr.litNat 42))
  match infer [] expr st with
  | InferResult.ok ty _ _ => IO.println s!"let wrap result: {repr ty}"
  | InferResult.error msg => IO.println s!"Error: {msg}"

-- Test 12: Free variables in generic types
#eval do
  let ty := Ty.generic2 "Map" (Ty.var 0) (Ty.generic1 "List" (Ty.var 1))
  IO.println s!"Free vars in Map[α, List[β]]: {freeVars ty}"

-- Test 13: Generalization with generics
#eval do
  let ty := Ty.generic1 "Option" (Ty.var 0)
  let sch := generalize [] ty
  IO.println s!"Generalized Option[α]: ∀{sch.vars}. {repr sch.ty}"

/-! ## Verification that key properties hold -/

-- Verify substitution on generic1
example : applySubst (singleSubst 0 Ty.nat) (Ty.generic1 "List" (Ty.var 0))
        = Ty.generic1 "List" Ty.nat := by
  simp [applySubst, singleSubst, substLookup]

-- Verify substitution on generic2
example : applySubst (singleSubst 0 Ty.str) (Ty.generic2 "Map" (Ty.var 0) Ty.nat)
        = Ty.generic2 "Map" Ty.str Ty.nat := by
  simp [applySubst, singleSubst, substLookup]

-- Verify occurs check in generic1
example : occurs 0 (Ty.generic1 "List" (Ty.var 0)) = true := rfl
example : occurs 1 (Ty.generic1 "List" (Ty.var 0)) = false := rfl

-- Verify occurs check in generic2
example : occurs 0 (Ty.generic2 "Map" (Ty.var 0) Ty.nat) = true := rfl
example : occurs 1 (Ty.generic2 "Map" (Ty.var 0) (Ty.var 1)) = true := rfl
example : occurs 2 (Ty.generic2 "Map" (Ty.var 0) (Ty.var 1)) = false := rfl

-- Verify empty subst identity on generics
example : applySubst emptySubst (Ty.generic1 "Option" Ty.nat) = Ty.generic1 "Option" Ty.nat := by
  simp [applySubst, emptySubst]

example : applySubst emptySubst (Ty.generic2 "Map" Ty.str Ty.nat) = Ty.generic2 "Map" Ty.str Ty.nat := by
  simp [applySubst, emptySubst]
