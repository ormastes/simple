/-
  ContractsTest.lean - Tests for contract verification model
-/

import Contracts

open Contracts

/-! ## Test Cases -/

-- Test 1: Empty contract passes
#eval do
  let contract : FunctionContract := {
    preconditions := [],
    invariants := [],
    postconditions := [],
    errorPostconditions := []
  }
  let env : Env := []
  let (result, _) := checkEntry env contract
  IO.println s!"Empty contract: {repr result}"

-- Test 2: Simple precondition (b != 0)
#eval do
  let contract : FunctionContract := {
    preconditions := [{
      condition := ContractExpr.binOp "!=" (ContractExpr.var "b") (ContractExpr.val (Val.int 0))
    }],
    invariants := [],
    postconditions := [],
    errorPostconditions := []
  }
  -- Test with b = 5 (should pass)
  let env1 : Env := [("b", Val.int 5)]
  let (result1, _) := checkEntry env1 contract
  IO.println s!"Precondition b=5: {repr result1}"

  -- Test with b = 0 (should fail)
  let env2 : Env := [("b", Val.int 0)]
  let (result2, _) := checkEntry env2 contract
  IO.println s!"Precondition b=0: {repr result2}"

-- Test 3: Postcondition check
#eval do
  let contract : FunctionContract := {
    preconditions := [],
    invariants := [],
    postconditions := [{
      condition := ContractExpr.binOp ">" ContractExpr.ret (ContractExpr.val (Val.int 0))
    }],
    errorPostconditions := []
  }
  let st : ContractState := {
    env := [],
    oldSnapshots := [],
    returnValue := none,
    errorValue := none
  }
  -- Test with ret = 5 (should pass)
  let result1 := checkSuccessExit st (Val.int 5) contract
  IO.println s!"Postcondition ret=5: {repr result1}"

  -- Test with ret = -1 (should fail)
  let result2 := checkSuccessExit st (Val.int (-1)) contract
  IO.println s!"Postcondition ret=-1: {repr result2}"

-- Test 4: old() snapshot test
#eval do
  let contract : FunctionContract := {
    preconditions := [],
    invariants := [],
    postconditions := [{
      condition := ContractExpr.binOp "=="
        ContractExpr.ret
        (ContractExpr.old (ContractExpr.var "x"))
    }],
    errorPostconditions := []
  }
  let env : Env := [("x", Val.int 10)]
  let (_, st) := checkEntry env contract
  IO.println s!"Snapshots: {repr st.oldSnapshots}"

  -- Return value equals old(x)
  let result1 := checkSuccessExit st (Val.int 10) contract
  IO.println s!"old(x)=10, ret=10: {repr result1}"

  -- Return value doesn't equal old(x)
  let result2 := checkSuccessExit st (Val.int 5) contract
  IO.println s!"old(x)=10, ret=5: {repr result2}"

-- Test 5: Refinement type checks
#eval do
  IO.println s!"posI64(5): {checkRefinement (Val.int 5) posI64}"
  IO.println s!"posI64(0): {checkRefinement (Val.int 0) posI64}"
  IO.println s!"posI64(-1): {checkRefinement (Val.int (-1)) posI64}"
  IO.println s!"nonZero(5): {checkRefinement (Val.int 5) nonZero}"
  IO.println s!"nonZero(0): {checkRefinement (Val.int 0) nonZero}"

-- Test 6: Invariant at entry and exit
#eval do
  let contract : FunctionContract := {
    preconditions := [],
    invariants := [{
      condition := ContractExpr.binOp ">=" (ContractExpr.var "balance") (ContractExpr.val (Val.int 0))
    }],
    postconditions := [],
    errorPostconditions := []
  }
  -- Test with balance = 100 (should pass)
  let env1 : Env := [("balance", Val.int 100)]
  let (result1, st1) := checkEntry env1 contract
  IO.println s!"Invariant entry balance=100: {repr result1}"

  let exitResult1 := checkSuccessExit st1 (Val.int 50) contract
  IO.println s!"Invariant exit balance=100: {repr exitResult1}"

  -- Test with balance = -10 (should fail at entry)
  let env2 : Env := [("balance", Val.int (-10))]
  let (result2, _) := checkEntry env2 contract
  IO.println s!"Invariant entry balance=-10: {repr result2}"

-- Test 7: Error postcondition
#eval do
  let contract : FunctionContract := {
    preconditions := [],
    invariants := [],
    postconditions := [],
    errorPostconditions := [{
      condition := ContractExpr.binOp "!="
        (ContractExpr.field ContractExpr.err "msg")
        (ContractExpr.val (Val.str ""))
    }]
  }
  let st : ContractState := {
    env := [],
    oldSnapshots := [],
    returnValue := none,
    errorValue := none
  }
  -- Would need field access implementation for full test
  IO.println "Error postcondition structure created"

-- Test 8: Complex precondition with logical operators
#eval do
  let contract : FunctionContract := {
    preconditions := [{
      condition := ContractExpr.binOp "&&"
        (ContractExpr.binOp ">=" (ContractExpr.var "a") (ContractExpr.val (Val.int 0)))
        (ContractExpr.binOp ">" (ContractExpr.var "b") (ContractExpr.val (Val.int 0)))
    }],
    invariants := [],
    postconditions := [],
    errorPostconditions := []
  }
  -- a=5, b=3 (should pass)
  let env1 : Env := [("a", Val.int 5), ("b", Val.int 3)]
  let (result1, _) := checkEntry env1 contract
  IO.println s!"a>=0 && b>0 with a=5,b=3: {repr result1}"

  -- a=5, b=0 (should fail)
  let env2 : Env := [("a", Val.int 5), ("b", Val.int 0)]
  let (result2, _) := checkEntry env2 contract
  IO.println s!"a>=0 && b>0 with a=5,b=0: {repr result2}"

  -- a=-1, b=3 (should fail)
  let env3 : Env := [("a", Val.int (-1)), ("b", Val.int 3)]
  let (result3, _) := checkEntry env3 contract
  IO.println s!"a>=0 && b>0 with a=-1,b=3: {repr result3}"

/-! ## Verification Examples -/

-- Verify empty contract theorem
example : let contract : FunctionContract := {
    preconditions := [],
    invariants := [],
    postconditions := [],
    errorPostconditions := []
  }
  (checkEntry [] contract).1 = CheckResult.ok := by
  simp [checkEntry, checkPreconditions, checkInvariantsEntry, evalClauses]

-- Verify precondition determinism
example (st : ContractState) (contract : FunctionContract) :
    checkPreconditions st contract = checkPreconditions st contract := rfl
