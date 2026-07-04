import Contracts

/-!
# ContractsConstraints — hand-written constraints and proofs for `Contracts`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `Contracts` live here; the generated model lives in
`Contracts.lean` and may be replaced wholesale by regeneration.
-/

namespace Contracts

def emptyContract : FunctionContract :=
  { preconditions := []
  , invariants := []
  , postconditions := []
  , errorPostconditions := [] }

theorem empty_contract_has_no_clauses :
  emptyContract.preconditions = [] ∧
  emptyContract.invariants = [] ∧
  emptyContract.postconditions = [] ∧
  emptyContract.errorPostconditions = [] := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl


end Contracts
