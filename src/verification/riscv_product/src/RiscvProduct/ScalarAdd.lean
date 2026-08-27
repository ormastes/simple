/-!
# Bounded RV32 ADD retirement semantics

This module proves the first generated scalar instruction-family contract.  It
does not promote the generated Linux core: `RiscvProduct.Generated` continues
to report that product as placeholder-rejected until RTL/RVFI/SBY and netlist
evidence close the remaining chain.
-/

namespace RiscvProduct.ScalarAdd

structure Input where
  valid : Bool
  order : BitVec 64
  privilege : BitVec 2
  instruction : BitVec 32
  pc : BitVec 32
  rs1Value : BitVec 32
  rs2Value : BitVec 32
  rd : BitVec 5

structure Retirement where
  valid : Bool
  order : BitVec 64
  instruction : BitVec 32
  trap : Bool
  interrupt : Bool
  privilege : BitVec 2
  pcBefore : BitVec 32
  pcAfter : BitVec 32
  rd : BitVec 5
  rdWrite : Bool
  rdValue : BitVec 32

/-- Exact RV32 wrapping ADD projection before the one-entry retirement owner. -/
def project (input : Input) : Retirement :=
  if input.valid then
    { valid := true
      order := input.order
      instruction := input.instruction
      trap := false
      interrupt := false
      privilege := input.privilege
      pcBefore := input.pc
      pcAfter := input.pc + 4
      rd := input.rd
      rdWrite := input.rd != 0
      rdValue := if input.rd = 0 then 0 else input.rs1Value + input.rs2Value }
  else
    { valid := false, order := 0, instruction := 0, trap := false,
      interrupt := false, privilege := 0, pcBefore := 0, pcAfter := 0,
      rd := 0, rdWrite := false, rdValue := 0 }

theorem valid_add_wraps_exactly (input : Input) (h : input.valid = true) :
    (project input).rdValue =
      if input.rd = 0 then 0 else input.rs1Value + input.rs2Value := by
  simp [project, h]

theorem valid_add_advances_pc_by_four (input : Input) (h : input.valid = true) :
    (project input).pcAfter = input.pc + 4 := by
  simp [project, h]

theorem x0_write_is_suppressed (input : Input)
    (hvalid : input.valid = true) (hzero : input.rd = 0) :
    (project input).rdWrite = false ∧ (project input).rdValue = 0 := by
  simp [project, hvalid, hzero]

theorem inactive_projection_is_not_a_retirement (input : Input)
    (h : input.valid = false) : (project input).valid = false := by
  simp [project, h]

def reachableWitness : Input :=
  { valid := true, order := 0, privilege := 3, instruction := 0x002081b3,
    pc := 0x1000, rs1Value := 1, rs2Value := 2, rd := 3 }

theorem add_retirement_is_reachable : (project reachableWitness).valid = true := by
  decide

/-- Deliberately wrong implementation used to prove the witness is sensitive. -/
def subtractMutant (input : Input) : BitVec 32 := input.rs1Value - input.rs2Value

theorem add_mutation_is_detected :
    (project reachableWitness).rdValue ≠ subtractMutant reachableWitness := by
  decide

#print axioms valid_add_wraps_exactly
#print axioms valid_add_advances_pc_by_four
#print axioms x0_write_is_suppressed
#print axioms inactive_projection_is_not_a_retirement
#print axioms add_retirement_is_reachable
#print axioms add_mutation_is_detected

end RiscvProduct.ScalarAdd
