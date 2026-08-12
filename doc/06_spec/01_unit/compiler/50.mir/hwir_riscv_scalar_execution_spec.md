# Bounded Scalar ALU Retirement Projection

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_riscv_scalar_execution_spec.spl`

## Purpose and scope

This focused source-level unit specification builds the bounded base-I
ADD/SUB/AND/OR/XOR retirement-projection HWIR slice and checks its concrete
RV32/RV64 shape, deterministic structure, strict VHDL text, and fail-closed
instruction admission.

## Scenarios

1. Build each admitted base-I ALU row for concrete RV32 and RV64 products.
2. Compile concrete-width strict VHDL and inspect exact projected retirement
   outputs.
3. Reject a load instruction outside the bounded ALU slice.
4. Check invalid/x0 normalization and repeatable structural hashes.

## Requirement traceability

- REQ-G2-003 — the bounded projection rejects unsupported instructions rather
  than using a fallback route.
- REQ-G2-004 — admitted typed modules render deterministic, non-empty strict
  VHDL with concrete selected widths.

## Evidence boundary

This is source-level HWIR and VHDL-text evidence for a bounded combinational
projection. It does not execute an architectural scalar core, own retirement
state, prove ISA equivalence, run GHDL/Sail/riscv-formal/SBY, synthesize RTL,
or support an unqualified hardware-correctness claim.
