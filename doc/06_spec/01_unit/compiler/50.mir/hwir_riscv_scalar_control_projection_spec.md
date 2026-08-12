# Shared Scalar Branch and Jump Projection

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_riscv_scalar_control_projection_spec.spl`

## Purpose and scope

This focused source-level unit specification evaluates the strict, stateless
base-I branch/JAL/JALR HWIR projection for concrete RV32 and RV64 products. It
checks branch predicates, register-index binding, XLEN-wrapped target
calculation, JALR bit-zero clearing, product-selected instruction alignment,
normalized retirement payloads, deterministic graph identity, and typed VHDL
projection text.

The projection admits only base-I conditional branches, JAL, and JALR. It is
not a general scalar executor or a compressed-instruction decoder; compressed
configuration is exercised only to establish the product's IALIGN choice for
the same base-I control instruction.

## Scenarios

1. Evaluate equal, signed, and unsigned branch conditions and wrapped targets
   for RV32 and RV64.
2. Clear JALR bit zero, reject mismatched encoded register bindings, and
   normalize the invalid retirement payload.
3. Check IALIGN32 target exceptions and IALIGN16 admission for direct jumps,
   taken and non-taken branches, and post-bit-clear JALR targets.
4. Exercise boundary branch/JAL/JALR immediates, RV32 wrapping, and RV64
   signed-extreme comparisons.
5. Emit the admitted branch/JAL/JALR rows as typed, concrete-width strict
   VHDL without an XLEN runtime selector.
6. Rebuild an identical product for a stable structural hash, distinguish the
   RV64 graph, and count normalized invalid retirement selects.

## Requirement traceability

- REQ-G2-002 — concrete RV32/RV64 configuration, including the selected
  compressed-decode profile that fixes IALIGN, is elaborated before projection.
- REQ-G2-003 — the bounded projection admits only explicit base-I control-flow
  rows and rejects invalid register binding rather than creating a valid
  retirement result.
- REQ-G2-004 — admitted concrete rows emit deterministic, non-empty typed VHDL
  with selected 32- or 64-bit ports.
- NFR-G2-001..003 — repeated graphs have stable identity; invalid inputs are
  normalized; and generated products have no runtime XLEN branch.

## Evidence boundary

This is host-evaluated HWIR and VHDL-text evidence for a bounded,
combinational control projection. It does not execute a scalar pipeline,
decode or prove compressed instructions, own branch prediction or fetch,
maintain architectural register/memory state, run GHDL/Sail/riscv-formal/SBY,
synthesize RTL, or establish full RISC-V control-flow correctness.
