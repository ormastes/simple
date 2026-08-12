# RISC-V Gen2 Strict HWIR Foundation

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_foundation_spec.spl`

## Purpose and scope

This focused source-level unit specification validates the typed Gen2 HWIR
foundation: stable graph/origin identity, concrete RV32/RV64 and compressed
profiles, strict lowering and VHDL-emission boundaries, selected compressed
semantic rows, and bounded sequential-plan validation.

## Scenarios

1. Construct and hash typed graphs, origins, concrete ports, and fixed-width
   constants without text-valued HWIR operands.
2. Validate concrete configuration, selected critical targets, and closed
   compressed capability profiles.
3. Reject invalid inputs, unsafe names, malformed modules, unsupported strict
   shapes, and serializer-invalid declarations without a legacy fallback.
4. Render selected typed and sequential HWIR products, including the bounded
   compressed semantic-row catalog and retirement-composition receipt guard.

## Requirement traceability

- REQ-G2-001 — typed HWIR module, node, origin, and structural contracts.
- REQ-G2-002 — concrete RV32/RV64 and compressed-profile elaboration.
- REQ-G2-003 — strict lowering rejects unsupported hardware input without
  legacy fallback.
- REQ-G2-004 — strict typed HWIR emission validates identifiers and renders
  deterministic VHDL.
- REQ-G2-007 — bounded compressed semantic-row construction is explicit.
- REQ-G2-010 — bounded typed sequential frontend-plan ownership and validation.

## Evidence boundary

This is source-level construction, validation, and emitted-text evidence. It
does not execute a full ISA/pipeline, prove complete compressed semantics,
provide an architectural retirement producer, run GHDL/Sail/riscv-formal/SBY,
perform synthesis or equivalence, or qualify a generated or deployed hardware
artifact.
