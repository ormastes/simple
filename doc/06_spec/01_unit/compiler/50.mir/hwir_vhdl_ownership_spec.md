# RISC-V Gen2 HWIR VHDL Ownership

## Purpose

This focused unit specification keeps typed Gen2 HWIR construction separate
from target-language serialization. It is a source-ownership gate, not a VHDL
simulation or qualification receipt.

## Scenarios

1. Scan each semantic Gen2 HWIR owner for VHDL grammar fragments and reject
   `library ieee`, `std_logic`, direct `entity work.` instantiation, and
   `architecture` declarations outside the backend.
2. Confirm that the strict backend emitter owns the VHDL prelude.

## Requirement traceability

- NFR-G2-004 — semantic HWIR never embeds direct VHDL.

## Evidence status

The executable source is
`test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl`. A bootstrap-seed
run is diagnostic only; a qualified self-hosted run is required for release
evidence.
