# RISC-V Gen2 declarative scalar decoder

Status: development evidence; qualification requires an admitted full
self-hosted compiler and the generated-decoder GHDL gate.

## Scenario: concrete decoder generation

1. Freeze RV32I and RV64I+Zicsr+Zifencei plans from the shared ISA database.
2. Lower each exact plan to fixed-XLEN strict HWIR.
3. Require valid deterministic graphs with different concrete hashes and no
   runtime XLEN/profile input.
4. Require every legal row to carry a nonzero stable semantic opcode and an
   explicit operand-width mode; row order remains provenance rather than
   execution semantics.

## Scenario: fail-closed illegal input

1. Evaluate the exact RV32 HWIR graph with the all-zero instruction.
2. Require legality, row identity, and canonical instruction all to be zero.

## Scenario: strict VHDL

1. Compile the RV64 decoder through the compiler-owned strict product route.
2. Require nonempty deterministic VHDL, the
   `hwir-gen2-scalar-decoder-v1` route, 64-character graph-hash lineage, and
   no legacy fallback.

## Scenario: runtime decoded-uop handoff

1. Bind the exact concrete decoder graph and decoder-plan hash to the frozen
   decoded-uop interface.
2. Build one registered decoded-uop skid for semantic opcode, instruction identity,
   register indices and values, PC, privilege, and event lineage.
3. Require conservative ready/valid behavior: capture only while empty and
   hold the complete payload until downstream acceptance.

The behavioral GHDL gate is
`test/02_integration/compiler/riscv_scalar_decoder_ghdl_spec.spl`. It analyzes,
elaborates, and simulates legal and illegal RV32/RV64 vectors; execution remains
pending an admitted full CLI.

Traceability: REQ-G2-001, REQ-G2-003, REQ-G2-004, NFR-G2-001,
NFR-G2-002, NFR-G2-003, NFR-G2-004.
