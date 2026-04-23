# RISC-V FPGA Linux RTL Completion Agent Tasks

## Current Trace State

- REQ-RFL-001 through REQ-RFL-009 remain covered by the existing hardware feature specs for board profiles, lane defaults, prepare manifests, generated Simple source, VHDL source maps, and RTL manifests.
- REQ-RFL-010 is planned and now has a compiler trace surface through the expanded MIR JSON export: module functions, blocks, instruction payloads, and terminators.
- REQ-RFL-011 remains downstream of REQ-RFL-010 because VHDL slice emission should consume typed MIR bitfield facts rather than re-parse generated Simple hardware source.

## Active Blocker

Frontend and semantic analysis must accept `bitfield` declarations and field reads from generated RISC-V hardware source, then preserve typed field metadata into HIR/MIR. Until that path exists, MIR lowering can only be validated on constructed or partial inputs, and REQ-RFL-010 should stay marked blocked/planned rather than full.

## Next Bounded Tasks

1. Add or update frontend/semantic specs for `bitfield RiscvInstruction(u32)` declarations, constructor calls, and reads such as `inst.opcode`, `inst.rd`, `inst.funct3`, `inst.rs1`, `inst.rs2`, and `inst.funct7`.
2. Extend MIR specs to assert bounded extraction metadata for those fields through the expanded MIR JSON export surface.
3. After REQ-RFL-010 is green, add VHDL backend specs for deterministic `downto` slices and source-map entries, then advance REQ-RFL-011.
