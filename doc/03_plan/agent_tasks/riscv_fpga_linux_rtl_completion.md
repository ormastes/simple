# RISC-V FPGA Linux RTL Completion Agent Tasks

## Current Trace State

- REQ-RFL-001 through REQ-RFL-009 remain covered by the existing hardware feature specs for board profiles, lane defaults, prepare manifests, generated Simple source, VHDL source maps, and RTL manifests.
- REQ-RFL-010 is partially satisfied: generated RISC-V hardware source now parses and lowers through the real frontend -> HIR -> MIR path, and the current regressions already prove typed bitfield reads plus `rd` writeback recomposition for bounded helper cases.
- REQ-RFL-010 also has a usable compiler trace surface through the expanded MIR JSON export: module functions, blocks, instruction payloads, and terminators.
- REQ-RFL-011 remains downstream because VHDL slice emission should consume typed MIR bitfield facts rather than re-parse generated Simple hardware source, and because the backend proof still needs exact guard/source-map coverage on the generated helper paths.

## Active Gate

The stale frontend/semantic blocker is cleared. The remaining gate is broader generated-source-backed decode coverage, including at least one immediate reconstruction path, plus exact VHDL/source-map assertions for the generated helper cases. REQ-RFL-010 should stay partial until that wider decode/immediate coverage exists, and REQ-RFL-011 should stay planned until the backend proof is exact rather than inferred from partial substrings.

## Next Bounded Tasks

1. Extend the generated helper coverage with one immediate reconstruction case so REQ-RFL-010 advances beyond the current opcode/rd/funct3/rs1/rs2/funct7 writeback-focused helpers.
2. Tighten MIR and generated-source regressions to keep asserting bounded extraction metadata for those fields through the expanded MIR JSON export surface.
3. Add exact VHDL backend assertions for guard structure, slice usage, concat/update expressions, and source-map entries for the generated helper paths, then advance REQ-RFL-011.
