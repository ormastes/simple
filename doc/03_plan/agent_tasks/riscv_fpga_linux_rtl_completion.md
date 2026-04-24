# RISC-V FPGA Linux RTL Completion Agent Tasks

## Current Trace State

- REQ-RFL-001 through REQ-RFL-009 remain covered by the existing hardware feature specs for board profiles, lane defaults, prepare manifests, generated Simple source, VHDL source maps, and RTL manifests.
- REQ-RFL-010 is satisfied for the implemented helper set: generated RISC-V hardware source now parses and lowers through the real frontend -> HIR -> MIR path, and regressions prove typed bitfield reads plus writeback/branch/store/I-type/upper/execute-control/jump recomposition through dedicated helpers.
- REQ-RFL-010 also has a usable compiler trace surface through the expanded MIR JSON export: module functions, blocks, instruction payloads, and terminators.
- REQ-RFL-011 is satisfied for the same helper set because VHDL slice emission is now proven against exact helper guards, concat shapes, and source-map entries rather than inferred from partial substrings.

## Active Gate

The stale frontend/semantic blocker is cleared and this helper-proof milestone is complete. Generated-source-backed decode coverage now includes writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, and jump immediate helpers, and the backend proof is exact rather than inferred from partial substrings.

## Next Bounded Tasks

1. Preserve the exact helper contract when future decode helpers are added; new helper paths should follow the same overlay-bitfield plus field-write pattern.
2. Keep MIR and backend regressions exact for any additional immediate/decode families so the proof surface stays slice-based and source-mapped.
3. Continue the handwritten-core migration without reintroducing raw `imem_rdata` reconstruction when a generated helper contract already exists.
