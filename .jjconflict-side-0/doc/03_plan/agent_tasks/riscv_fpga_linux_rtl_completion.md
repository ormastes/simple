# RISC-V FPGA Linux RTL Completion Agent Tasks

> Status: COMPLETE — spipe 16/16 done

## Baseline Tasks (from riscv_fpga_linux.md, merged)

1. Keep the preparation contract and executable lane validation green without restating this file as the canonical Linux platform source.
2. Preserve the completed helper-proof surface: writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, execute datapath, branch datapath, control-flow datapath, memory access control, and jump immediate.
3. Keep both generated RV32 and RV64 Linux lanes authoritative in manifests, smoke scripts, and board wrappers.
4. Extend DTB and boot ROM packaging as generated Linux boot artifacts consumed by the authoritative board products.
5. Add Vivado materialization for concrete Xilinx board profiles, starting with MLK-S02-100T.
6. Add and maintain hardware boot-test runners for generated board products once FPGA access is available.
7. Continue fixing Simple compiler VHDL/codegen gaps discovered by the RTL generator, with explicit exact-shape tests for each new helper family.

## Current Trace State

- REQ-RFL-001 through REQ-RFL-009 remain covered by the existing hardware feature specs for board profiles, lane defaults, prepare manifests, generated Simple source, VHDL source maps, and RTL manifests.
- REQ-RFL-010 is satisfied for the implemented helper set: generated RISC-V hardware source now parses and lowers through the real frontend -> HIR -> MIR path, and regressions prove typed bitfield reads plus writeback/branch/store/I-type/upper/execute-control/execute-datapath/branch-datapath/control-flow-datapath/memory-access/jump/dispatch/trap-halt recomposition through dedicated helpers.
- REQ-RFL-010 also has a usable compiler trace surface through the expanded MIR JSON export: module functions, blocks, instruction payloads, and terminators.
- REQ-RFL-011 is satisfied for the same helper set because VHDL slice emission is now proven against exact helper guards, concat shapes, and source-map entries rather than inferred from partial substrings.

## Active Gate

The stale frontend/semantic blocker is cleared and this helper-proof milestone is complete. Generated-source-backed decode coverage now includes writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, execute datapath, branch datapath, control-flow datapath, memory access control, jump immediate, dispatch class, and trap/halt helpers, and the backend proof is exact rather than inferred from partial substrings.

## Next Bounded Tasks

1. Preserve the exact helper contract when future decode helpers are added; new helper paths should follow the same overlay-bitfield plus field-write pattern.
2. Extend the helper-driven shell cleanup from bounded dispatch/trap orchestration into the remaining handwritten decode/update islands without reintroducing raw `imem_rdata` reconstruction when a generated helper contract already exists.
3. Sequence the next milestone around CSR/privilege/MMU/interrupt/full-trap completion, DTB plus firmware handoff, OpenSBI/U-Boot/Linux boot validation, and final ownership handoff to the canonical RV64 Linux RTL lane.
