# RISC-V FPGA Linux System Test Plan

Historical helper-proof scope:

- Unit: board profiles validate prepare-only versus hardware-boot requirements.
- Unit: RV64 exposes the authoritative contract lane and RV32 remains compiler-parity only.
- Unit: Linux boot validation fails until readiness and required artifacts are configured.
- Unit: MIR lowering exposes a bounded bitfield extraction hook for RISC-V instruction decode fields before any VHDL text is emitted.
- Integration: Vivado TCL plan generation is deterministic for `xilinx_generic`.
- Integration: generated Simple hardware source preserves `@hardware`, `@clocked`, instruction bitfields, opcode width, and decode source traces for the implemented helper set.
- Integration: generated VHDL includes source-map comments, typed slice emission for decoded instruction fields, and helper-aligned manifest records for the bounded lane artifacts.
- Regression: existing VHDL backend E2E and targeted RISC-V hardware/compiler specs remain green.
- Hardware: future FPGA runs should validate only the canonical RV64 lane unless RV32 later graduates from parity-only status.

## Traceability

| REQ | Executable Spec | Coverage |
|-----|-----------------|----------|
| REQ-RFL-001..002 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` board profile prepare/boot validation | Full |
| REQ-RFL-003..005 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` historical lane defaults and current RV64-first truthfulness checks | Full |
| REQ-RFL-006..007 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` deterministic prepare manifest and Vivado plan | Full |
| REQ-RFL-008 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` generated Simple hardware source expectations for the implemented helper set | Full |
| REQ-RFL-009 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` VHDL source-map and RTL manifest expectations for the implemented helper set | Full |
| REQ-RFL-010 | MIR bitfield lowering hook spec covering opcode/rd/funct3/rs1/rs2/funct7 extraction handoff to hardware decode, plus MIR JSON export visibility for functions, blocks, instructions, and terminators | Full for the implemented generated helper set: writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, execute datapath, branch datapath, control-flow datapath, memory access control, and jump immediate now parse/lower through frontend -> HIR -> MIR with exact slice/concat proof coverage |
| REQ-RFL-011 | VHDL slice-emission spec proving typed MIR bitfield extracts lower to deterministic `downto` slices with source-map entries after the expanded MIR JSON export exposes the lowering shape | Full for the implemented generated helper set: backend specs assert exact helper guards, slice emission, concat expressions, and source-map records for writeback/branch/store/I-type/upper/execute-control/execute-datapath/branch-datapath/control-flow-datapath/memory-access/jump helpers |

## Active Gates

- REQ-RFL-010 is satisfied for the current helper milestone. Generated RISC-V hardware source now carries dedicated writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, execute datapath, branch datapath, control-flow datapath, memory access control, and jump immediate helpers through the real frontend -> HIR -> MIR lowering path with bounded structured evidence.
- REQ-RFL-011 is satisfied for the same helper set. Backend specs now pin exact VHDL guard structure, slice usage, concat/update expressions, and source-map records, including execute-datapath, branch-datapath, and control-flow-datapath selection lowering, instead of relying on partial substring evidence.
- Memory behavior remains intentionally bounded: specs now assert helper-driven alignment guards for halfword/word/doubleword accesses, but byte-enable or strobe-capable store plumbing is still deferred to a later interface slice.
- The bounded memory-interface slice now has executable proof for `dmem_re`/`dmem_width` exposure, but subword write strobes and byte-enable semantics remain deferred.
- The bounded memory-interface slice now also proves `dmem_wstrb` exposure plus address-derived mask/data packing for `SB/SH/SW` on RV32 and `SB/SH/SW/SD` on RV64.
- The bounded memory-interface slice now also proves load-side lane extraction from aligned `dmem_rdata` through address-derived shifts before extension.
- Remaining RTL work is outside this trace milestone: broader handwritten-core replacement, CSR/privilege/MMU/trap coverage, and Linux boot validation still belong to later slices.
