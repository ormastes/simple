# RISC-V FPGA Linux System Test Plan

- Unit: board profiles validate prepare-only versus hardware-boot requirements.
- Unit: RV32 and RV64 lanes expose correct MMU modes, Linux policies, required SoC blocks, and boot markers.
- Unit: Linux boot validation fails until required artifacts are configured.
- Unit: MIR lowering exposes a bounded bitfield extraction hook for RISC-V instruction decode fields before any VHDL text is emitted.
- Integration: Vivado TCL plan generation is deterministic for `xilinx_generic`.
- Integration: generated RV32/RV64 Simple hardware source preserves `@hardware`, `@clocked`, instruction bitfields, opcode width, and decode source traces.
- Integration: generated VHDL includes source-map comments, typed slice emission for decoded instruction fields, RV base integer decode cases, and the RTL manifest records source, package, and core files for both lanes.
- Regression: existing VHDL backend E2E, RV32 RTL simulation, RV32/RV64 emulator, and RISC-V QEMU boot specs remain green.
- Hardware: when the Xilinx board arrives, program bitstreams and capture UART markers for RV64 upstream Linux and RV32 experimental Linux.

## Traceability

| REQ | Executable Spec | Coverage |
|-----|-----------------|----------|
| REQ-RFL-001..002 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` board profile prepare/boot validation | Full |
| REQ-RFL-003..005 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` RV32/RV64 lane defaults and source contracts | Full |
| REQ-RFL-006..007 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` deterministic prepare manifest and Vivado plan | Full |
| REQ-RFL-008 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` generated Simple hardware source expectations | Full |
| REQ-RFL-009 | `doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl` VHDL source-map and RTL manifest expectations | Full |
| REQ-RFL-010 | MIR bitfield lowering hook spec covering opcode/rd/funct3/rs1/rs2/funct7 extraction handoff to hardware decode, plus MIR JSON export visibility for functions, blocks, instructions, and terminators | Planned; blocked on frontend/semantic bitfield resolution for generated source |
| REQ-RFL-011 | VHDL slice-emission spec proving typed MIR bitfield extracts lower to deterministic `downto` slices with source-map entries after the expanded MIR JSON export exposes the lowering shape | Planned; depends on REQ-RFL-010 blocker removal |

## Active Blockers

- Frontend/semantic bitfield support is the next blocker for REQ-RFL-010. The generated RISC-V hardware source already uses `bitfield` definitions and field reads, but those must parse, resolve, and reach HIR/MIR as typed bitfield metadata before MIR lowering can prove bounded extraction on real generated source.
- The expanded MIR JSON export now provides a usable trace surface for downstream specs by including function, block, instruction, and terminator payloads. The next spec update should assert bitfield-lowering instruction shape through that JSON surface once frontend/semantic resolution is unblocked.
