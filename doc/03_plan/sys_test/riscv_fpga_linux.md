# RISC-V FPGA Linux System Test Plan

- Unit: board profiles validate prepare-only versus hardware-boot requirements.
- Unit: RV32 and RV64 lanes expose correct MMU modes, Linux policies, required SoC blocks, and boot markers.
- Unit: Linux boot validation fails until required artifacts are configured.
- Integration: Vivado TCL plan generation is deterministic for `xilinx_generic`.
- Integration: generated RV32/RV64 Simple hardware source preserves `@hardware`, `@clocked`, instruction bitfields, opcode width, and decode source traces.
- Integration: generated VHDL includes source-map comments, RV base integer decode cases, and the RTL manifest records source, package, and core files for both lanes.
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
