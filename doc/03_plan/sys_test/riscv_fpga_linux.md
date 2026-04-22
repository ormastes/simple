# RISC-V FPGA Linux System Test Plan

- Unit: board profiles validate prepare-only versus hardware-boot requirements.
- Unit: RV32 and RV64 lanes expose correct MMU modes, Linux policies, required SoC blocks, and boot markers.
- Unit: Linux boot validation fails until required artifacts are configured.
- Integration: Vivado TCL plan generation is deterministic for `xilinx_generic`.
- Regression: existing VHDL backend E2E, RV32 RTL simulation, RV32/RV64 emulator, and RISC-V QEMU boot specs remain green.
- Hardware: when the Xilinx board arrives, program bitstreams and capture UART markers for RV64 upstream Linux and RV32 experimental Linux.
