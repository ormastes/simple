<!-- codex-research -->
# RISC-V FPGA Linux Local Research

The repo currently has three relevant foundations:

- Generic VHDL backend support in `src/compiler/70.backend/backend`, with GHDL validation and support-matrix docs for a bounded synthesizable subset.
- RV32 FPGA/VHDL example under `examples/09_embedded/fpga_riscv`, including a single-cycle RV32I core, GHDL simulation, and ZedBoard-oriented Vivado scripts.
- RV64 software/hardware models under `src/hardware/rv64gc` plus QEMU boot scripts for SimpleOS RISC-V 32/64.

Gaps for Linux-on-FPGA:

- No board-profile abstraction exists for unknown Xilinx hardware.
- No RV64 synthesizable RTL SoC lane exists.
- Existing RV32 RTL is useful for smoke tests but is not Linux-capable; it lacks Linux-grade MMU, interrupts, firmware handoff, and memory-controller integration.
- Linux boot validation is currently QEMU/firmware-script based, not FPGA UART/bitstream based.

Implementation implication: the first safe slice is a pre-hardware preparation contract that validates board profiles, RV32/RV64 lane manifests, Vivado inputs, Linux artifact requirements, and boot-marker policy before the exact board arrives.
