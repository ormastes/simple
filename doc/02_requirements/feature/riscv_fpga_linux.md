# RISC-V FPGA Linux Feature Requirements

- REQ-RFL-001: Provide a Xilinx board-profile contract with board name, part, clock, reset, memory, UART, constraints, programmer, and Vivado mode.
- REQ-RFL-002: Permit `xilinx_generic` for pre-hardware preparation, but reject it for hardware boot validation.
- REQ-RFL-003: Define RV32 and RV64 CPU SoC lanes with top module, RTL output directory, boot ROM path, Linux artifact set, MMU mode, required SoC blocks, and boot markers.
- REQ-RFL-004: Mark RV64 Linux as upstream and require firmware handoff through OpenSBI or U-Boot before Linux boot validation.
- REQ-RFL-005: Mark RV32 Linux as experimental and require externally supplied kernel, rootfs, DTB, and toolchain artifacts before boot validation.
- REQ-RFL-006: Generate a deterministic Vivado TCL preparation plan from the board profile and lane manifests.
- REQ-RFL-007: Keep pre-hardware validation executable without a connected FPGA.
