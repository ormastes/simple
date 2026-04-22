<!-- codex-design -->
# RISC-V FPGA Linux Detail Design

The initial implementation lives in `src/hardware/fpga_linux/riscv_fpga_linux.spl`.

Data model:

- `RiscvXlen`: `Rv32` and `Rv64`, with Linux policy and MMU mode helpers.
- `XilinxBoardProfile`: board identity, part, clock/reset, memory, UART, constraints, programmer, Vivado mode.
- `LinuxArtifactSet`: kernel, rootfs, firmware, DTB, and toolchain paths.
- `RiscvFpgaLane`: per-width SoC lane manifest and validation.
- `FpgaPrepareManifest`: board plus lanes, deterministic Vivado TCL plan, readiness summary.

Validation:

- `validate_for_prepare` accepts `xilinx_generic` and catches malformed profiles/lanes.
- `validate_for_hardware_boot` requires a real part and memory size.
- `validate_for_linux_boot` requires Linux artifacts; RV64 additionally requires OpenSBI or U-Boot firmware.

Next slices:

- Add actual RTL emission from the Simple hardware model into lane `rtl_dir`.
- Add DTB/boot ROM generation.
- Add Vivado project materialization and board programming once the exact board profile is known.
