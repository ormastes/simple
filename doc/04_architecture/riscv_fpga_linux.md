<!-- codex-design -->
# RISC-V FPGA Linux Architecture

The feature adds a small preparation layer above existing RISC-V hardware and VHDL backend work. It does not claim full Linux-capable RTL is complete; it defines the board and lane contracts required to generate, synthesize, program, and boot-test that RTL.

Core architecture:

- `XilinxBoardProfile` owns board-specific data and separates prepare-time validation from hardware-boot validation.
- `RiscvFpgaLane` owns per-width SoC lane data: RV32 experimental Linux and RV64 upstream Linux.
- `FpgaPrepareManifest` combines one board profile with one or more lanes and emits deterministic Vivado project intent.

Future implementation layers should consume this contract:

- RTL generator: emits RV32/RV64 SoC VHDL from Simple hardware modules.
- Firmware packager: emits boot ROM, DTB, OpenSBI/U-Boot payload metadata.
- Vivado adapter: materializes TCL/project/bitstream from `FpgaPrepareManifest`.
- Boot tester: programs the board and matches UART markers defined by each lane.
