<!-- codex-design -->
# RISC-V FPGA Linux Architecture

The feature adds a small preparation layer above existing RISC-V hardware and VHDL backend work. It does not claim full Linux-capable RTL is complete; it defines the board and lane contracts required to generate, synthesize, program, and boot-test that RTL.

Core architecture:

- `XilinxBoardProfile` owns board-specific data and separates prepare-time validation from hardware-boot validation.
- `RiscvFpgaLane` owns per-width SoC lane data: RV32 experimental Linux and RV64 upstream Linux.
- `FpgaPrepareManifest` combines one board profile with one or more lanes and emits deterministic Vivado project intent.
- MIR bitfield lowering owns the first compiler hook for RISC-V instruction field extraction. It must preserve width, offset, signedness, and source span metadata as structured MIR facts rather than as VHDL strings.

Future implementation layers should consume this contract:

- RTL generator: emits RV32/RV64 SoC VHDL from Simple hardware modules.
- VHDL slice emitter: consumes the MIR bitfield extraction facts and emits deterministic `std_logic_vector` slices for opcode, register, funct, immediate, and CSR decode fields, with source-map entries tied back to the Simple hardware source.
- Firmware packager: emits boot ROM, DTB, OpenSBI/U-Boot payload metadata.
- Vivado adapter: materializes TCL/project/bitstream from `FpgaPrepareManifest`.
- Boot tester: programs the board and matches UART markers defined by each lane.

Traceability handoff:

- REQ-RFL-010 is satisfied when MIR tests prove the bitfield hook exists for bounded RISC-V decode fields and rejects out-of-range or dynamic extraction before VHDL lowering.
- REQ-RFL-011 is satisfied when VHDL backend specs prove those MIR extracts lower to stable slices and source-map records without re-parsing facade source strings.
- MIR JSON export is the trace boundary between compiler lowering and RTL/VHDL tests. It must expose enough structured module shape for specs to identify functions, basic blocks, emitted instructions, and terminators without depending on raw debug logs.
- Current blocker: generated hardware source cannot complete REQ-RFL-010 until frontend and semantic analysis accept `bitfield` declarations and resolve bitfield field reads into typed HIR/MIR metadata. The MIR and VHDL work should not add a parallel RISC-V-only parser to bypass that semantic path.
