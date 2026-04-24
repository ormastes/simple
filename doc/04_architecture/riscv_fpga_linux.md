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

- REQ-RFL-010 is partially satisfied: generated RISC-V hardware source now parses and lowers through the real frontend -> HIR -> MIR path, and bounded specs already prove typed bitfield reads and `rd` writeback recomposition for selected decode/update helpers.
- REQ-RFL-010 reaches full satisfaction when that generated-source-backed coverage expands beyond the current opcode/rd/funct3/rs1/rs2/funct7 helper cases to additional decode and immediate reconstruction paths while still rejecting out-of-range or dynamic extraction before VHDL lowering.
- REQ-RFL-011 remains gated on exact VHDL/backend proof: specs must show those typed MIR extracts lower to stable slices, guard structure, concat/update expressions, and source-map records without re-parsing facade source strings.
- MIR JSON export is the trace boundary between compiler lowering and RTL/VHDL tests. It must expose enough structured module shape for specs to identify functions, basic blocks, emitted instructions, and terminators without depending on raw debug logs.
- Remaining gap: broader generated decode/immediate coverage and exact VHDL/source-map assertions, not frontend or semantic acceptance of `bitfield` declarations. The MIR and VHDL work should continue to extend the real compiler path rather than add a RISC-V-only bypass.
