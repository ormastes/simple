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

- REQ-RFL-010 is satisfied for the implemented helper set: generated RISC-V hardware source now parses and lowers through the real frontend -> HIR -> MIR path, and bounded specs prove typed bitfield reads and dedicated writeback/branch/store/jump helper recomposition.
- REQ-RFL-011 is satisfied for the same helper set: specs show those typed MIR extracts lower to stable slices, exact guard structure, concat/update expressions, and source-map records without re-parsing facade source strings.
- Future decode families should extend the same contract rather than bypass it with handwritten bit slicing or backend-specific special cases.
- MIR JSON export is the trace boundary between compiler lowering and RTL/VHDL tests. It must expose enough structured module shape for specs to identify functions, basic blocks, emitted instructions, and terminators without depending on raw debug logs.
- Remaining gap is no longer the helper-proof trace surface. The next work items are broader handwritten-core replacement and eventual Linux-capable SoC concerns, while continuing to extend the real compiler path rather than add a RISC-V-only bypass.
