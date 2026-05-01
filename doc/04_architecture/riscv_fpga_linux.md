<!-- codex-design -->
# RISC-V FPGA Linux Architecture

Superseded for canonical RV64 Linux truth by `doc/04_architecture/rv64_linux_rtl_pipeline.md`.
This document remains historical context for the orchestration-layer origin and the completed helper-proof milestone only, but it now reflects the strict generated-core provenance policy used by the active runners.

The feature adds a small preparation layer above existing RISC-V hardware and VHDL backend work. It does not claim full Linux-capable RTL is complete; it defines the board and lane contracts required to generate, synthesize, program, and boot-test that RTL. For generated-core lanes, the authoritative runner-consumed RTL is the emitted bundle under `GEN_DIR/.../rtl`, not handwritten files under `examples/09_embedded/fpga_riscv/rtl`.

Core architecture:

- `XilinxBoardProfile` owns board-specific data and separates prepare-time validation from hardware-boot validation.
- `RiscvFpgaLane` owns the strict lane contract: RV32 remains the repo-native generated-core baremetal lane, RV64 remains the repo-native generated-core Linux lane, and any RV32 Linux bring-up stays opt-in as an explicit experimental lane.
- `FpgaPrepareManifest` combines one board profile with one or more lanes and emits deterministic Vivado project intent.
- `FpgaPrepareManifest` records both the stable `build/.../rtl` contract path and the emitted `authoritative_rtl_root` consumed by generated runners from `GEN_DIR/.../rtl`.
- MIR bitfield lowering owns the first compiler hook for RISC-V instruction field extraction. It must preserve width, offset, signedness, and source span metadata as structured MIR facts rather than as VHDL strings.

Future implementation layers should consume this historical contract shape without over-claiming platform readiness:

- RTL generator: emits bounded lane artifacts and helper-proof RTL scaffolding from Simple hardware modules, including the authoritative wrapper/package/testbench set required by generated runners.
- VHDL slice emitter: consumes the MIR bitfield extraction facts and emits deterministic `std_logic_vector` slices for opcode, register, funct, immediate, and CSR decode fields, with source-map entries tied back to the Simple hardware source.
- Firmware packager: emits boot ROM, DTB, OpenSBI/U-Boot payload metadata.
- Vivado adapter: materializes TCL/project/bitstream from `FpgaPrepareManifest`.
- Boot tester: programs the board and matches UART markers defined by each lane while sourcing generated-core RTL only from the emitted bundle directories.

Traceability handoff:

- REQ-RFL-010 is satisfied for the implemented helper set: generated RISC-V hardware source now parses and lowers through the real frontend -> HIR -> MIR path, and bounded specs prove typed bitfield reads and dedicated writeback/branch/store/I-type/upper/execute-control/execute-datapath/branch-datapath/control-flow-datapath/memory-access/jump/dispatch/trap-halt helper recomposition.
- REQ-RFL-011 is satisfied for the same helper set: specs show those typed MIR extracts lower to stable slices, exact guard structure, concat/update expressions, and source-map records without re-parsing facade source strings, including execute-datapath, branch-datapath, control-flow-datapath, dispatch-class, and trap-halt contracts.
- Generated-core provenance now has an explicit architectural rule: generated runners may compile only the bundle-emitted RTL rooted at `GEN_DIR/.../rtl`, and `examples/09_embedded/fpga_riscv/rtl` is non-authoritative for repo-native generated-core lanes.
- The optional `generated_rv32_linux` lane is intentionally non-authoritative. Its emitted `rv32_linux/rtl` bundle exists only to cross-check Linux handoff and DTB bring-up on the generated RV32 shell without upgrading RV32 Linux to the repo-native proof claim.
- Future decode families should extend the same contract rather than bypass it with handwritten bit slicing or backend-specific special cases.
- MIR JSON export is the trace boundary between compiler lowering and RTL/VHDL tests. It must expose enough structured module shape for specs to identify functions, basic blocks, emitted instructions, and terminators without depending on raw debug logs.
- The handwritten VHDL shell is now internally separated into decode staging, execute/load-store behavior, and control-flow/trap-halt orchestration regions so bounded follow-on cleanup can land without re-editing one monolithic string block.
- Remaining gap is no longer the helper-proof trace surface. The next work items are CSR/privilege/MMU/interrupt/trap completion, firmware handoff and DTB plumbing, OpenSBI/U-Boot/Linux boot validation, and continued extension of the real compiler path rather than a return to handwritten example RTL for generated-core lanes.
