<!-- codex-design -->
# RISC-V FPGA Linux Detail Design

Superseded for canonical Linux-platform truth by `doc/05_design/rv64_linux_rtl_pipeline.md`.
This file records the bounded helper-proof design and the original orchestration surface in `src/hardware/fpga_linux/riscv_fpga_linux.spl`.

Data model:

- `RiscvXlen`: `Rv32` and `Rv64`, with Linux policy and MMU mode helpers.
- `XilinxBoardProfile`: board identity, part, clock/reset, memory, UART, constraints, programmer, Vivado mode.
- `LinuxArtifactSet`: kernel, rootfs, firmware, DTB, and toolchain paths.
- `RiscvFpgaLane`: per-width SoC lane manifest and validation.
- `FpgaPrepareManifest`: board plus lanes, deterministic Vivado TCL plan, readiness summary.
- Generated helper bitfields:
  - instruction layouts: `Rv32Instruction` / `Rv64Instruction`
  - immediate/control target layouts: `RiscvBranchImmediate`, `RiscvStoreImmediate`, `RiscvIImmediate`, `RiscvUpperImmediate`, `RiscvExecuteControl`, `RiscvJumpImmediate`
  - source-layout overlays: `RiscvBranchEncoding`, `RiscvStoreEncoding`, `RiscvIImmediateEncoding`, `RiscvUpperImmediateEncoding`, `RiscvExecuteControlEncoding`, `RiscvJumpEncoding`

Generated helper contract:

- Each lane emits dedicated pure `@hardware` + `@clocked` helpers for `decode_writeback`, `decode_branch_immediate`, `decode_store_immediate`, `decode_i_immediate`, `decode_upper_immediate`, `decode_execute_control`, `decode_memory_access_control`, and `decode_jump_immediate`.
- Helper reconstruction is overlay-driven: read exact fields from source-layout bitfields, write exact fields into packed target bitfields, and return packed `u32` helper values.
- The helper surface is intentionally bounded: no PC update, register-file mutation, memory effects, trap flow, privilege flow, or MMU behavior.

Generated artifact details:

- The emitted package/core VHDL carries a source-map header in comment form.
- Source-map lines cover instruction `opcode`, `rd`, `funct3`, `rs1`, `rs2`, `funct7` plus branch/store/I-type/upper/execute-control/jump overlay fields.
- The handwritten VHDL shell keeps entity/package/process structure stable, but now consumes helper-aligned packed variables for writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, memory access control, and jump immediate instead of independently reconstructing those values from ad hoc raw slices.
- Memory accesses stay bounded to the current bus contract: helper-derived `funct3` drives load sign/zero extension and alignment traps, while unsupported store widths still trap instead of implying byte-strobe support the shell does not expose.
- The bounded memory shell now exposes `dmem_re` and `dmem_width` next to `dmem_we`, using helper-derived width codes `00/01/10/11` for byte/halfword/word/doubleword intent.
- The bounded store path now also exposes `dmem_wstrb` and lane-packed `dmem_wdata`, covering `SB/SH/SW` on RV32 and `SB/SH/SW/SD` on RV64 through address-derived masks and shifts.
- The bounded load path now mirrors that lane behavior by extracting bytes, halfwords, and words from aligned `dmem_rdata` via address-derived right shifts before sign or zero extension.
- Current default generation is RV64-first. RV32 remains a parity-only contract lane and is intentionally not emitted by the default manifest.

Validation:

- `validate_for_prepare` accepts `xilinx_generic` and catches malformed profiles/lanes.
- `validate_for_hardware_boot` requires a real part and memory size.
- `validate_for_linux_boot` requires Linux artifacts plus advanced readiness; RV64 additionally requires OpenSBI or U-Boot firmware, while RV32 is explicitly rejected as a first-class Linux CPU/RTL claim.
- `hardware_source_contract_errors` enforces helper declarations, overlay bitfields, decode guards, and exact field-to-field reconstruction assignments.
- Backend/unit/system specs prove the helper surface through exact MIR slice/concat checks, exact VHDL guard and concat checks, and exact source-map comment checks.

Next slices:

- Add DTB/boot ROM generation.
- Add Vivado project materialization and board programming once the exact board profile is known.
- Extend the helper-proof pattern to additional decode/update families without reintroducing handwritten raw-slice reconstruction where a generated helper contract already exists.
- Keep future docs aligned with `rv64_linux_rtl_pipeline` as the canonical milestone rather than restating mixed-lane Linux capability claims here.
