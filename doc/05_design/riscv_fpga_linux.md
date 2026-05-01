<!-- codex-design -->
# RISC-V FPGA Linux Detail Design

Superseded for canonical Linux-platform truth by `doc/05_design/rv64_linux_rtl_pipeline.md`.
This file records the bounded helper-proof design and the original orchestration surface in `src/hardware/fpga_linux/riscv_fpga_linux.spl`, updated to match the strict generated-core provenance policy now enforced by generated runners.

Data model:

- `RiscvXlen`: `Rv32` and `Rv64`, with Linux policy and MMU mode helpers.
- `XilinxBoardProfile`: board identity, part, clock/reset, memory, UART, constraints, programmer, Vivado mode.
- `LinuxArtifactSet`: kernel, rootfs, firmware, DTB, and toolchain paths.
- `RiscvFpgaLane`: per-width SoC lane manifest and validation.
- `FpgaPrepareManifest`: board plus lanes, deterministic Vivado TCL plan, readiness summary, stable `build/.../rtl` contract paths, and emitted `authoritative_rtl_root` bundle paths for generated runners.
- Generated helper bitfields:
  - instruction layouts: `Rv32Instruction` / `Rv64Instruction`
  - immediate/control target layouts: `RiscvBranchImmediate`, `RiscvStoreImmediate`, `RiscvIImmediate`, `RiscvUpperImmediate`, `RiscvExecuteControl`, `RiscvExecuteDatapath`, `RiscvBranchDatapath`, `RiscvControlFlowDatapath`, `RiscvJumpImmediate`, `RiscvDispatchClass`, `RiscvTrapHaltControl`
  - source-layout overlays: `RiscvBranchEncoding`, `RiscvStoreEncoding`, `RiscvIImmediateEncoding`, `RiscvUpperImmediateEncoding`, `RiscvExecuteControlEncoding`, `RiscvExecuteDatapathEncoding`, `RiscvBranchDatapathEncoding`, `RiscvControlFlowDatapathEncoding`, `RiscvJumpEncoding`, `RiscvDispatchClassEncoding`, `RiscvTrapHaltControlEncoding`

Generated helper contract:

- Each lane emits dedicated pure `@hardware` + `@clocked` helpers for `decode_writeback`, `decode_branch_immediate`, `decode_store_immediate`, `decode_i_immediate`, `decode_upper_immediate`, `decode_execute_control`, `decode_execute_datapath`, `decode_branch_datapath`, `decode_control_flow_datapath`, `decode_memory_access_control`, `decode_jump_immediate`, `decode_dispatch_class`, and `decode_trap_halt_control`.
- Helper reconstruction is overlay-driven: read exact fields from source-layout bitfields, write exact fields into packed target bitfields, and return packed `u32` helper values.
- The helper surface is intentionally bounded: no PC update, register-file mutation, memory effects, privilege flow, interrupt flow, or MMU behavior. `decode_trap_halt_control` only classifies `continue`, `trap`, and `halt` for the current bounded shell.

Generated artifact details:

- The emitted package/core VHDL carries a source-map header in comment form, and each lane now emits a sibling `*.debug.json` sidecar as the canonical machine-readable debug metadata artifact for lint and proof tooling.
- Within that sidecar contract, `reportMarkers` are failure/debug-context telemetry markers for trap, halt, heartbeat, progress, and similar post-failure or in-flight diagnostics; they are not the top-level proof-success contract.
- The sidecar `runnerSuccessMarkers` field is the canonical machine-readable summary of top-level runner PASS markers and should be the first success surface consumed by lint/proof tooling before any deeper testbench log inspection.
- The emitted bundle is the only authoritative source for generated-core runner RTL; generated runners consume `GEN_DIR/.../rv32/rtl` and `GEN_DIR/.../rv64/rtl` rather than `examples/09_embedded/fpga_riscv/rtl`.
- Source-map lines cover instruction `opcode`, `rd`, `funct3`, `rs1`, `rs2`, `funct7` plus branch/store/I-type/upper/execute-control/execute-datapath/branch-datapath/control-flow-datapath/jump overlay fields.
- Source-map lines now also cover the dispatch-class and trap-halt opcode overlays.
- The handwritten VHDL shell keeps entity/package/process structure stable, but now consumes helper-aligned packed variables for writeback, branch immediate, store immediate, I-type immediate, upper immediate, execute control, execute datapath, branch datapath, control-flow datapath, memory access control, jump immediate, dispatch class, and trap/halt intent instead of independently reconstructing those values from ad hoc raw slices.
- The shell emitter is split into decode staging, execute/load-store behavior, and control-flow/trap-halt orchestration regions. The top-level bounded dispatch now keys off helper-derived class bits instead of a raw opcode `case`, and unsupported versus halt selection is routed through helper-derived intent bits.
- Memory accesses stay bounded to the current bus contract: helper-derived `funct3` drives load sign/zero extension and alignment traps, while unsupported store widths still trap instead of implying byte-strobe support the shell does not expose.
- The bounded memory shell now exposes `dmem_re` and `dmem_width` next to `dmem_we`, using helper-derived width codes `00/01/10/11` for byte/halfword/word/doubleword intent.
- The bounded store path now also exposes `dmem_wstrb` and lane-packed `dmem_wdata`, covering `SB/SH/SW` on RV32 and `SB/SH/SW/SD` on RV64 through address-derived masks and shifts.
- The bounded load path now mirrors that lane behavior by extracting bytes, halfwords, and words from aligned `dmem_rdata` via address-derived right shifts before sign or zero extension.
- Current lane policy is strict and repo-wide: RV32 and RV64 are both repo-native generated-core Linux lanes, and generated-core provenance comes from the emitted bundle RTL rather than handwritten example RTL.
- The generated RV32 Linux surface now lives in the default `rv32/rtl` bundle root and is authoritative for the repo-native acceptance path, paired with the generated RV64 Linux `rv64/rtl` bundle root.

Validation:

- `validate_for_prepare` accepts `xilinx_generic` and catches malformed profiles/lanes.
- `validate_for_hardware_boot` requires a real part and memory size.
- `validate_for_linux_boot` requires Linux artifacts plus advanced readiness for both RV32 and RV64, with OpenSBI or U-Boot firmware required when the shared Linux profile requires supervisor-mode handoff.
- `hardware_source_contract_errors` enforces helper declarations, overlay bitfields, decode guards, and exact field-to-field reconstruction assignments.
- Backend/unit/system specs prove the helper surface through exact MIR slice/concat checks, exact VHDL guard and concat checks, exact source-map comment checks, and provenance assertions that generated lanes do not fall back to `examples/09_embedded/fpga_riscv/rtl`.

Next slices:

- Add DTB/boot ROM generation.
- Add Vivado project materialization and board programming once the exact board profile is known.
- Extend the helper-proof pattern to additional decode/update families without reintroducing handwritten raw-slice reconstruction where a generated helper contract already exists.
- Use the next milestone to add CSR/privilege/MMU/interrupt/trap completion, DTB plus firmware handoff generation, and Linux boot validation on top of this bounded helper-driven shell rather than widening this historical artifact into a second canonical Linux pipeline.
- Until those layers are complete, treat external RV32 and RV64 Linux references as cross-checks only. They do not substitute for the repo-emitted authoritative `generated_rv32_linux` and `generated_rv64_linux` bundle roots.
- Keep future docs aligned with `rv64_linux_rtl_pipeline` as the canonical milestone rather than restating mixed-lane Linux capability claims or restoring authority to handwritten example RTL here.
