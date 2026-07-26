
## lane1 notes

- 2026-07-26 lane1 (exec-core generator) COMPLETE — pure-Simple structured generator
  `src/lib/hardware/vhdl_gen/` emits rv32_exec_core.vhd (1179 lines) + rv64_exec_core.vhd
  (685 lines) into build/os/rtl/, byte-identical to the goldens (diff = 0 both), from one
  shared template parameterized by XlenConfig. Deterministic (2 runs, identical md5).
  Deliberate-red: flipping opcode "0010011" in the rv32 table changed exactly the one
  `when` arm line — decode is live table-driven. GHDL `-a --std=08` clean on both.
  Entry: `sh scripts/fpga/generate_exec_core_vhdl.shs [--mem-prefix DIR/] [--out-dir DIR]`.
  Tests: test/01_unit/lib/hardware/vhdl_gen/exec_core_gen_spec.spl + probe_exec_core_gen.spl
  (probe: EXEC_CORE_GEN PROBE: ALL PASS).
- Structure: ~16% of output lines structurally generated (entity/ports/generics via VgPort
  descriptor arrays, constants via XlenConfig+VgCoreGeometry, regs_t/state_t types,
  init_rom/init_data_rom/init_mem via VgMemInit, concurrent assigns, 12+13 opcode decode
  when-arms via VgArm tables, 7 CSR read-mux cases via VgCsr table, all dbg_* taps via
  debug_tap_aspect join points ports/signals/assigns/process_taps, default ON); remaining
  ~84% is irreducible per-core logic paragraphs as named literal sections (26 rv32 + 20 rv64
  section functions in rv32_sections.spl / rv64_sections.spl) per design rule 1.
- runtime_need: chosen_path=reuse-facade, no new rt_* — reuses existing rt_file_write_text /
  rt_file_read_text externs (same facade as src/lib/hardware/fpga_linux/xdc_gen.spl).
- Landmine hit: a parallel jj session (snapshot/commit/fetch/rebase at ~05:50Z) swept ALL
  uncommitted new files mid-task (src files + spec + this state.md); recreated from
  scratchpad masters and re-verified green. Keep scratchpad backups until landed.
