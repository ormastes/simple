
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

## Lane 4 — flat/axi variant cores (2026-07-26)
- DONE: generator extended to emit ALL SIX cores byte-identical to goldens: base rv32/rv64
  plus rv32/rv64_exec_core_flat.vhd (806/934 lines; GHDL boot-tiny + NVMe-fw testbenches)
  and rv32/rv64_exec_core_axi.vhd (840/1047; AXI SoC tops). One driver run
  (`sh scripts/fpga/generate_exec_core_vhdl.shs`) writes all 6 into build/os/rtl/;
  diff vs golden = 0 for each; two runs byte-identical (md5 sets equal).
- Factoring (variants are siblings of EACH OTHER, not of the base: verbatim base-section
  reuse is only ~32/16 lines per rv32/rv64 variant, but flat<->axi share 521 (rv32) / 660
  (rv64) lines): fa## sections shared flat<->axi + fl##/ax## variant-only literals in NEW
  rv32_variant_sections.spl / rv64_variant_sections.spl; assembly + entity descriptor tables
  in NEW exec_core_variant_gen.spl; NEW gen_types primitives VgGenericSpec/VgPortSpec/
  emit_entity_spec (per-item name_w/dir_w column widths — the goldens use GROUP-LOCAL port
  alignment a single aligned flag can't express) + vg_reindent (rv64 variants reuse base
  decode arms shifted +2). .mem references (init_ram "rvNN_flat.mem" + file_open
  "rvNN_ramdisk.mem") emitted in the assembly so --mem-prefix covers them.
- Coverage stats: of 3627 total variant-golden lines, 68.2% emitted from sections shared
  with another core (fa## + base-arm reuse + library headers), 3.2% descriptor/structured
  (entity/ports/generics, arch line, mem-file lines), 28.6% variant-only literals
  (per-variant: flat32 69.2%/rv64 72.9% shared). No whole-core forks of shared sections.
- check-vhdl-golden-match.shs: CORES extended to 6; new keys vhdl_golden_match_rv32_flat/
  rv64_flat/rv32_axi/rv64_axi; --selftest gained a variant deliberate-red phase
  (rv32_flat mutant -> fail, proven). Gate run: all 6 keys=pass; overall ok=false ONLY from
  a PRE-EXISTING manifest drift on tb_rv64_k26_ddr_boot.vhd — an UNCOMMITTED parallel-lane
  edit (rv64 KV260 DDR session); HEAD gate fails identically, so not this lane's regression.
  With that single external entry factored out (scratch manifest, repo untouched):
  manifest=ok, all 6 pass, ok=true, selftest=ok. The landing lane for the tb edit must
  regenerate the manifest in its own commit.
- check-riscv-rtl-truth.shs: all 6 build/os/rtl cores classify generated-real,
  riscv_rtl_truth_generated_real=6, riscv_rtl_truth_ok=true.
- Tests: spec extended with 6 variant scenarios (golden-match x4, determinism, flat
  mem-prefix incl. ramdisk file_open); probe extended, prints EXEC_CORE_GEN PROBE: ALL PASS
  (14 PASS lines). NOTE pre-existing: deployed seed's `simple test` cannot parse `@step "..."`
  decorators (HEAD spec fails identically: "expected Fn, found FString") — probe is the
  runnable evidence lane until a self-hosted redeploy.
- Lint note (pre-existing class): seed linter fires COLL006 "string concat in loop" on the
  bounded padding/joining loops this generator family deliberately uses (14 hits already at
  HEAD in gen_types/generate_main); new code follows the same landed style.

## lane5 evidence (2026-07-26, GHDL gates on GENERATED cores)
All three lanes ran against staged rtl where the exec cores are the vhdl_gen
GENERATED artifacts (sha256 generated==staged==golden IDENTICAL for all 6 cores;
full table: build/test-artifacts/vhdl_gen_ghdl_evidence_2026-07-26/core_sha256.txt).
- lane1 rv32 SimpleOS boot (tiny): PASS — `RV32_TINY_BOOT_DONE reached=TEST_PASSED`,
  kernel ladder through `SIMPLEOS_RISCV_SMF_FS_PASS` / `TEST PASSED`, stack_used=344.
  Transcript: build/test-artifacts/vhdl_gen_ghdl_evidence_2026-07-26/lane1_rv32_tiny_boot.log
- lane2 rv32 NVMe fw smoke: PASS — `RV32_NVME_FW_PASS`, `STATUS: PASS ghdl-rv32-nvme-fw`
  (firmware ran on soft-core, marker matches QEMU).
  Transcript: .../lane2_rv32_nvme_fw.log
- lane3 rv64 SimpleOS K26-DDR boot: PASS — `RESULT: PASS - rv64 SimpleOS booted through
  the AXI4/DDR path`, rc=0. Transcript: .../lane3_rv64_k26_ddr_boot.log
Board lane remains explicitly BLOCKED on 3.3V PMOD UART adapter (AC-4/AC-11) —
hardware procurement; resume = program KV260 bitstream built from build/os/rtl cores
via scripts/fpga/build_k26_rv32_ddr_bitstream.shs once adapter present.

## lane6 silicon evidence

FULL SILICON PROOF: KV260 (xck26) bitstreams built FROM THE GENERATED exec cores
and booted on the physical board. Evidence:
`build/test-artifacts/vhdl_gen_silicon_evidence_2026-07-26/` (see README.md there).

Provenance: `sh scripts/fpga/generate_exec_core_vhdl.shs` ->
`sh scripts/check/check-vhdl-golden-match.shs --require-generated` = all 6 cores
PASS (only drift is the working-copy TESTBENCH `tb_rv64_k26_ddr_boot.vhd`, not a
core). Generated cores staged into `build/fpga/rtl_gen_rv32/` and
`build/fpga/rtl_gen_rv64/` with the unmodified SoC/adapter/ctrl-slave files;
`cmp` proves each staged core byte-identical to its golden. `examples/` untouched.
Both DDR build scripts gained one env-overridable line
`RTL_DIR="${RTL_DIR:-examples/09_embedded/fpga_riscv/rtl}"` (default unchanged).

### Lane 6a — rv32-DDR: PASS (silicon)
- core sha256 4c19ffe470f7e3bd81d346f283605b96c0060dfa75fe42817b60b6d8f2b00be0
  (`build/os/rtl/rv32_exec_core_axi.vhd`, == golden)
- bitstream sha256 3ca189ba73d898c805baaac7c1fad08de43ec01bcb9f930d9ef37e28b6afcc4b
  (`build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit`)
- build: `ALLOW_CONCURRENT_BUILD=1 RTL_DIR=build/fpga/rtl_gen_rv32 bash scripts/fpga/build_k26_rv32_ddr_bitstream.shs`
- boot: `bash scripts/fpga/bringup_kv260_rv32_ddr.shs` (full psu_init from XSA,
  ELF-derived .bss zero-fill: BSS_HEAPOFF_PRE=0x260 -> POST=0x0), rc=0
- markers: CTRL_MAGIC=0x52563332, UART_BYTE_COUNT=445, FINAL_PC=0x8000002A,
  AXI_READS=17341264 / AXI_WRITES=95898, transcript reached
  `SIMPLEOS_RISCV_SMF_FS_PASS` + `TEST PASSED`
- verdict line: `PASS: rv32 SimpleOS reached TEST PASSED on KV260 silicon`

### Lane 6b — rv64-DDR: PASS (silicon)
- core sha256 c83c0869eab5e37e5d02bd9a3fc215279dc9ecbbfd17ea2e2d72af5fe14600c8
  (`build/os/rtl/rv64_exec_core_axi.vhd`, == golden)
- bitstream sha256 3ffb79f0d2709dc3218a8870f9e9bea1b41251c28fe2c04fb74aebee5924f686
  (`build/fpga/k26_rv64_ddr/k26_rv64_ddr.bit`), Vivado TIMING_MET
- build: `ALLOW_CONCURRENT_BUILD=1 RTL_DIR=build/fpga/rtl_gen_rv64 bash scripts/fpga/build_k26_rv64_ddr_bitstream.shs`
- first bring-up hit the documented WEDGED-PS zero-fetch (CTRL_MAGIC ok, loads
  verified, CORE_RELEASED, but AXI_READS=0 / UART_BYTE_COUNT=0) — see
  `rv64_bringup_attempt1_wedged.log`. Fix applied exactly once: xsdb
  `targets -filter {name =~ "PSU"}; rst -system` (`rv64_rst_system.log`), then
  re-ran the bring-up unmodified.
- markers after reset: UART_BYTE_COUNT=546, FINAL_PC_LO32=0x80200028,
  AXI_READS=10374602 / AXI_WRITES=85007, transcript reached
  `SIMPLEOS_RISCV_SMF_FS_PASS` + `TEST PASSED`
- verdict line: `PASS: rv64 SimpleOS reached TEST PASSED on KV260 silicon`

### Timing finding (recorded honestly)
rv32-DDR misses timing at IMPL_WNS=-0.115377 / WHS=+0.017749 and Vivado prints
TIMING_NOT_MET. The retained GOLDEN-RTL build log
(`build/fpga/k26_rv32_ddr/vivado_1302320.backup.log`) reports the **identical**
WNS/WHS, so this is PRE-EXISTING SoC design timing, NOT a generator regression
(`rv32_ddr_timing_parity.txt`). The board is the arbiter and it booted. rv64-DDR
MEETS timing (`rv64_ddr_timing_parity.txt`). Follow-up (not a lane-6 blocker):
close the -0.115ns path on soc_top_rv32_k26_ddr.

### Still blocked (unchanged, accepted)
Interactive UART login on the board needs a 3.3 V PMOD adapter (AC-4/AC-11,
hardware procurement) — the KV260 carrier does not route fabric UART H12/PMOD J2
to the FT4232H. JTAG status-word / UART-capture markers remain the accepted
silicon bar, same as the prior golden silicon PASSes. Resume when the adapter
arrives: `bash scripts/fpga/capture_kv260_uart_ila.shs`.

Reproduce either lane end to end:
```
sh scripts/fpga/generate_exec_core_vhdl.shs
ALLOW_CONCURRENT_BUILD=1 RTL_DIR=build/fpga/rtl_gen_rv32 bash scripts/fpga/build_k26_rv32_ddr_bitstream.shs
bash scripts/fpga/bringup_kv260_rv32_ddr.shs     # rv64: swap 32->64 in both
```

## VHDL process-facade SSpec follow-up (2026-08-16)

- Requirement: `REQ-VHDL-SFFI-001`.
- Executable: `test/03_system/feature/usage/vhdl_spec.spl` — three modern
  step-based scenarios covering positive qualified GHDL analysis, exact result
  edge semantics, and real invalid-VHDL error capture.
- Fail-closed admission: absent `SIMPLE_VHDL_TEST=1` prints `TEST_BLOCKED`,
  fails the `ready` matcher, and returns before host-tool execution; no skip can
  become PASS.
- Manual: `doc/06_spec/03_system/feature/usage/vhdl_spec.md`.
- Plan/traceability: `doc/03_plan/sys_test/vhdl_process_facade.md`.
- Runtime status: `TEST_BLOCKED`. The admitted Stage2 recovery runtime supports
  `compile`/`native-build` only, not `test`, `spipe-docgen`, or
  `sspec-maintain`. The earlier admitted native probe PASS remains
  implementation evidence and is not reused as SSpec/docgen evidence.
- Resume once: with an admitted full CLI and GHDL/Yosys installed, set
  `SIMPLE_VHDL_TEST=1`, run the SSpec, docgen, and sspec-maintain commands from
  the plan exactly once, then replace the manual's blocked provenance only if
  all three gates pass.
