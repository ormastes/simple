# Feature Expert: Pure-Simple VHDL Exec-Core Generator

## Role

Own process knowledge for `src/lib/hardware/vhdl_gen/` — the pure-Simple
generator that EMITS the RISC-V exec cores that were previously hand-written
VHDL. It is a **structured** generator (typed descriptor arrays elaborated into
VHDL text), explicitly NOT blob embedding: no whole-file string constants, no
`.vhd` read-and-reprint. Written so the next agent does not re-litigate "is the
generated core real?" — it is silicon-proven.

## What it emits

**35 RTL files**, every one byte-identical to its golden:

- **6 silicon-lane exec cores** — `rv32`/`rv64` x {base, `_flat`, `_axi`}.
  Variants share ~68% of emitted lines with the base sections (state.md: 68.2%
  of 3627 variant-golden lines come from shared sections).
- **24 more** under `examples/09_embedded/fpga_riscv/rtl/` — 4 bus/memory infra
  (2 AXI4 adapters, `rv32_ctrl_obs_slave`, `rv32_bram_soc`), 7 SoC tops, 13
  testbenches. With the cores that is **all 30** files in that directory.
- **5 with goldens OUTSIDE that directory** — `tb_rv32_payload.vhd`,
  `test/riscv_isa_gate/tb_gate.vhd`, and the three `fpga_linux` product
  testbenches (rv32 sv32-PMP, rv64 sv39-PMP, rv64 WB/AXI).

Two output dirs: 30 files land in `build/os/rtl/`, the 5 out-of-tree-golden ones
in **`build/os/rtl_external/`** — because `check-riscv-rtl-truth.shs` scans
`build/os/rtl` as a single lane and requires every instantiated entity to be
defined within it. `generate_main.spl` holds the one authoritative output list
(and its own `ext_names`/`ext_texts` pair for the external set).

- Driver: `sh scripts/fpga/generate_exec_core_vhdl.shs [--mem-prefix DIR/] [--out-dir DIR]`
  (entry `src/lib/hardware/vhdl_gen/generate_main.spl`).
- 64/32 templating is `XlenConfig` (`std.hardware.riscv_common.xlen`,
  `XlenConfig.rv32()` / `.rv64()`) — a RUNTIME value, because Simple has no
  const generics. Width is a struct field consumed at elaboration time.
- JTAG is an **AOP aspect**, not a fork: `vhdl_gen/debug_tap_aspect.spl` weaves
  the `debug_*` / `dbg_reg_*` taps at four named join points — PORTS, SIGNALS,
  ASSIGNS, PROCESS_TAPS — default ON. OFF is diagnostic-only (the literal core
  paragraphs still reference `debug_*`, so OFF output is not buildable).
  TAP/DTM/DMI/DM themselves stay hand-written in `src/lib/hardware/debug/`.

## Source of truth

- Sufficiency study (normative on the language constraints):
  `doc/01_research/hardware/riscv/simple_grammar_vhdl_edsl_sufficiency_2026-07-26.md`;
  prior-art survey: `.../python_rtl_generation_survey_2026-07-26.md`.
- Plan: `doc/03_plan/hardware/riscv/vhdl_exec_core_generator_plan.md`;
  migration: `doc/03_plan/hardware/riscv/riscv_generated_core_migration.md`.
- Lane state + evidence: `.spipe/vhdl-gen-backend/state.md`.
- Specs: `test/01_unit/lib/hardware/vhdl_gen/exec_core_gen_spec.spl` (+
  `probe_exec_core_gen.spl`),
  `test/03_system/compiler/pure_simple_vhdl_source_of_truth_spec.spl`.

## Gates

- `sh scripts/check/check-vhdl-golden-match.shs` — byte-compares all 35 files.
  Generation is now the DEFAULT (a missing generated file FAILS);
  `--allow-missing` opts out, `--require-generated` is an accepted no-op.
  Layers: 1 manifest drift, 2 the 6 cores (per-core keys), 3 the other 24
  (`vhdl_golden_match_rest_{total,pass,fail,missing}`, `rest_total=24`),
  3b out-of-tree goldens (`..._external_{total,pass,fail,missing}`,
  `external_total=5`; read from `build/os/rtl_external/`, override with
  `VHDL_GEN_EXT_DIR` as `VHDL_GEN_DIR` overrides the main dir),
  4 coverage audit — any `.vhd` in the golden dir not
  listed in the gate fails as `UNCOVERED GOLDEN` (`vhdl_golden_match_uncovered`).
  `--selftest` is the deliberate-red arm (mutates a copy; the gate must FAIL).
- `sh scripts/check/check-vhdl-gen-probes.shs` — runs EVERY probe under
  `test/01_unit/lib/hardware/vhdl_gen/`, discovered by glob. Fail-closed:
  non-zero exit, any `FAIL ` line, zero `PASS ` lines, or a missing `ALL PASS`
  banner all fail. `vhdl_gen_probes_{total,pass,fail,ok}`; currently 8 probes /
  72 checks. `--selftest` proves it can go red.
- `sh scripts/check/check-riscv-rtl-truth.shs` — clean at HEAD:
  `riscv_rtl_truth_ok=true`, `generated_real=8`, `unknown=0`, zero violations.
- Pin file: `doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt`
  (56 sha256 pins: 30 under `examples/09_embedded/fpga_riscv/rtl/`, the 5
  out-of-tree goldens, 21 under `src/lib/hardware/debug/`).

## Silicon evidence (2026-07-26)

SimpleOS booted on a REAL KV260 (xck26) on BOTH rv32 and rv64, from bitstreams
built out of the GENERATED cores — staged via the new env-overridable
`RTL_DIR="${RTL_DIR:-examples/09_embedded/fpga_riscv/rtl}"` line in the DDR
build scripts (`build/fpga/rtl_gen_rv32/`, `rtl_gen_rv64/`; `examples/`
untouched). See `## lane6 silicon evidence` in `.spipe/vhdl-gen-backend/state.md`
and commit `edcd2bcf9810`. Artifacts:
`build/test-artifacts/vhdl_gen_silicon_evidence_2026-07-26/`.

## Scope limit — deliberately NOT generated

`examples/09_embedded/fpga_riscv/rtl/` is now fully generated (30/30), so the
old "only the exec cores" caveat is retired. Three things stay hand-written **on
purpose** — do not "finish the job":

- `core64_imac_product_entry_stub.vhd` (in
  `test/01_unit/lib/hardware/fpga_linux/rv64_product_wb_axi_ghdl/`) — entity
  `core64_imac_product_entry`, basename contains `core`, only `case` is
  `case state is`, so the truth gate reads `decode_present=0`. Generating it
  would give the generator the ability to MINT FAKE CPUs with generated
  provenance — exactly what `check-riscv-rtl-truth.shs` and
  `test/fixtures/riscv_truth/fake_*.vhd` exist to catch.
- `examples/09_embedded/vhdl/simulation/bounded_loop_example.vhd` — hand-written
  reference fixture of the compiler `--backend=vhdl` lane, zero consumers, and
  it does not even analyse (`ceil`/`log2`/`real` with no `use ieee.math_real`).
- The 21 JTAG transport files in `src/lib/hardware/debug/` — pinned in the
  manifest, so drift is still caught without generating them.

Claim precisely: "the fpga_riscv RTL set is generated", never "all RTL".

## Landmines

- **Timing parity trap.** rv32-DDR reports `IMPL_WNS=-0.115377` /
  TIMING_NOT_MET — but the retained GOLDEN-RTL build log
  `build/fpga/k26_rv32_ddr/vivado_1302320.backup.log` has the IDENTICAL WNS/WHS.
  Identical RTL gives an identical implementation result. ALWAYS diff the
  retained golden build log before calling timing a generator regression.
- **Board bring-up:** a wedged PS zero-fetch (`AXI_READS=0`, UART silent) is
  cleared by xsdb `targets PSU; rst -system`. Use `hw_server`, NOT openocd.
- **`.len()` counts BYTES, indexing counts CHARS.** They disagree the moment
  text is non-ASCII: an em dash in the `tb_rv32_payload` header ran an index
  loop past the end. Use `split` or a char-index loop over generated/golden
  text, never `for i in 0..s.len()` with `s[i]`. See the recorded note in
  `test/01_unit/lib/hardware/vhdl_gen/probe_tb_oneoff_gen.spl`.
- **Negative and fake RTL fixtures must stay hand-authored.** The moment the
  generator can emit a decode-free "core", the truth gate's `generated-real`
  verdict stops meaning anything. Deleting-by-generating a negative fixture is a
  regression even when every gate stays green.
- **A hardcoded file list in a gate is how a real RTL file stayed invisible for
  weeks.** `tb_rv32_nvme_bram_soc.vhd` was live at origin, unpinned and
  ungenerated, and a stray local deletion went unnoticed. Prefer glob discovery
  (as `check-vhdl-gen-probes.shs` does); where a list is unavoidable, back it
  with a coverage audit (golden-match Layer 4).
- **Never stage the 5 out-of-tree-golden files into `build/os/rtl/`.** They
  instantiate companions that live only in their own golden dirs, and the truth
  gate scans that directory as one lane — flat staging yields spurious
  `wrapper instantiates undefined entity`. Keep them in
  `build/os/rtl_external/`; fix the staging, never suppress the check.
- Generator-side language landmines live in the layer expert:
  [`layer_expert/hardware_rtl`](../../layer_expert/hardware_rtl/skill.md).

## Update Rule

After any change to the generator, the aspect, the goldens, or the pin manifest,
refresh this skill with the new gate output and evidence links — and re-run
`check-vhdl-golden-match.shs --require-generated` before claiming parity.

## Compiler HWIR boundary

This feature expert owns `src/lib/hardware/vhdl_gen`, not compiler Gen2 HWIR.
The typed mixed sequential compiler boundary is documented by
[`layer_expert/compiler_hwir`](../../layer_expert/compiler_hwir/skill.md),
`doc/07_guide/hardware/riscv/vhdl_exec_core_generator.md`, and
`.spipe/riscv_gen2_hwir_foundation/state.md`. Do not copy its typed datapath or
sequential validation into this generator, and do not use golden-text parity as
a substitute for its self-hosted and generated-VHDL/GHDL receipts.
