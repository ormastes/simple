# Feature Expert: Pure-Simple VHDL Exec-Core Generator

## Role

Own process knowledge for `src/lib/hardware/vhdl_gen/` — the pure-Simple
generator that EMITS the RISC-V exec cores that were previously hand-written
VHDL. It is a **structured** generator (typed descriptor arrays elaborated into
VHDL text), explicitly NOT blob embedding: no whole-file string constants, no
`.vhd` read-and-reprint. Written so the next agent does not re-litigate "is the
generated core real?" — it is silicon-proven.

## What it emits

All SIX silicon-lane cores, byte-identical to the goldens in
`examples/09_embedded/fpga_riscv/rtl/`: `rv32`/`rv64` x {base, `_flat`, `_axi`}.
Variants share ~68% of emitted lines with the base sections (state.md: 68.2% of
3627 variant-golden lines come from shared sections).

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

- `sh scripts/check/check-vhdl-golden-match.shs --require-generated` — runs the
  generator and byte-compares all 6 cores against the goldens.
  `--selftest` is the deliberate-red arm (mutates a copy; the gate must FAIL).
- `sh scripts/check/check-riscv-rtl-truth.shs` — the 6 lanes must report
  `generated-real` (not hand-written, not stub).
- Pin file: `doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt`
  (sha256 pins; 29 entries under `examples/09_embedded/fpga_riscv/rtl/` plus 21
  under `src/lib/hardware/debug/`).

## Silicon evidence (2026-07-26)

SimpleOS booted on a REAL KV260 (xck26) on BOTH rv32 and rv64, from bitstreams
built out of the GENERATED cores — staged via the new env-overridable
`RTL_DIR="${RTL_DIR:-examples/09_embedded/fpga_riscv/rtl}"` line in the DDR
build scripts (`build/fpga/rtl_gen_rv32/`, `rtl_gen_rv64/`; `examples/`
untouched). See `## lane6 silicon evidence` in `.spipe/vhdl-gen-backend/state.md`
and commit `edcd2bcf9810`. Artifacts:
`build/test-artifacts/vhdl_gen_silicon_evidence_2026-07-26/`.

## Scope limit (do not overclaim)

Only 6 of the 29 pinned RTL files are generated. SoC tops
(`soc_top_rv{32,64}*`), AXI4 memory adapters, `rv32_bram_soc.vhd`, the ctrl-obs
slave and every testbench remain hand-written. "The RTL is generated" is false;
"the exec cores are generated" is true.

## Landmines

- **Timing parity trap.** rv32-DDR reports `IMPL_WNS=-0.115377` /
  TIMING_NOT_MET — but the retained GOLDEN-RTL build log
  `build/fpga/k26_rv32_ddr/vivado_1302320.backup.log` has the IDENTICAL WNS/WHS.
  Identical RTL gives an identical implementation result. ALWAYS diff the
  retained golden build log before calling timing a generator regression.
- **Board bring-up:** a wedged PS zero-fetch (`AXI_READS=0`, UART silent) is
  cleared by xsdb `targets PSU; rst -system`. Use `hw_server`, NOT openocd.
- Generator-side language landmines live in the layer expert:
  [`layer_expert/hardware_rtl`](../../layer_expert/hardware_rtl/skill.md).

## Update Rule

After any change to the generator, the aspect, the goldens, or the pin manifest,
refresh this skill with the new gate output and evidence links — and re-run
`check-vhdl-golden-match.shs --require-generated` before claiming parity.
