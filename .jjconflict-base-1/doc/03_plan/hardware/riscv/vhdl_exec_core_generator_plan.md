# VHDL Exec-Core Generator Plan (vhdl-gen-backend campaign)

**Date:** 2026-07-26 · **Status:** Active — Task 1 (generator lane) LANDED
`caee5b14a00b` (byte-diff 0 both cores, truth gate `generated_real=2`) ·
**Design:** `doc/05_design/hardware/riscv/vhdl_exec_core_generator_design.md`

Predecessor `doc/03_plan/hardware/pure_simple_vhdl_riscv_gap_spawn_plan.md` is
COMPLETE (compiler-backend lane). This plan covers the structured exec-core
generator lane (b). Docs-only decisions are fixed in the design doc; tasks
below implement them. Do not re-litigate lane split, eDSL style, or gate set.

## Task 1 — Generator + debug tap aspect — LANDED (caee5b14a00b)

Build `src/lib/hardware/vhdl_gen/`: single `XlenConfig`-parameterized template
source emitting `rv32_exec_core.vhd` and `rv64_exec_core.vhd` into
`build/os/rtl/`. Method-chaining eDSL, array-driven deterministic emission
(no Dict iteration), `debug_tap_aspect` module weaving taps at named generator
join points. TAP/DTM/DMI/DM remain hand-written in `src/lib/hardware/debug/`.

**Acceptance:** both cores regenerate from one template source; byte diff 0 vs
`examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd` and
`rv64_exec_core.vhd`; GHDL analyze/elaborate clean on both; taps only appear
when the aspect is enabled and output stays byte-identical when disabled.
**Evidence:** landed `caee5b14a00b` — byte-diff 0 on both cores; rtl-truth
gate reports `generated_real=2`.

## Task 2 — Gates

Add `scripts/check/check-vhdl-golden-match.shs` with golden manifest
`doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt`; wire the
generated lane (`build/os/rtl/`) into existing
`scripts/check/check-riscv-rtl-truth.shs`.

**Acceptance:** gate exits 0 on clean regen; deliberate-red — mutating one
decode-table entry in the generator makes byte-diff AND a GHDL testbench fail;
restoring it returns green; manifest lists every generated file with hash.

## Task 3 — Docs

Land design + TLDR (this campaign's task #3, done), refresh the compiler
design doc cross-reference, and update the related LLM wiki feature/layer
expert entries alongside the code commits (per vcs rule).

**Acceptance:** design doc ≤120 lines new content with diagram; `_tldr.md`
≤30 lines + diagram; `VHDL_BACKEND_DESIGN.md` carries a dated two-lane
cross-reference section; wiki entries updated in the same change as Task 1/2.

## Task 4 — flat/axi variant coverage

Extend the generator to emit `rv32_exec_core_flat.vhd`,
`rv64_exec_core_flat.vhd`, `rv32_exec_core_axi.vhd`, `rv64_exec_core_axi.vhd`
from the same template source; add them to the golden manifest.

**Acceptance:** byte diff 0 vs all four goldens in
`examples/09_embedded/fpga_riscv/rtl/`; `check-vhdl-golden-match.shs` covers
all six cores; deliberate-red still trips on every variant.

## Task 5 — SimpleOS + NVMe GHDL evidence

Run the existing GHDL SimpleOS-boot and NVMe-fw testbench harnesses against
the *generated* cores (not the goldens) from `build/os/rtl/`.

**Acceptance:** SimpleOS-boot GHDL harness green on generated rv32 and rv64
cores; NVMe-fw rv32 testbench green on generated core; evidence logs recorded
under `doc/08_tracking/hardware/`. **Board lane:** BLOCKED on 3.3V PMOD UART
adapter (AC-4/AC-11) — explicit blocker per `.claude/rules/board-runnable.md`;
board evidence is out of scope until the adapter is available and must not be
implied by GHDL green.
