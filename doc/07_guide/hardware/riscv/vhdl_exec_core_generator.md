# VHDL Exec-Core Generator (operator guide)

Date: 2026-07-26 · Status: **generated cores silicon-proven on KV260**

Operator guide for the pure-Simple structured VHDL generator in
`src/lib/hardware/vhdl_gen/`. It emits the six silicon-lane RISC-V exec cores
byte-identical to the proven goldens in `examples/09_embedded/fpga_riscv/rtl/`,
from one shared template parameterized by `XlenConfig`.

## Not to be confused with the compiler VHDL backend

There are **two** VHDL generation lanes. This guide covers lane (b) only.

| Lane | Location | Input | Status |
|---|---|---|---|
| (a) Compiler VHDL backend | `src/compiler/70.backend/backend/vhdl*`, driven by `bin/simple compile --backend=vhdl` | `@hardware fn` Simple source | `contract-not-ready` — see [`simple_generated_fpga_rtl.md`](simple_generated_fpga_rtl.md) |
| (b) Structured exec-core generator (this guide) | `src/lib/hardware/vhdl_gen/` | one `XlenConfig`-parameterized template source | six cores, byte diff 0 vs goldens, booted on silicon |

Do not mix them. Lane (a) tries to compile Simple semantics into a CPU; lane (b)
is a structured emitter whose acceptance bar is byte-equality with the
already-silicon-tested RTL, so the RTL cannot drift while it becomes generated.

See also: [`riscv_guide.md`](riscv_guide.md),
[`../fpga/simpleos_on_simple_riscv_fpga.md`](../fpga/simpleos_on_simple_riscv_fpga.md),
[`../fpga/kv260_rv64gc_fpga_boot.md`](../fpga/kv260_rv64gc_fpga_boot.md).

## Quick start

```bash
sh scripts/fpga/generate_exec_core_vhdl.shs
sh scripts/check/check-vhdl-golden-match.shs
```

Generation is the **default** expectation: the gate fails if any pinned RTL file
is missing from `build/os/rtl/`. Pass `--allow-missing` to opt out (missing is
then reported as `not-generated` instead of failing). `--require-generated` is
still accepted as a no-op, since that is now the default.

The first command writes all 29 `.vhd` files into `build/os/rtl/`; the second
proves each is byte-identical to its golden and that no golden has drifted from
its pinned hash.

## What gets generated

One driver run emits all six cores into `build/os/rtl/`:

| File | Variant | Consumed by |
|---|---|---|
| `rv32_exec_core.vhd` | base | GHDL NVMe-fw smoke, WB SoC |
| `rv64_exec_core.vhd` | base | GHDL WB SoC |
| `rv32_exec_core_flat.vhd` | flat (full-RAM behavioral) | GHDL boot-tiny / NVMe-fw testbenches |
| `rv64_exec_core_flat.vhd` | flat | GHDL SimpleOS boot testbenches |
| `rv32_exec_core_axi.vhd` | axi (synthesizable AXI-master-shaped) | `soc_top_rv32_k26_ddr`, tiny-BRAM SoC |
| `rv64_exec_core_axi.vhd` | axi | `soc_top_rv64_k26_ddr` |

Roughly 16% of the base-core output lines are structurally generated (entity /
ports / generics from `VgPort` descriptor arrays, constants from
`XlenConfig` + `VgCoreGeometry`, `regs_t`/`state_t` types, memory-init impure
functions from `VgMemInit`, concurrent assigns, opcode decode `when` arms from
`VgArm` tables, CSR read-mux cases from `VgCsr` tables, and every `dbg_*` tap).
The remaining ~84% is irreducible per-core logic held as named literal section
functions. For the flat/axi variants, 68.2% of the 3627 golden lines come from
sections shared with another core.

Emission is **deterministic**: arrays only, never Dict iteration (Dict key order
is randomised per process). Two runs are byte-identical.

## Source layout

| File | Role |
|---|---|
| `__init__.spl` | module exports |
| `gen_types.spl` | emitter primitives: `VgGeneric`/`VgPort`/`VgAssign`/`VgConst`/`VgArm`/`VgCsr`/`VgMemInit`/`VgCoreGeometry`/`VgGenericSpec`/`VgPortSpec` plus `emit_entity`, `emit_entity_spec`, `emit_constants`, `emit_mem_init`, `emit_assigns`, `emit_decode_case`, `emit_csr_read_case`, `vg_reindent` |
| `exec_core_gen.spl` | base-core assembly; public `generate_exec_core(cfg, mem_prefix, debug_taps)` |
| `rv32_sections.spl` / `rv64_sections.spl` | 26 + 20 named literal paragraphs for the base cores |
| `exec_core_variant_gen.spl` | variant assembly; `generate_exec_core_flat(cfg, mem_prefix)`, `generate_exec_core_axi(cfg)` |
| `rv32_variant_sections.spl` / `rv64_variant_sections.spl` | `fa##` sections shared flat↔axi, `fl##`/`ax##` variant-only literals |
| `debug_tap_aspect.spl` | AOP debug-tap advice at named join points |
| `generate_main.spl` | CLI entry used by the driver script |

## Driver script

```bash
sh scripts/fpga/generate_exec_core_vhdl.shs [--mem-prefix DIR/] [--out-dir DIR]
```

It `cd`s to the repo root, creates `build/os/rtl`, and runs
`bin/simple run src/lib/hardware/vhdl_gen/generate_main.spl` with your flags.

| Flag | Default | Meaning |
|---|---|---|
| `--mem-prefix <dir/>` | `""` (golden's relative form, e.g. `rv32_payload.mem`) | Path prefix prepended to the `.mem` filenames in `init_rom` / `init_data_rom` / `init_mem` / `init_ram` / `init_rdisk` and the flat cores' `file_open` ramdisk reference. Use it when a simulator runs from a different working directory. **The axi cores read no `.mem` files**, so this flag does not affect them. Any non-empty prefix necessarily breaks byte-equality with the goldens — that is expected and intended. |
| `--out-dir <dir>` | `build/os/rtl` | Output directory. |

There are no other flags. Success prints one `VHDL_GEN: wrote <path>` line per
core followed by `VHDL_GEN: OK`; a write failure prints
`VHDL_GEN: FAILED (write error)`.

`build/os/rtl/` is one of the lane roots scanned by
`scripts/check/check-riscv-rtl-truth.shs`, and the emitted cores contain real
opcode decode, so they classify **`generated-real`** rather than
`generated-contract`.

## 64/32 templating with `XlenConfig`

Simple has no const generics, so XLEN is an ordinary **runtime value**:
`XlenConfig` (`src/lib/hardware/riscv_common/xlen.spl`, imported as
`std.hardware.riscv_common.xlen.XlenConfig`) is a struct carrying `xlen`,
`mask`, `sign_bit`, `bytes_per_reg`, `cause_interrupt_bit`, constructed by
`XlenConfig.rv32()` / `XlenConfig.rv64()` and queried with `is_rv32()` /
`is_rv64()`. Elaboration is just Simple code running at generation time, so a
plain `if cfg.is_rv32():` is the whole mechanism.

**To add an XLEN-dependent difference**, in increasing order of preference:

1. **Derive it from a field.** Port and signal widths should come from
   `cfg.xlen` (e.g. `dbg_slv(cfg.xlen - 1)` in `debug_tap_aspect.spl`), never
   from a literal 31/63. This is the only form that stays correct if a third
   width is ever added.
2. **Put it in the geometry/descriptor table.** Per-core facts that are not
   arithmetic in XLEN (entity name, alignment style, case indent, memory sizes)
   belong in `rv32_geometry()` / `rv64_geometry()` (`VgCoreGeometry`) or in the
   `rv32_consts` / `rv64_consts` `VgConst` arrays, not in an `if`.
3. **Branch on `cfg.is_rv32()`** inside a single emitter when the two cores
   genuinely diverge in *structure* — e.g. `rv32_opcode_arms` vs
   `rv64_opcode_arms`, or the rv32-only `PROCESS_TAPS` advice.
4. **Add a named literal section** in `rv32_sections.spl` / `rv64_sections.spl`
   (or the `*_variant_sections.spl` pair) only for irreducible logic paragraphs.
   Never fork a whole shared section to change a few lines; if two cores need a
   shifted copy of the same block, use `vg_reindent` (the rv64 variants reuse
   the base decode arms shifted `+2`).

Whatever you change, the acceptance bar is unchanged: re-run the driver and the
golden-match gate, and get byte diff 0 on all six cores.

## AOP JTAG debug taps

`debug_tap_aspect.spl` holds **all** `dbg_*` / `debug_*` tap emission as advice
functions invoked at four named generator join points:

| Join point | Advice | Emits |
|---|---|---|
| PORTS | `dbg_tap_ports(cfg, enabled)` | `debug_uart_valid`, `debug_uart_byte`, rv32-only `debug_pc`/`debug_ins`/`debug_a0`/`debug_ra`/`debug_sp`/`debug_phase`, plus `dbg_reg_addr` (in, defaulted `(others => '0')`), `dbg_reg_data`, `dbg_pc` |
| SIGNALS | `dbg_tap_signal_lines(cfg, enabled)` | the `*_q` tap registers |
| ASSIGNS | `dbg_tap_assigns(cfg, enabled)` | read-only concurrent taps of `regs_q` / `pc_q` |
| PROCESS_TAPS | `dbg_tap_process_lines(cfg, enabled)` | in-process debug register updates (**rv32 only**; rv64 returns no lines) |

The `dbg_reg_addr` input has a safe default, so existing instantiations that
ignore it stay byte-identical, and the outputs are pure read-only taps that
cannot perturb execution.

**Default ON.** The goldens contain the taps, so byte-match *requires* enabled.
Turn them off via the third argument of `generate_exec_core`:

```simple
generate_exec_core(XlenConfig.rv32(), "", false)   # taps off — diagnostic only
```

OFF mode is diagnostic-only: the literal core paragraphs still reference
`debug_*` signals, so OFF output is not meant to be analyzed or simulated. The
driver always passes `true`. The variant generators
(`generate_exec_core_flat` / `generate_exec_core_axi`) take no tap flag.

**TAP / DTM / DMI / Debug-Module RTL is NOT generated here.** Those stay
hand-written, fail-closed VHDL in `src/lib/hardware/debug/` (`jtag_tap.vhd`,
`riscv_dtm.vhd`, `dmi_bus.vhd`, `riscv_debug_module.vhd`, …). AOP is only for
hart join points — mirroring the philosophy of
`src/lib/hardware/debug_hooks/hart_debug.spl`.

## Gates

### Golden match

```bash
sh scripts/check/check-vhdl-golden-match.shs
```

Covers all 29 pinned RTL files. Missing generated files fail by default; use
`--allow-missing` to opt out.

Two fail-closed layers:

1. **Golden drift** — every file in the manifest must still hash to its pinned
   sha256.
2. **Generated match** — each core present in the generated dir must be
   byte-identical to its same-named golden.

Without `--require-generated`, a missing generated file reports
`not-generated` and does not fail (the generator may simply not have run). With
it, missing = fail. Always pass it in CI or when making a claim.

Summary keys (always printed, one per line):

```text
vhdl_golden_match_manifest=ok|drift
vhdl_golden_match_rv32=pass|fail|not-generated
vhdl_golden_match_rv64=pass|fail|not-generated
vhdl_golden_match_rv32_flat=pass|fail|not-generated
vhdl_golden_match_rv64_flat=pass|fail|not-generated
vhdl_golden_match_rv32_axi=pass|fail|not-generated
vhdl_golden_match_rv64_axi=pass|fail|not-generated
vhdl_golden_match_ok=true|false
```

Exit `0` = all good, `1` = any fail (drift, byte mismatch, or missing under
`--require-generated`), `2` = environment problem (missing manifest or golden).

`VHDL_GEN_DIR` overrides the generated-output directory (default
`build/os/rtl`) — useful for checking a staged tree without regenerating.

### Deliberate-red self-test

```bash
sh scripts/check/check-vhdl-golden-match.shs --selftest
```

A gate that cannot fail is not a gate. `--selftest` copies the rv32 golden to a
scratch dir and proves (1) an exact copy classifies `pass`, (2) a one-byte
mutation at offset 100 classifies `fail` with non-zero exit, then repeats both
phases for `rv32_exec_core_flat.vhd`. It cleans up either way and prints
`vhdl_golden_match_selftest=ok`, exiting 0 only if the mutants were caught.

### RTL truth

```bash
sh scripts/check/check-riscv-rtl-truth.shs
```

Classifies every `.vhd` lane as `reference-handwritten` / `fixture` /
`generated-contract` / `generated-real` / `absent` and fails closed on fake-CPU
evidence (empty architecture, step-counter "core", decode-free PC incrementer,
wrapper instantiating an untracked entity). With the six cores present it
reports `riscv_rtl_truth_generated_real=6` and `riscv_rtl_truth_ok=true`.

A VIOLATION is a finding to file, never a reason to weaken the rule.

## Golden manifest and legitimate drift

`doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt` pins 50 files by
sha256: 29 under `examples/09_embedded/fpga_riscv/rtl/` and 21 under
`src/lib/hardware/debug/`. The header records the repo HEAD the pins were taken
at.

The goldens are the silicon-tested baseline. When a golden legitimately changes:

- **Regenerate the manifest pin in the same change**, and say so in the commit
  message. Do **not** hand-edit hashes ad hoc, and never "absorb" drift by
  loosening the gate.
- Add a dated note to the manifest header explaining *what* moved and *why it is
  safe*.

The header already carries the worked example:

> `2026-07-27: tb_rv64_k26_ddr_boot.vhd pin refreshed cdfad472 -> 60df8d49 for the`
> `landed commit dae8b497135 (adds the G_SKIP_BSS_ZERO generic, default false so`
> `the historical board-flow rehearsal is unchanged). Testbench only — no exec`
> `core moved, and all six generated cores still match byte-for-byte.`

Copy that shape: name the file, both hashes, the landing commit, why the change
is behaviour-preserving, and confirm whether any exec core moved.

## Feeding generated RTL into FPGA builds

Both KV260 DDR bitstream scripts take an env-overridable RTL source directory:

```sh
RTL_DIR="${RTL_DIR:-examples/09_embedded/fpga_riscv/rtl}"
```

The **default is unchanged**, and `examples/` is never written by the generator
or the build.

To build from generated cores, stage a directory containing the generated core
**plus the unmodified SoC / adapter / ctrl-slave files** (the build needs all
four sources), then point `RTL_DIR` at it:

```bash
sh scripts/fpga/generate_exec_core_vhdl.shs
mkdir -p build/fpga/rtl_gen_rv32
cp build/os/rtl/rv32_exec_core_axi.vhd build/fpga/rtl_gen_rv32/
cp examples/09_embedded/fpga_riscv/rtl/rv32_axi4_mem_adapter.vhd \
   examples/09_embedded/fpga_riscv/rtl/rv32_ctrl_obs_slave.vhd \
   examples/09_embedded/fpga_riscv/rtl/soc_top_rv32_k26_ddr.vhd \
   build/fpga/rtl_gen_rv32/
cmp build/fpga/rtl_gen_rv32/rv32_exec_core_axi.vhd \
    examples/09_embedded/fpga_riscv/rtl/rv32_exec_core_axi.vhd

RTL_DIR=build/fpga/rtl_gen_rv32 sh scripts/fpga/build_k26_rv32_ddr_bitstream.shs
```

The rv64 sibling is identical with `rv64_exec_core_axi.vhd`,
`rv64_axi4_mem_adapter.vhd`, `soc_top_rv64_k26_ddr.vhd`,
`build/fpga/rtl_gen_rv64/`, and
`scripts/fpga/build_k26_rv64_ddr_bitstream.shs` — note the ctrl-obs slave is
`rv32_ctrl_obs_slave.vhd` for **both** lanes.

Add `ALLOW_CONCURRENT_BUILD=1` only when you have already checked host capacity;
Vivado oversubscription thrashes.

Then bring up the board:

```bash
sh scripts/fpga/bringup_kv260_rv32_ddr.shs   # rv64: swap 32 -> 64
```

## Evidence achieved

Simulation gates run against staged trees where the exec cores are the
**generated** artifacts (sha256 generated == staged == golden for all six):

| Lane | Result | Marker |
|---|---|---|
| rv32 SimpleOS boot (tiny) | PASS | `RV32_TINY_BOOT_DONE reached=TEST_PASSED`, `SIMPLEOS_RISCV_SMF_FS_PASS`, stack_used=344 |
| rv32 NVMe firmware smoke | PASS | `RV32_NVME_FW_PASS`, `STATUS: PASS ghdl-rv32-nvme-fw` |
| rv64 SimpleOS K26-DDR boot | PASS | `RESULT: PASS - rv64 SimpleOS booted through the AXI4/DDR path` |

**Real silicon**, KV260 (xck26), bitstreams built from the generated cores:

| Lane | Result | Markers |
|---|---|---|
| rv32-DDR | PASS | `CTRL_MAGIC=0x52563332`, `UART_BYTE_COUNT=445`, `FINAL_PC=0x8000002A`, `SIMPLEOS_RISCV_SMF_FS_PASS` + `TEST PASSED` |
| rv64-DDR | PASS | `UART_BYTE_COUNT=546`, `FINAL_PC_LO32=0x80200028`, `SIMPLEOS_RISCV_SMF_FS_PASS` + `TEST PASSED`, Vivado `TIMING_MET` |

Full provenance — core and bitstream sha256s, build commands, bring-up logs,
timing-parity files — is in `## lane6 silicon evidence` of
`.spipe/vhdl-gen-backend/state.md`, with artifacts under
`build/test-artifacts/vhdl_gen_silicon_evidence_2026-07-26/`.

**Still blocked (accepted):** interactive UART login on the board needs a 3.3 V
PMOD adapter (AC-4/AC-11, hardware procurement) — the KV260 carrier does not
route fabric UART H12/PMOD J2 to the FT4232H. JTAG status-word and UART-capture
markers remain the accepted silicon bar, the same bar the prior golden-RTL
silicon PASSes met. Resume with `sh scripts/fpga/capture_kv260_uart_ila.shs`.

## Scope limit — what is NOT generated

The generator covers the **six exec cores only**. Of the 29 pinned RTL files in
`examples/09_embedded/fpga_riscv/rtl/`, the other **23 are still hand-written**:

- SoC tops — `soc_top_rv32.vhd`, `soc_top_rv64.vhd`, `soc_top_rv32_sim.vhd`,
  `soc_top_rv64_sim.vhd`, `soc_top_rv32_k26_ddr.vhd`, `soc_top_rv64_k26_ddr.vhd`,
  `soc_top_rv32_tiny_bram.vhd`
- AXI4 memory adapters — `rv32_axi4_mem_adapter.vhd`, `rv64_axi4_mem_adapter.vhd`
- BRAM SoC — `rv32_bram_soc.vhd`
- Control/observation slave — `rv32_ctrl_obs_slave.vhd`
- 12 testbenches (`tb_*.vhd`)

The 21 pinned files under `src/lib/hardware/debug/` (TAP, DTM, DMI, Debug
Module, and their testbenches) are also hand-written and deliberately stay that
way.

## Tests

```bash
bin/simple test test/01_unit/lib/hardware/vhdl_gen/exec_core_gen_spec.spl
bin/simple run  test/01_unit/lib/hardware/vhdl_gen/probe_exec_core_gen.spl
```

The probe prints per-stage `PASS`/`FAIL` lines and a final
`EXEC_CORE_GEN PROBE: ALL PASS` (14 PASS lines). It is the runnable evidence
lane while the deployed binary cannot run the spec (below).

## Troubleshooting

**`expected Fn, found FString` when running the spec.** Pre-existing, not a
regression in this lane: the deployed seed's `simple test` cannot parse the
`@step "..."` decorator form. HEAD fails identically. The spec in this lane is
written with the `step("...")` call form; if you reintroduce the decorator form
you will hit this again. Use `probe_exec_core_gen.spl` as the runnable evidence
lane until a self-hosted redeploy. Do not "fix" it by deleting the step labels.

**Timing looks bad on rv32-DDR — is that my change?** Almost certainly not.
rv32-DDR misses timing at `IMPL_WNS=-0.115377` / `WHS=+0.017749` and Vivado
prints `TIMING_NOT_MET`. The retained **golden-RTL** build log
(`build/fpga/k26_rv32_ddr/vivado_1302320.backup.log`) reports the *identical*
WNS/WHS, so this is pre-existing `soc_top_rv32_k26_ddr` design timing, not a
generator regression — see `rv32_ddr_timing_parity.txt` in the evidence dir.
**Always diff against the retained golden build log before calling timing a
regression.** rv64-DDR meets timing. Closing the −0.115 ns path is a tracked
follow-up, not a generator bug.

**Board bring-up: `CTRL_MAGIC` ok and loads verified, but `AXI_READS=0` and
`UART_BYTE_COUNT=0`.** This is the wedged-PS zero-fetch. Fix, applied exactly
once, then re-run the bring-up unmodified:

```tcl
# in xsdb
targets -filter {name =~ "PSU"}
rst -system
```

(Recorded verbatim from the rv64-DDR bring-up: `rv64_bringup_attempt1_wedged.log`
shows the symptom, `rv64_rst_system.log` the fix.)

**`vhdl_golden_match_ok=false` but all six core keys say `pass`.** Read the
`manifest` key — an unrelated golden (typically a testbench edited by a parallel
lane) has drifted. That is the *other* lane's manifest refresh to land, not
yours. Confirm by re-running the gate at HEAD: if it fails identically, it is
not your regression.

**Linter fires `COLL006` "string concat in loop".** Pre-existing class: the
bounded padding/joining loops this generator family deliberately uses already
trip it 14 times at HEAD in `gen_types.spl` / `generate_main.spl`. New code
follows the same landed style.

**Uncommitted generator files vanished mid-session.** A parallel `jj` session
snapshot/commit/fetch/rebase can sweep uncommitted new files. Keep scratchpad
copies of new sources until they land.

## References

- Design: `doc/05_design/hardware/riscv/vhdl_exec_core_generator_design.md`
- Plan: `doc/03_plan/hardware/riscv/vhdl_exec_core_generator_plan.md`
- Research — Python-style RTL generation survey:
  `doc/01_research/hardware/riscv/python_rtl_generation_survey_2026-07-26.md`
- Research — Simple grammar / VHDL eDSL sufficiency:
  `doc/01_research/hardware/riscv/simple_grammar_vhdl_edsl_sufficiency_2026-07-26.md`
- Campaign state and silicon evidence: `.spipe/vhdl-gen-backend/state.md`
- Golden manifest: `doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt`
