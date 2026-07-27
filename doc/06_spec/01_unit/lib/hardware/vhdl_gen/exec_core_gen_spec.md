# Exec-Core VHDL Generator (rv32/rv64 silicon lanes)

> RISC-V exec cores used to be six hand-maintained `.vhd` files. Every change to the instruction decode, the CSR read mux, or the JTAG debug taps had to be re-typed into all six, and the rv32 and rv64 copies drifted apart. The structured VHDL generator in `src/lib/hardware/vhdl_gen/` replaces that copy work: one pure-Simple template source emits all six silicon-lane cores, and the acceptance bar is that the emitted text is **byte-identical** to the proven goldens already sitting in `examples/09_embedded/fpga_riscv/rtl/`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exec-Core VHDL Generator (rv32/rv64 silicon lanes)

RISC-V exec cores used to be six hand-maintained `.vhd` files. Every change to the instruction decode, the CSR read mux, or the JTAG debug taps had to be re-typed into all six, and the rv32 and rv64 copies drifted apart. The structured VHDL generator in `src/lib/hardware/vhdl_gen/` replaces that copy work: one pure-Simple template source emits all six silicon-lane cores, and the acceptance bar is that the emitted text is **byte-identical** to the proven goldens already sitting in `examples/09_embedded/fpga_riscv/rtl/`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #vhdl-gen-exec-core |
| Category | Tooling |
| Status | Implemented |
| Requirements | doc/02_requirements/hardware/vhdl_golden.md |
| Plan | doc/03_plan/hardware/riscv/vhdl_exec_core_generator_plan.md |
| Design | doc/05_design/hardware/riscv/vhdl_exec_core_generator_design.md |
| Research | doc/01_research/hardware/riscv/python_rtl_generation_survey_2026-07-26.md |
| Source | `test/01_unit/lib/hardware/vhdl_gen/exec_core_gen_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

RISC-V exec cores used to be six hand-maintained `.vhd` files. Every change to
the instruction decode, the CSR read mux, or the JTAG debug taps had to be
re-typed into all six, and the rv32 and rv64 copies drifted apart. The
structured VHDL generator in `src/lib/hardware/vhdl_gen/` replaces that copy
work: one pure-Simple template source emits all six silicon-lane cores, and the
acceptance bar is that the emitted text is **byte-identical** to the proven
goldens already sitting in `examples/09_embedded/fpga_riscv/rtl/`.

Byte-identity is the whole point. These goldens are not aspirational RTL — they
are the cores that boot SimpleOS in GHDL simulation and on real KV260 silicon.
Requiring an exact byte match means adopting the generator changes nothing
electrically: the same bitstream, the same timing closure, the same board
transcript. A single differing character is a failed run, not a formatting nit.

Hardware engineers regenerate the cores before an FPGA build; compiler and OS
engineers regenerate them after touching the decode tables; CI regenerates them
on every push and fails the build if any core drifts from its golden.

## Who Uses This

| Audience | What they do with it |
|----------|----------------------|
| FPGA engineer | Regenerates cores into `build/os/rtl/` before a Vivado bitstream build |
| RISC-V core author | Edits an opcode arm or CSR case once; all lanes inherit it |
| OS / firmware engineer | Repoints `.mem` init files at a build-local firmware directory |
| CI / release gate | Proves generated equals golden, and that the RTL is generator-real |

## The Six Silicon Lanes

| Core | Shape | Where it runs |
|------|-------|---------------|
| `rv32_exec_core.vhd` | Base core | Shared decode / CSR reference lane |
| `rv64_exec_core.vhd` | Base core | Shared decode / CSR reference lane |
| `rv32_exec_core_flat.vhd` | Full-RAM behavioral | GHDL boot-tiny and NVMe firmware testbenches |
| `rv64_exec_core_flat.vhd` | Full-RAM behavioral | GHDL boot-tiny and NVMe firmware testbenches |
| `rv32_exec_core_axi.vhd` | Synthesizable AXI master | KV260 SoC top, real silicon |
| `rv64_exec_core_axi.vhd` | Synthesizable AXI master | KV260 SoC top, real silicon |

## Key Concepts

| Concept | Description |
|---------|-------------|
| Golden match | Generated text must equal the proven `.vhd` byte-for-byte; length first, then content |
| Structured, not blob | Ports, generics, constants, decode arms and CSR cases come from typed descriptor arrays, not embedded text dumps |
| Descriptor types | `VgPort`, `VgArm`, `VgCsr`, `VgMemInit`, `VgCoreGeometry`, `VgGenericSpec`, `VgPortSpec` |
| Literal sections | Irreducible per-core paragraphs live in named section functions, so the reader can still find any line of RTL by name |
| `XlenConfig` | 32-vs-64 templating is a runtime value (`XlenConfig.rv32()` / `.rv64()`) because Simple has no const generics |
| Debug aspect | `dbg_*` taps are AOP advice woven at named join points (ports, signals, assigns, process_taps), default ON |
| `.mem` prefix | An optional directory prefix rewritten into every memory-init and ramdisk file reference |
| Determinism | Arrays only, never Dict iteration, so two runs are byte-identical |

## Syntax

Regenerate every core from the command line. Output lands in `build/os/rtl/`;
`examples/` is never written:

```sh
sh scripts/fpga/generate_exec_core_vhdl.shs
sh scripts/fpga/generate_exec_core_vhdl.shs --mem-prefix build/fw/ --out-dir build/os/rtl
```

Or call the library directly. Every entry point returns the finished VHDL as
text, so callers compare or write it themselves:

```simple
use lib.hardware.riscv_common.xlen.XlenConfig
use lib.hardware.vhdl_gen.exec_core_gen.generate_exec_core
use lib.hardware.vhdl_gen.exec_core_variant_gen.generate_exec_core_flat

val base32 = generate_exec_core(XlenConfig.rv32(), "", true)
val flat64 = generate_exec_core_flat(XlenConfig.rv64(), "build/fw/")
```

## Examples

**Prove a regenerated core against its golden.** Generate, then compare against
the shipped `.vhd`. Any difference at all is a failure:

```simple
val generated = generate_rv32_exec_core("")
val golden = rt_file_read_text("examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd")
assert_true(generated == golden)
```

**Retarget the firmware images.** A flat core normally loads `rv32_flat.mem`
from the simulator's working directory. A prefix moves both the RAM image and
the ramdisk without editing RTL by hand:

```simple
val core = generate_exec_core_flat(XlenConfig.rv32(), "/tmp/fw/")
assert_true(core.contains("is \"/tmp/fw/rv32_flat.mem\";"))
```

**Strip the JTAG taps.** Passing `false` for the debug aspect removes every
`dbg_*` port and the debug UART handshake, for a lean synthesis run:

```simple
val lean = generate_exec_core(XlenConfig.rv32(), "", false)
assert_false(lean.contains("dbg_reg_addr"))
```

## How the Cores Are Built

Roughly one line in six of a base core is emitted structurally — the entity,
port and generic lists from `VgPort` / `VgPortSpec` descriptor arrays, the
geometry constants from `XlenConfig` plus `VgCoreGeometry`, the `init_rom` /
`init_data_rom` / `init_mem` impure functions from `VgMemInit`, the top-level
instruction-decode `when` arms from an opcode table of `VgArm`, the CSR
read-mux cases from a `VgCsr` table, and every `dbg_*` tap from the debug
aspect. The remaining lines are irreducible per-core logic paragraphs held as
named literal sections, which keeps the diff against a golden readable.

The flat and axi variants are siblings of each other rather than of the base:
they share large `fa##` paragraph sections, add variant-only literals, and
reuse base decode arms where those are byte-identical after reindenting.

The TAP, DTM, DMI and DM blocks are **not** generated — they stay hand-written
RTL under `src/lib/hardware/debug/`. The generator only weaves the core-side
`dbg_*` taps that connect to them.

## Acceptance Gates

| Gate | Command | What it proves |
|------|---------|----------------|
| Golden byte-match | `sh scripts/check/check-vhdl-golden-match.shs --require-generated` | All six generated cores equal the pinned manifest goldens |
| Deliberate red | `sh scripts/check/check-vhdl-golden-match.shs --selftest` | The gate actually fails on a mutated core, so a pass means something |
| RTL truth | `sh scripts/check/check-riscv-rtl-truth.shs` | All six lanes classify as `generated-real`, not hand-maintained |

The pinned golden manifest is
`doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt`.

## Proven Downstream

The generated cores are not simulation-only. GHDL SimpleOS boot and NVMe
firmware gates run on them, and KV260 (xck26) bitstreams built from the
generated `*_axi` cores booted SimpleOS on physical silicon for both rv32 and
rv64 — reaching `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED` on the serial
transcript. See `## lane6 silicon evidence` in `.spipe/vhdl-gen-backend/state.md`
for core and bitstream digests, build commands, and board markers.

## Troubleshooting

| Symptom | Likely cause | Fix |
|---------|--------------|-----|
| Golden match fails on one core only | A literal section was edited without updating its golden | Diff the generated file against the golden; the section name in the surrounding text names the function to fix |
| Golden match fails on a testbench, not a core | Uncommitted parallel-lane edit to a `tb_*.vhd` | Regenerate the pinned manifest in the lane that owns the testbench edit |
| Two runs differ | Dict iteration crept into the emitter | Replace it with an ordered array; the generator must never iterate a Dict |
| Simulator cannot open `rv32_flat.mem` | Firmware images are not in the simulator working directory | Regenerate with `--mem-prefix` pointing at the firmware directory |
| Synthesis complains about unconnected `dbg_*` ports | Debug aspect left ON without a TAP instance | Pass `false` for the aspect, or wire the hand-written TAP from `src/lib/hardware/debug/` |

## Related Specifications

- `test/01_unit/lib/hardware/vhdl_gen/probe_exec_core_gen.spl` — standalone probe lane that prints `EXEC_CORE_GEN PROBE: ALL PASS`
- `doc/04_architecture/hardware/vhdl/vhdl_hardware_subset_contract.md` — the VHDL subset the emitted cores must stay inside
- `doc/04_architecture/hardware/vhdl/vhdl_support_matrix.md` — feature support across the VHDL toolchain

## Scenarios

### Exec-core VHDL generator

#### emits rv32_exec_core byte-identical to the golden

- Run the generator for the rv32 base lane with no firmware directory prefix
- Load the proven rv32_exec_core.vhd golden shipped under examples
- Then matches golden


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the generator for the rv32 base lane with no firmware directory prefix")
val generated = generate_rv32_text()
step("Load the proven rv32_exec_core.vhd golden shipped under examples")
val golden = read_golden(RV32_GOLDEN_PATH)
Then_matches_golden(generated, golden)
```

</details>

#### emits rv64_exec_core byte-identical to the golden

- Run the generator for the rv64 base lane with no firmware directory prefix
- Load the proven rv64_exec_core.vhd golden shipped under examples
- Then matches golden


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the generator for the rv64 base lane with no firmware directory prefix")
val generated = generate_rv64_text()
step("Load the proven rv64_exec_core.vhd golden shipped under examples")
val golden = read_golden(RV64_GOLDEN_PATH)
Then_matches_golden(generated, golden)
```

</details>

#### drops every JTAG debug tap when the debug aspect is switched off

- Generate the rv32 and rv64 base cores with the debug aspect off
- Then debug taps are absent
- Then debug taps are absent
- Generate the rv32 core again with the debug aspect back on
- Then debug taps are woven in


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the rv32 and rv64 base cores with the debug aspect off")
val off32 = generate_exec_core(XlenConfig.rv32(), "", false)
val off64 = generate_exec_core(XlenConfig.rv64(), "", false)
Then_debug_taps_are_absent(off32)
Then_debug_taps_are_absent(off64)
step("Generate the rv32 core again with the debug aspect back on")
val on32 = generate_exec_core(XlenConfig.rv32(), "", true)
Then_debug_taps_are_woven_in(on32)
```

</details>

#### produces the same base cores on every run

- Generate the rv32 base core twice in the same session
- Then both runs are identical
- Generate the rv64 base core twice in the same session
- Then both runs are identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the rv32 base core twice in the same session")
val a32 = generate_rv32_text()
val b32 = generate_rv32_text()
Then_both_runs_are_identical(a32, b32)
step("Generate the rv64 base core twice in the same session")
val a64 = generate_rv64_text()
val b64 = generate_rv64_text()
Then_both_runs_are_identical(a64, b64)
```

</details>

### Exec-core VHDL generator — flat/axi variants

#### emits rv32_exec_core_flat byte-identical to the golden

- Run the generator for the rv32 flat testbench lane
- Then matches golden


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the generator for the rv32 flat testbench lane")
val generated = generate_exec_core_flat(XlenConfig.rv32(), "")
val golden = read_golden(RV32_FLAT_GOLDEN_PATH)
Then_matches_golden(generated, golden)
```

</details>

#### emits rv64_exec_core_flat byte-identical to the golden

- Run the generator for the rv64 flat testbench lane
- Then matches golden


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the generator for the rv64 flat testbench lane")
val generated = generate_exec_core_flat(XlenConfig.rv64(), "")
val golden = read_golden(RV64_FLAT_GOLDEN_PATH)
Then_matches_golden(generated, golden)
```

</details>

#### emits rv32_exec_core_axi byte-identical to the golden

- Run the generator for the rv32 synthesizable AXI silicon lane
- Then matches golden


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the generator for the rv32 synthesizable AXI silicon lane")
val generated = generate_exec_core_axi(XlenConfig.rv32())
val golden = read_golden(RV32_AXI_GOLDEN_PATH)
Then_matches_golden(generated, golden)
```

</details>

#### emits rv64_exec_core_axi byte-identical to the golden

- Run the generator for the rv64 synthesizable AXI silicon lane
- Then matches golden


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the generator for the rv64 synthesizable AXI silicon lane")
val generated = generate_exec_core_axi(XlenConfig.rv64())
val golden = read_golden(RV64_AXI_GOLDEN_PATH)
Then_matches_golden(generated, golden)
```

</details>

#### produces the same variant cores on every run

- Generate the rv32 flat core twice in the same session
- Then both runs are identical
- Generate the rv64 AXI core twice in the same session
- Then both runs are identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the rv32 flat core twice in the same session")
val f1 = generate_exec_core_flat(XlenConfig.rv32(), "")
val f2 = generate_exec_core_flat(XlenConfig.rv32(), "")
Then_both_runs_are_identical(f1, f2)
step("Generate the rv64 AXI core twice in the same session")
val x1 = generate_exec_core_axi(XlenConfig.rv64())
val x2 = generate_exec_core_axi(XlenConfig.rv64())
Then_both_runs_are_identical(x1, x2)
```

</details>

#### points flat RAM and ramdisk loads at the firmware directory the operator names

- Generate the rv32 flat core with the firmware directory /tmp/fw/
- Then flat images use prefix
- Generate the rv64 flat core with the same firmware directory
- Then flat images use prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the rv32 flat core with the firmware directory /tmp/fw/")
val p32 = generate_exec_core_flat(XlenConfig.rv32(), "/tmp/fw/")
val ram32 = "is \"/tmp/fw/rv32_flat.mem\";"
val disk32 = "file_open(fstatus, f, \"/tmp/fw/rv32_ramdisk.mem\", read_mode);"
Then_flat_images_use_prefix(p32, ram32, disk32)
step("Generate the rv64 flat core with the same firmware directory")
val p64 = generate_exec_core_flat(XlenConfig.rv64(), "/tmp/fw/")
val ram64 = "is \"/tmp/fw/rv64_flat.mem\";"
val disk64 = "file_open(fstat, f, \"/tmp/fw/rv64_ramdisk.mem\", read_mode);"
Then_flat_images_use_prefix(p64, ram64, disk64)
```

</details>

### Exec-core VHDL generator edge cases

<details>
<summary>Advanced: rewrites the base memory-init images only when a prefix is given</summary>

#### rewrites the base memory-init images only when a prefix is given

- Generate the rv32 base core with the firmware directory /tmp/fw/
- Then base images use prefix
- Then default images stay relative


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the rv32 base core with the firmware directory /tmp/fw/")
val prefixed = generate_exec_core(XlenConfig.rv32(), "/tmp/fw/", true)
val payload_image = "is \"/tmp/fw/rv32_payload.mem\";"
val fat32_image = "is \"/tmp/fw/rv32_fat32.mem\";"
Then_base_images_use_prefix(prefixed, payload_image, fat32_image)
val plain = generate_rv32_text()
Then_default_images_stay_relative(plain)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/hardware/vhdl_golden.md`
- **Plan:** `doc/03_plan/hardware/riscv/vhdl_exec_core_generator_plan.md`
- **Design:** `doc/05_design/hardware/riscv/vhdl_exec_core_generator_design.md`
- **Research:** `doc/01_research/hardware/riscv/python_rtl_generation_survey_2026-07-26.md`


</details>
