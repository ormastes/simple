# VHDL Exec-Core Generator (operator guide)

Date: 2026-07-27 · Status: **generated cores silicon-proven on KV260**

Operator guide for the pure-Simple structured VHDL generator in
`src/lib/hardware/vhdl_gen/`. It emits **35 RTL files** byte-identical to the
proven goldens — the six silicon-lane RISC-V exec cores (from one shared
template parameterized by `XlenConfig`) plus the bus/memory infrastructure, the
SoC tops and the simulation testbenches that surround them.

## Not to be confused with the compiler VHDL backend

There are **two** VHDL generation lanes. This guide covers lane (b) only.

| Lane | Location | Input | Status |
|---|---|---|---|
| (a) Compiler VHDL backend | `src/compiler/70.backend/backend/vhdl*`, driven by `bin/simple compile --backend=vhdl` | `@hardware fn` Simple source | `contract-not-ready` — see [`simple_generated_fpga_rtl.md`](simple_generated_fpga_rtl.md) |
| (b) Structured exec-core generator (this guide) | `src/lib/hardware/vhdl_gen/` | typed descriptor arrays + one `XlenConfig`-parameterized core template | 35 RTL files, byte diff 0 vs goldens; cores booted on silicon |

Do not mix them. Lane (a) tries to compile Simple semantics into a CPU; lane (b)
is a structured emitter whose acceptance bar is byte-equality with the
already-silicon-tested RTL, so the RTL cannot drift while it becomes generated.

### Compiler Gen2 strict-HWIR development route

Typed sequential modules can now include a combinational HWIR datapath before
their guarded state transition plan. Construct that datapath with `HwSignal`,
`HwConstant`/`HwBitVectorConstant`, `HwCombOp`, `HwCompareOp`, `HwSelectOp`,
`HwBitExtractOp`, and `HwFixedSliceOp`; do not supply VHDL fragments. The
module validator rejects unreadable output operands, width drift, unsupported
operations, duplicate names, undriven signals, and multiple drivers. The v3
module structural hash covers every datapath field, and
`render_strict_sequential_hwir` emits declarations and combinational
assignments before output bindings and the synchronous process.

The focused contract is
`test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl`, with
its operator-readable mirror under `doc/06_spec/01_unit/compiler/50.mir/`.
Executable qualification still requires the provenance-admitted self-hosted
CLI; a bootstrap seed or a crashing deployed binary is diagnostic only.

The compiler lane now has a bounded, development-stage critical route for one
`@hardware` source function:

```bash
SIMPLE_SAFETY_PROFILE=critical simple-vhdl source.spl \
  --riscv-gen2-target rv32 --output source.vhd
```

`rv64` is the other accepted target. The selected target is elaboration data;
critical compilation snapshots the policy, lowers only the supported real-MIR
combinational subset into typed HWIR, and rejects unsupported MIR with
`HWIR-E-*` before it can reach the legacy VHDL catalog emitter. The generated
manifest records `generation_route=hwir-strict`, the HWIR node ID, and the
concrete profile. This is not an alternative path for the silicon-proven cores,
not a full RISC-V core compiler, and not release-qualified until the self-hosted
CLI and GHDL route evidence are available.

### Compiler-owned Gen2 product route

Compiler-owned Gen2 products have no user source file. Invoke a supported
product explicitly, with an output path and its stricter elaboration target:

```bash
SIMPLE_SAFETY_PROFILE=critical simple-vhdl \
  --riscv-gen2-product riscv-gen2-zca-control-predecode-v1 \
  --riscv-gen2-target rv32-zca-critical --output zca_control.vhd
```

`rv64-zca-critical` selects the corresponding RV64 graph. The enabled IDs are
`riscv-gen2-zca-control-predecode-v1`,
`riscv-gen2-zca-migrating-predecode-v1`, the RV32/RV64 specialized migrating
and stateful products listed below, and
`riscv-gen2-zca-trap-single-outstanding-v3`. The trap frontend serializes only
from its typed sequential state plan and records its decoder-closure hash. A source pathname and
`--riscv-gen2-product` are mutually exclusive. The emitted manifest preserves
the exact `generation_route`, a `compiler-product:` entry identity, and an
empty user `source_closure`; it must not be represented as a generated source
program. These are bounded frontend products, not full Zca or qualified
processor products.

The current non-trap composition is precisely a **24-ID common low-shamt
tranche**. The concrete RV32 product adds C.JAL and the concrete RV64 product
adds C.ADDIW, producing separate **25-ID product closures**. This count is not
a claim of complete Zca: the remaining high-shamt/XLEN-dependent rows and the
C.EBREAK trap row require their own typed product composition and evidence.
Every admitted row contributes an explicit `legal` or `match_legal` selector;
classifier overlap fails closed to the illegal `PC+2` tuple.

The generic raw artifact writer refuses any bundle that claims a compiler-owned
Gen2 route before removing a prior output. Product drivers use the dedicated
Gen2 writer after rebuilding and checking their typed graph/provenance. This is
an internal compiler boundary, not a cryptographic signature; the remaining
module-encapsulation requirement is tracked before release.

The v3 trap product accepts retirement only when the 64-bit lineage, original
16-bit parcel, canonical 32-bit instruction, and original-length encoding all
match the outstanding entry. Matching lineage alone is insufficient. Any valid
retirement with an identity mismatch enters sticky `protocol_fault`; only reset
recovers it. The lineage remains a development-stage bounded transaction token,
not an unbounded proof token. A terminal full-identity match faults before
increment, preventing wrap and token reuse before reset. Release still requires
a reset-coupled architectural retirement producer and successful self-hosted
RV32/RV64 VHDL/GHDL receipts. Bootstrap-seed output, including warning-truncated
test output, is diagnostic only and does not establish any of those conditions.

The added retirement identity inputs change the stateful frontend's public port
sequence and graph closure hash. The widened non-trap products therefore use
the `*-single-outstanding-v2` IDs and `hwir-gen2-stateful-product-v2` route; the
widened trap product uses `*-trap-single-outstanding-v3` and
`hwir-gen2-trap-stateful-product-v3`. The CLI rejects the retired v1/v2 product
IDs, and provenance admission does not recognize the retired unversioned
stateful routes. Existing artifacts must be regenerated; there is no compatible
in-place manifest migration. Fresh self-hosted manifest/GHDL receipts are still
required before qualification.

`riscv-gen2-zca-rv32-cjal-migrating-predecode-v1` is a separate RV32-only
product and requires `--riscv-gen2-target rv32-zca-cjal-critical`. It adds the
RV32 C.JAL parcel to the common migrating predecode graph under a concrete
`rv32i_zca` profile. The common and RV64 targets reject it because the same
parcel class is RV64 C.ADDIW. Its manifest remains `frontend-predecode-only`:

`riscv-gen2-zca-rv64-addiw-migrating-predecode-v1` is the reciprocal RV64-only
product and requires `--riscv-gen2-target rv64-zca-addiw-critical`. It admits
only C.ADDIW for that overlapping parcel class under a concrete `rv64i_zca`
profile, rejects `rd=x0`, and records a distinct capability hash. It is also
`frontend-predecode-only`; neither product is a processor or an ISA-profile
compliance claim.

The corresponding `riscv-gen2-zca-rv32-cjal-single-outstanding-v2` and
`riscv-gen2-zca-rv64-addiw-single-outstanding-v2` products retain the same
respective targets and add the bounded one-entry fetch/dispatch/retire lineage
protocol. Their manifests record the specialized decoder as a graph-hashed
dependency. They remain frontend products, not processor/profile claims.

The effectful target route closes each 25-row specialized decoder with the
explicit C.EBREAK row, for exactly 26 admitted IDs. A global ambiguity guard
rejects overlap between those partitions and clears legality, canonical output,
redirect, and trap metadata. C.JR/C.JALR register binding and redirect semantics
remain owned only by the embedded target decoder. The stateful wrapper preserves
the fetched parcel and original two-byte length through dispatch and retirement;
no runtime XLEN or extension selector is emitted. These products remain
development-stage until self-hosted and GHDL qualification receipts exist.
this is not a full RV32 core claim.

See also: [`riscv_guide.md`](riscv_guide.md),
[`../fpga/simpleos_on_simple_riscv_fpga.md`](../fpga/simpleos_on_simple_riscv_fpga.md),
[`../fpga/kv260_rv64gc_fpga_boot.md`](../fpga/kv260_rv64gc_fpga_boot.md).

## Quick start

```bash
sh scripts/fpga/generate_exec_core_vhdl.shs
sh scripts/check/check-vhdl-golden-match.shs
sh scripts/check/check-vhdl-gen-probes.shs
```

Generation is the **default** expectation: the gate fails if any pinned RTL file
is missing from `build/os/rtl/`. Pass `--allow-missing` to opt out (missing is
then reported as `not-generated` instead of failing). `--require-generated` is
still accepted as a no-op, since that is now the default.

The first command writes 30 `.vhd` files into `build/os/rtl/` and the 5
out-of-tree-golden files into `build/os/rtl_external/`; the second proves each
is byte-identical to its golden and that no golden has drifted from its pinned
hash; the third runs the generator's own unit probes.

## What gets generated

One driver run emits **35** files: 30 into `build/os/rtl/` and 5 into
`build/os/rtl_external/`.

**Six exec cores** — the silicon lane:

| File | Variant | Consumed by |
|---|---|---|
| `rv32_exec_core.vhd` | base | GHDL NVMe-fw smoke, WB SoC |
| `rv64_exec_core.vhd` | base | GHDL WB SoC |
| `rv32_exec_core_flat.vhd` | flat (full-RAM behavioral) | GHDL boot-tiny / NVMe-fw testbenches |
| `rv64_exec_core_flat.vhd` | flat | GHDL boot-tiny / SimpleOS boot testbenches |
| `rv32_exec_core_axi.vhd` | axi (synthesizable AXI-master-shaped) | `soc_top_rv32_k26_ddr`, tiny-BRAM SoC |
| `rv64_exec_core_axi.vhd` | axi | `soc_top_rv64_k26_ddr` |

**24 more files whose goldens live in `examples/09_embedded/fpga_riscv/rtl/`:**

| Group | Count | Files |
|---|---|---|
| Bus / memory infra | 4 | `rv32_axi4_mem_adapter.vhd`, `rv64_axi4_mem_adapter.vhd`, `rv32_ctrl_obs_slave.vhd`, `rv32_bram_soc.vhd` |
| SoC tops | 7 | `soc_top_rv{32,64}.vhd`, `soc_top_rv{32,64}_k26_ddr.vhd`, `soc_top_rv{32,64}_sim.vhd`, `soc_top_rv32_tiny_bram.vhd` |
| Testbenches | 13 | `tb_rv{32,64}_k26_ddr_boot.vhd`, `tb_rv{32,64}_wb_soc_smoke.vhd`, `tb_rv{32,64}_simpleos_boot.vhd`, `tb_rv{32,64}_simpleos_boot_axi.vhd`, `tb_rv32_nvme_fw_smoke.vhd`, `tb_rv32_simpleos_boot_tiny.vhd`, `tb_rv32_tiny_bram_soc.vhd`, `tb_rv64_soak.vhd`, `tb_rv32_nvme_bram_soc.vhd` |

Together with the cores that is all **30** `.vhd` files under
`examples/09_embedded/fpga_riscv/rtl/` — the directory is fully generated.

**5 files whose goldens live OUTSIDE that directory.** These are emitted into a
**separate output dir, `build/os/rtl_external/`**, and matched through an
explicit basename → golden-path map (Layer 3b below):

| Generated basename | Golden path |
|---|---|
| `tb_rv32_payload.vhd` | `examples/09_embedded/fpga_riscv/payload/tb_rv32_payload.vhd` |
| `tb_gate.vhd` | `test/riscv_isa_gate/tb_gate.vhd` |
| `tb_rv32_product_sv32_pmp.vhd` | `test/01_unit/lib/hardware/fpga_linux/rv32_product_sv32_pmp_ghdl/` |
| `tb_rv64_product_sv39_pmp.vhd` | `test/01_unit/lib/hardware/fpga_linux/rv64_product_sv39_pmp_ghdl/` |
| `tb_rv64_product_wb_axi.vhd` | `test/01_unit/lib/hardware/fpga_linux/rv64_product_wb_axi_ghdl/` |

They get their own directory because `check-riscv-rtl-truth.shs` scans
`build/os/rtl` as a **single lane** and requires every instantiated entity to be
defined within it — the three product testbenches instantiate companions that
exist only in their own golden dirs, so staging them flat produced spurious
`wrapper instantiates undefined entity` violations.

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
| `bus_infra_types.spl`, `axi4_mem_adapter_{gen,sections}.spl`, `ctrl_obs_slave_{gen,sections}.spl`, `bram_soc_{gen,sections}.spl` | bus / memory infrastructure |
| `soc_top_types.spl`, `soc_top_{gen,sections}.spl` | the 7 SoC tops |
| `tb_single_lane_*`, `tb_k26_ddr_*`, `tb_wb_*`, `tb_simpleos_wb_gen`, `tb_oneoff_*`, `tb_product_*` (`_gen`/`_sections`/`_types`) | the testbench families |
| `generate_main.spl` | CLI entry used by the driver script; holds the one authoritative output list |

## Driver script

```bash
sh scripts/fpga/generate_exec_core_vhdl.shs [--mem-prefix DIR/] [--out-dir DIR]
```

It `cd`s to the repo root, creates `build/os/rtl` **and
`build/os/rtl_external`**, and runs
`bin/simple run src/lib/hardware/vhdl_gen/generate_main.spl` with your flags.

| Flag | Default | Meaning |
|---|---|---|
| `--mem-prefix <dir/>` | `""` (golden's relative form, e.g. `rv32_payload.mem`) | Path prefix prepended to the `.mem` filenames in `init_rom` / `init_data_rom` / `init_mem` / `init_ram` / `init_rdisk` and the flat cores' `file_open` ramdisk reference. Use it when a simulator runs from a different working directory. **The axi cores read no `.mem` files**, so this flag does not affect them. Any non-empty prefix necessarily breaks byte-equality with the goldens — that is expected and intended. |
| `--out-dir <dir>` | `build/os/rtl` | Output directory for the 30 in-tree-golden files. The 5 out-of-tree-golden files always go to `<out-dir>_external`. |

There are no other flags. Success prints one `VHDL_GEN: wrote <path>` line per
emitted file followed by `VHDL_GEN: OK`; a write failure prints
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

Covers all 35 generated RTL files. **Generation is the default expectation**: a
missing `build/os/rtl/<file>.vhd` FAILS. Pass `--allow-missing` to opt out and
have it reported as `not-generated` instead; `--require-generated` is accepted
as a no-op because it is now the default.

Four fail-closed layers:

1. **Golden drift** — every file in the manifest must still hash to its pinned
   sha256.
2. **Generated match, cores** — each of the 6 cores must be byte-identical to
   its same-named golden. Reported per core so existing lanes citing those keys
   keep working.
3. **Generated match, rest** — the other 24 files under the golden dir, same
   rules, reported in aggregate.
   **3b. Out-of-tree goldens** — the 5 files whose golden is not in the golden
   dir, read from `build/os/rtl_external/` and matched through the explicit
   basename → golden-path map in the gate.
4. **Coverage audit** — every `.vhd` in the golden dir must appear in the gate's
   `CORES` or `RTL_REST` list. Anything else fails as `UNCOVERED GOLDEN`. This
   exists because a hash check cannot catch a file it was never told about: on
   2026-07-27 `tb_rv32_nvme_bram_soc.vhd` was live at origin but unpinned and
   ungenerated, so a stray local deletion went unnoticed. Adding a golden means
   adding it to **both** the gate and the generator.

Summary keys (always printed, one per line):

```text
vhdl_golden_match_external_total=5
vhdl_golden_match_external_pass=<n>
vhdl_golden_match_external_fail=<n>
vhdl_golden_match_external_missing=<n>
vhdl_golden_match_uncovered=<n>
vhdl_golden_match_manifest=ok|drift
vhdl_golden_match_rv32=pass|fail|not-generated
vhdl_golden_match_rv64=pass|fail|not-generated
vhdl_golden_match_rv32_flat=pass|fail|not-generated
vhdl_golden_match_rv64_flat=pass|fail|not-generated
vhdl_golden_match_rv32_axi=pass|fail|not-generated
vhdl_golden_match_rv64_axi=pass|fail|not-generated
vhdl_golden_match_rest_total=24
vhdl_golden_match_rest_pass=<n>
vhdl_golden_match_rest_fail=<n>
vhdl_golden_match_rest_missing=<n>
vhdl_golden_match_ok=true|false
```

Green at HEAD: `rest_pass=24`, `external_pass=5`, `uncovered=0`, all six core
keys `pass`, `manifest=ok`, `ok=true`.

Exit `0` = all good, `1` = any fail (drift, byte mismatch, uncovered golden, or
a missing generated file), `2` = environment problem (missing manifest or
golden).

`VHDL_GEN_DIR` overrides the generated-output directory (default
`build/os/rtl`) and `VHDL_GEN_EXT_DIR` the out-of-tree-golden one (default
`${VHDL_GEN_DIR}_external`) — useful for checking a staged tree without
regenerating.

### Generator probes

```bash
sh scripts/check/check-vhdl-gen-probes.shs
```

Runs every probe under `test/01_unit/lib/hardware/vhdl_gen/`. The probes are
**discovered by glob** (`probe_*.spl`), never a hardcoded list — a hardcoded
list is exactly how `tb_rv32_nvme_bram_soc.vhd` stayed invisible to the golden
gate for weeks. Adding a probe file is all it takes to gate it.

Why it exists: the probes prove byte-identity per family, but nothing ran them
automatically. Several emitter modules are shared across families (generalized
rather than forked), so a behaviour-preserving-looking refactor in one family
can silently break another's byte-identity. A hand-run probe is a snapshot; this
makes it standing.

Fail-closed on every ambiguous outcome — a probe **fails** (never skips) if the
runner exits non-zero, if any `FAIL ` line appears, if there are zero `PASS `
lines, or if the `ALL PASS` banner is missing. That last pair is the guard
against the false-green that already bit this lane: `ALL PASS` printed while
every file write had silently failed.

```text
vhdl_gen_probes_total=8
vhdl_gen_probes_pass=8
vhdl_gen_probes_fail=0
vhdl_gen_probes_ok=true
```

Currently 8 probes / 72 checks. Exit `0` = all passed, `1` = any probe failed,
`2` = environment problem (no probes found, no runner).

`--selftest` is the deliberate-red arm: it proves a probe printing a `FAIL` line
beats an `ALL PASS` banner, and that a silent probe fails rather than skips.

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
wrapper instantiating an untracked entity).

Clean at HEAD with the generator's output staged: `riscv_rtl_truth_ok=true`,
`riscv_rtl_truth_generated_real=8`, `riscv_rtl_truth_unknown=0`, zero
violations. That is why the 5 out-of-tree-golden files get
`build/os/rtl_external/` — this gate scans `build/os/rtl` as a single lane and
requires every instantiated entity to be defined within it.

A VIOLATION is a finding to file, never a reason to weaken the rule.

## Golden manifest and legitimate drift

`doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt` pins 56 files by
sha256: 30 under `examples/09_embedded/fpga_riscv/rtl/`, the 5 out-of-tree
goldens (payload / ISA gate / three fpga_linux product testbenches), and 21
under `src/lib/hardware/debug/`. The header records the repo HEAD the pins were
taken at, and carries the dated notes for every legitimate change.

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

## Scope limit — what is deliberately NOT generated

All 30 `.vhd` files under `examples/09_embedded/fpga_riscv/rtl/` plus the 5
out-of-tree goldens are generated. Three things are **deliberately** left
hand-written, and each has a reason that must survive the next agent who notices
the gap and "finishes the job".

**1. `core64_imac_product_entry_stub.vhd`** —
`test/01_unit/lib/hardware/fpga_linux/rv64_product_wb_axi_ghdl/`.
It declares entity `core64_imac_product_entry`; its basename contains `core` and
its only `case` is `case state is`, so `scripts/check/check-riscv-rtl-truth.shs`
reads `decode_present=0` and classifies it as a decode-free "core". Teaching the
generator to emit it would hand the generator the ability to **mint fake CPUs
with generated provenance** — precisely what that truth gate and the
`test/fixtures/riscv_truth/fake_*.vhd` negative fixtures exist to catch. Keep
negative and stub RTL hand-authored; a generator that can produce it is a
generator whose `generated-real` verdict means nothing.

**2. `examples/09_embedded/vhdl/simulation/bounded_loop_example.vhd`** — a
hand-written *reference fixture* of the compiler `--backend=vhdl` lane (lane (a)
above), not of this generator. It has zero consumers, and it does not even
analyse: it calls `ceil`/`log2`/`real` with no `use ieee.math_real.all`.
Generating an artefact nothing builds and nothing consumes would only pin a
broken file in place. `probe_tb_oneoff_gen.spl` records the SKIP with this
rationale; the manifest header repeats it.

**3. The 21 JTAG transport files under `src/lib/hardware/debug/`** — TAP, DTM,
DMI, Debug Module and their testbenches stay hand-written, fail-closed VHDL. AOP
is only for hart join points. They are still **pinned in the manifest**, so
drift in them is caught even though generation is not attempted.

## Tests

```bash
sh scripts/check/check-vhdl-gen-probes.shs                                  # all 8 probes
bin/simple test test/01_unit/lib/hardware/vhdl_gen/exec_core_gen_spec.spl
bin/simple run  test/01_unit/lib/hardware/vhdl_gen/probe_exec_core_gen.spl  # one family
```

Each probe prints per-stage `PASS`/`FAIL` lines and a final `... ALL PASS`
banner (`probe_exec_core_gen.spl`: 14 PASS lines; 72 checks across all 8). They
are the runnable evidence lane while the deployed binary cannot run the spec
(below) — prefer the gate, which runs them all and fails closed.

## Troubleshooting

Parcel and trap frontends now serialize through the same
`HwSequentialModuleDef` renderer as other typed sequential products. Their
fixed validators still reject template, pin, register, origin, and decoder
drift; the adapter binds the compiled decoder graph and prepends that decoder
once. Source rendering is not qualification: the admitted two-phase runner
must retain measured coverage and independent GHDL analyze/elaborate/run
evidence before PASS.

The v2 receipt retains the measured coverage command/report, changed files and
explicit exclusions, each RV32/RV64 product command and `.gen.json`, generated
VHDL and testbench, and separate GHDL analyze/elaborate/run commands, exits, and
logs. The runner cannot select another composer or write the receipt itself.

### Gen2 qualification v2 operator boundary

Run `scripts/check/run-riscv-gen2-hwir-qualification.shs` only with an absolute,
provenance-admitted Stage-4 CLI, its adjacent provenance file, and an absolute
fresh output directory. Phase one owns compiler coverage, both critical product
commands, fixed testbenches, and isolated GHDL analyze/elaborate/run commands;
the admitted Simple composer alone publishes the final receipt last. Coverage
must bind an authoritative owned-file inventory, include compiler-time
zero-count decisions, deduplicate runtime outcomes, and use exactly four
exclusions: generated VHDL, testbench literals, legacy v1 generators, and the
separate retirement producer. Missing GHDL is a blocker, not an exclusion.

This is currently a WARN/source handoff. Exact command grammar, duplicate-safe
product JSON, canonical parent handling, and destination rehash are implemented
at source level but remain unverified; deliberate-red writer coverage and an
admitted RV32/RV64 run remain open in the canonical
[task plan](../../../03_plan/agent_tasks/riscv_gen2_hwir_foundation.md) and
[qualification bug](../../../08_tracking/bug/riscv_gen2_hwir_qualification_contract_mismatch_2026-08-14.md).

The compiler-side inventory now walks only canonical, tag-dispatched flat-AST
children, preserves source spans through parsing and placeholder desugaring,
and emits bounded zero-count rows whose keys/escaping match runtime probes.
This source is highest-capability static-review green; the tracked Stage-3
bootstrap artifact exits 139 on its focused native build, so no executable
coverage or Stage-4 qualification is claimed.

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
