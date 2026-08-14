# hardware_rtl Layer Expert

## Role

Own layer-specific process knowledge for RTL **generation** in pure Simple —
`src/lib/hardware/vhdl_gen/`, the layer that turns typed descriptor arrays into
synthesizable VHDL text. This layer sits below the RISC-V core/SoC models
(`src/lib/hardware/riscv_common/`, `rv32i_rtl/`, `rv64gc_rtl/`, `soc_rtl/`) and
above the golden `.vhd` artifacts in `examples/09_embedded/fpga_riscv/rtl/`.
It owns emission determinism, XLEN templating, and the AOP debug-tap weave.
It does NOT own the core semantics — those live in the `.spl` models.

Scope is **35 emitted RTL files**, not just the 6 exec cores: all 30 files under
`examples/09_embedded/fpga_riscv/rtl/` (cores + bus/memory infra + 7 SoC tops +
13 testbenches) plus 5 whose goldens live elsewhere (`tb_rv32_payload`,
`test/riscv_isa_gate/tb_gate`, three `fpga_linux` product testbenches) — those
5 are emitted to a separate `build/os/rtl_external/`, see the landmine. Emitter
modules are SHARED across those families rather than forked, so a
behaviour-preserving-looking refactor in one family can break another's
byte-identity — always run the probe gate, not just your own family's probe.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify.md)
- [impl skill](../../../../.claude/skills/impl.md)
- [compiler HWIR layer](../compiler_hwir/skill.md) — the separate compiler-side
  typed combinational/sequential IR and strict VHDL lowering boundary.

## Layer Links

- Generation primitives: [src/lib/hardware/vhdl_gen/gen_types.spl](../../../../src/lib/hardware/vhdl_gen/gen_types.spl)
  (`VgPort`/`VgAssign`/`VgConst`/`VgArm`/`VgCsr`/`VgMemInit`/`VgCoreGeometry`,
  plus `vg_hex`/`vg_pad`/`vg_append`/`vg_spaces` and the section re-indent helper).
- Base-core emission: `exec_core_gen.spl` + `rv32_sections.spl` / `rv64_sections.spl`.
- Variant emission (flat/axi): `exec_core_variant_gen.spl` +
  `rv{32,64}_variant_sections.spl`.
- Bus/memory infra: `bus_infra_types.spl` + `axi4_mem_adapter_*`,
  `ctrl_obs_slave_*`, `bram_soc_*` (`_gen`/`_sections`).
- SoC tops: `soc_top_types.spl` + `soc_top_{gen,sections}.spl`.
- Testbench families: `tb_single_lane_*`, `tb_k26_ddr_*`, `tb_wb_*`,
  `tb_simpleos_wb_gen`, `tb_oneoff_*`, `tb_product_*`.
- Debug aspect: `debug_tap_aspect.spl` (join points PORTS / SIGNALS / ASSIGNS /
  PROCESS_TAPS, default ON).
- Entry point: `generate_main.spl` ← `scripts/fpga/generate_exec_core_vhdl.shs`.
- XLEN config: [src/lib/hardware/riscv_common/xlen.spl](../../../../src/lib/hardware/riscv_common/xlen.spl).
- Specs: `test/01_unit/lib/hardware/vhdl_gen/`,
  `test/03_system/compiler/pure_simple_vhdl_source_of_truth_spec.spl`.
- Feature expert: [vhdl_exec_core_gen](../../feature_expert/vhdl_exec_core_gen/skill.md);
  neighbours: [riscv_soc_linux](../../feature_expert/riscv_soc_linux/skill.md)
  and [nvme_firmware](../../feature_expert/nvme_firmware/skill.md).

## Structuring rules (why the code looks like this)

Four emission shapes, chosen deliberately over blob embedding:
typed **descriptor arrays** (ports/signals/constants), **opcode-table-driven**
decode arms (`VgArm`), **CSR read-mux cases** (`VgCsr`), and **named literal
sections** for the handful of irreducible paragraphs. A literal section is
allowed only when it is named and scoped to one paragraph — a whole-file literal
is the thing this layer exists to eliminate.

Variant cores reuse base sections through the re-indent helper rather than
copying them; that is where the ~68% section sharing comes from. Variant goldens
use GROUP-LOCAL column alignment (the AXI `mem_*` port group aligns to its own
width, `debug_*` does not), so `VgPortSpec`/`VgGenericSpec` carry explicit field
widths instead of a single `aligned` flag.

## Landmines (Simple-language constraints, learned the hard way)

- **No user-type operator overloading.** No trait `Add`, no dunders. The API is
  method chaining (`a.add(b)`, `a.eq(b)`) — do not try to build a `Signal`
  eDSL with `+`/`==`.
- **No const generics.** `Signal<32>` is impossible; width travels as a struct
  field (`XlenConfig`) consumed at elaboration time. This is a feature here, not
  a workaround — but never claim the generator is "compile-time parameterized".
- **Seed `Dict` iteration order is nondeterministic per process.** Use ARRAYS
  only, everywhere in this layer. One `Dict` in an emission path and the output
  stops being byte-reproducible — and the golden gate becomes a coin flip.
- **Seed `.push()` always clones (O(N²)).** Presize and assign `arr[i] = v` for
  anything line-count-sized; join per section once rather than accumulating the
  whole file.
- **Braces in generated text.** VHDL is brace-free so interpolation is clean,
  but XDC/Tcl output uses `get_ports {x}` — escape as `{{`/`}}` (see
  `src/lib/hardware/fpga_linux/xdc_gen.spl`). Watch this whenever emission moves
  beyond VHDL.
- **`@step "..."` decorator syntax does not parse in the deployed seed** —
  write SSpec steps as `step("...")` calls in this layer's specs.
- **`.len()` counts BYTES, indexing counts CHARS — they disagree on non-ASCII.**
  An em dash in a generated file's header ran an index loop past the end
  (`tb_rv32_payload`; note recorded in `probe_tb_oneoff_gen.spl`). Any loop that
  walks emitted or golden text must use `split` or a char-index loop; never pair
  `s.len()` with `s[i]`. Generated headers and comments are exactly where
  non-ASCII sneaks in.
- **Negative / fake RTL fixtures must stay HAND-AUTHORED.**
  `test/fixtures/riscv_truth/fake_*.vhd` and
  `core64_imac_product_entry_stub.vhd` (decode-free `core*` entity) are what
  `check-riscv-rtl-truth.shs` calibrates against. Teach this layer to emit them
  and the gate can no longer distinguish a real core from a minted one — the
  `generated-real` verdict becomes worthless. Coverage here is not a goal.
- **A hardcoded file list in a gate hides real files.**
  `tb_rv32_nvme_bram_soc.vhd` was live at origin, unpinned and ungenerated, and
  a stray local deletion went unnoticed for weeks because no list mentioned it.
  Discover by glob (`check-vhdl-gen-probes.shs` globs `probe_*.spl`); where a
  list is unavoidable, pair it with a coverage audit that fails on anything
  present-but-unlisted (golden-match Layer 4, `vhdl_golden_match_uncovered`).
- **Staging emitted RTL into a directory that a truth/lint gate scans as a
  SINGLE lane produces spurious undefined-entity violations** for any wrapper
  whose companion entities live elsewhere. `check-riscv-rtl-truth.shs` requires
  every instantiated entity to be defined within the lane dir, so the three
  `fpga_linux` product testbenches flagged 4 bogus violations until they were
  moved out. Give such files their own output dir (here
  `build/os/rtl_external/`, `VHDL_GEN_EXT_DIR`) — fix the staging, never
  weaken the gate or exempt the file.

## Verification

- `sh scripts/check/check-vhdl-golden-match.shs` — the layer's contract:
  generate, then byte-compare all 35 files. Generation is the DEFAULT (missing
  = FAIL; `--allow-missing` opts out, `--require-generated` is a no-op). Layer
  3b maps basenames to out-of-tree goldens, reading `build/os/rtl_external/`
  (`..._external_*`, total 5; `VHDL_GEN_EXT_DIR` / `VHDL_GEN_DIR` override the
  two dirs); Layer 4 audits coverage (`vhdl_golden_match_uncovered`). Any diff
  is a layer defect, never a "golden refresh".
- `sh scripts/check/check-vhdl-gen-probes.shs` — every probe under
  `test/01_unit/lib/hardware/vhdl_gen/`, glob-discovered, fail-closed (a probe
  with no `PASS ` lines or no `ALL PASS` banner FAILS, never skips — this caught
  an `ALL PASS` printed while every write silently failed). 8 probes / 72 checks.
- `--selftest` on both gates mutates/injects a red case and must FAIL (proves
  the gate can go red).
- `sh scripts/check/check-riscv-rtl-truth.shs` — clean at HEAD with the
  generator's output staged: `riscv_rtl_truth_ok=true`, `generated_real=8`,
  `unknown=0`, zero violations.
- Pins: `doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt` (56).

## Update Rule

When emission shape, the descriptor types, the aspect join points, or the golden
set changes, update this skill with the new links and gate results. Never update
a golden pin to make the match gate pass — root-cause the emission diff.
