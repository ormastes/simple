# hardware_rtl Layer Expert

## Role

Own layer-specific process knowledge for RTL **generation** in pure Simple —
`src/lib/hardware/vhdl_gen/`, the layer that turns typed descriptor arrays into
synthesizable VHDL text. This layer sits below the RISC-V core/SoC models
(`src/lib/hardware/riscv_common/`, `rv32i_rtl/`, `rv64gc_rtl/`, `soc_rtl/`) and
above the golden `.vhd` artifacts in `examples/09_embedded/fpga_riscv/rtl/`.
It owns emission determinism, XLEN templating, and the AOP debug-tap weave.
It does NOT own the core semantics — those live in the `.spl` models.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify.md)
- [impl skill](../../../../.claude/skills/impl.md)

## Layer Links

- Generation primitives: [src/lib/hardware/vhdl_gen/gen_types.spl](../../../../src/lib/hardware/vhdl_gen/gen_types.spl)
  (`VgPort`/`VgAssign`/`VgConst`/`VgArm`/`VgCsr`/`VgMemInit`/`VgCoreGeometry`,
  plus `vg_hex`/`vg_pad`/`vg_append`/`vg_spaces` and the section re-indent helper).
- Base-core emission: `exec_core_gen.spl` + `rv32_sections.spl` / `rv64_sections.spl`.
- Variant emission (flat/axi): `exec_core_variant_gen.spl` +
  `rv{32,64}_variant_sections.spl`.
- Debug aspect: `debug_tap_aspect.spl` (join points PORTS / SIGNALS / ASSIGNS /
  PROCESS_TAPS, default ON).
- Entry point: `generate_main.spl` ← `scripts/fpga/generate_exec_core_vhdl.shs`.
- XLEN config: [src/lib/hardware/riscv_common/xlen.spl](../../../../src/lib/hardware/riscv_common/xlen.spl).
- Specs: `test/01_unit/lib/hardware/vhdl_gen/`,
  `test/03_system/compiler/pure_simple_vhdl_source_of_truth_spec.spl`.
- Feature expert: [vhdl_exec_core_gen](../../feature_expert/vhdl_exec_core_gen/skill.md);
  neighbours: [riscv_soc_linux](../../feature_expert/riscv_soc_linux/skill.md).

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

## Verification

- `sh scripts/check/check-vhdl-golden-match.shs --require-generated` — the
  layer's contract: generate, then byte-compare all 6 cores. Any diff is a
  layer defect, never a "golden refresh".
- `--selftest` mutates a copy and must FAIL (proves the gate can go red).
- `sh scripts/check/check-riscv-rtl-truth.shs` — 6 lanes must say `generated-real`.
- Pins: `doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt`.

## Update Rule

When emission shape, the descriptor types, the aspect join points, or the golden
set changes, update this skill with the new links and gate results. Never update
a golden pin to make the match gate pass — root-cause the emission diff.
