# VHDL Backend Design

**Date**: 2026-02-11  
**Status**: Design proposal (draft)  
**Owner**: Tooling/Backends

## Goals
- Emit synthesizable VHDL for Simple programs with feature parity to the Verilog backend.
- Preserve compile-time guarantees (bounded loops, width correctness, CDC safety, no unsynthesizable constructs).
- Fit into existing backend architecture with minimal duplication.

## Scope (v1)
- Target synthesizable VHDL-2008 subset; allow select VHDL-2019 features that map cleanly (records, numeric_std).
- Single-clock and multi-clock modules with explicit clock/reset annotations.
- Structural/RTL generation only (no behavioral wait statements, no textio).
- Optional resolved signals (`std_logic[_vector]`) when multi-driver nets are detected; otherwise use unresolved `bit[_vector]`.

Out of scope v1: protected types, shared variables, VHPI/foreign imports, PSL, vendor IP generators.

## Architecture Integration
- Reuse existing MIR → backend abstraction. Add `VhdlBackend` alongside Verilog/LLVM.
- Introduce shared `backend/common/vhdl` utilities for name mangling, type mapping, and library/package emission.
- CLI flag `--emit-vhdl` or `target = vhdl` routed through backend factory.

## Type & Object Mapping
- Scalars: `bool` → `bit`, signed/unsigned ints → `signed`/`unsigned` from `ieee.numeric_std`.
- Aggregates: tuples/structs → `record` declarations emitted into a generated package; arrays → `array` of `std_logic_vector`/`bit_vector`.
- Enums: `enum` → VHDL `enum` with explicit encoding attribute for stability across backends.
- Aliases: mirror Simple aliases as VHDL `subtype` where widths are constant.

## Process Model
- Clocked blocks: emit `process(clk) begin if rising_edge(clk) then ... end if; end process;`
- Combinational blocks: emit sensitivity lists over read signals; insert default assignments to avoid latches.
- Bounded loops: generate unrolled logic when bound small; otherwise convert to FSM with explicit state type; reject unbounded/unknown bounds.
- Recursion: hard error.

## Static Checks & Annotations
- Width inference must resolve all arithmetic widths; truncation requires explicit policy (`wrap`/`saturate`) captured as attributes and comments.
- CDC: when signals cross domains, auto-insert two-flop synchronizer module references or emit error per configuration.
- Assertions: generate `assert ... severity error;` guarded with `-- synthesis translate_off/on` for synthesis-friendly builds; mirror SVA obligations from Verilog backend where feasible.

## Compile-Time Verification Points
- Type inference: resolve widths, signedness, and aggregate shapes before emit; fail if any type remains unknown or if inferred widths exceed configured caps.
- Loop checks: require static upper bounds; unroll when under threshold; otherwise generate FSM with explicit state enum and sanity-checked trip count; reject unbounded `while`.
- Combinational soundness: ensure processes have complete sensitivity lists and default assignments to avoid latches; run combinational-cycle detection on MIR nets.
- CDC enforcement: track clock/reset domains on signals; flag crossings without synchronizer primitives or explicit waiver; auto-insert two-flop sync when policy allows.
- Resolution policy: detect multi-driver nets; force resolved `std_logic[_vector]` and emit resolution function use; error if unresolved type would be multiply driven.
- Unsynthesizable constructs: ban recursion, dynamic memory, textio, wait statements, and non-static generates; surface diagnostics before VHDL emission.
- Assertion carry-over: translate backend invariants into VHDL `assert` statements and keep a map to source spans for IDE jump-to-error.

## Naming & Packaging
- Deterministic naming with source span hints; sanitize to VHDL identifier rules.
- One package per compilation unit: `<unit>_pkg.vhd` containing records, enums, subtypes, constants.
- Entities map 1:1 with top-level modules; architectures named `rtl`.
- Generate `work` library usage plus `ieee.std_logic_1164` and `ieee.numeric_std`.

## File Emission Layout
- `build/vhdl/<unit>_pkg.vhd` (types/constants)
- `build/vhdl/<module>.vhd` (entity/architecture)
- Optional `build/vhdl/<module>_tb.vhd` for generated test benches (future)

## Configuration / Grammar (consistent with existing backend selectors)
- Project-wide backend choice follows the existing lowercase token grammar used for CPU/GPU backends: `--backend=vhdl` (CLI) and `backend = "vhdl"` in project config (same slot currently accepting `"auto"`, `"cranelift"`, `"llvm"`, etc.).
- Per-file override uses the same token: keep any backend override directive/attribute grammar aligned (e.g., `@backend(vhdl)` or header comment form once wired). No mixed-case aliases; one canonical spelling `vhdl`.
- Mixed projects (CPU/GPU + VHDL) keep the same selector surface so automation/scripts don’t need special-casing.

## Compatibility & Interop
- Mixed-language goal: keep port names/types alignable with Verilog backend; avoid hidden name mangling.
- Resolved/unresolved policy configurable to ease integration with existing `std_logic` ecosystems.

## Risks & Mitigations
- Open-source synth gaps for VHDL-2019: keep default at 2008, gate newer features.
- Delta-cycle semantics: rely on explicit process types and default assignments; add CI simulations to detect unintended latches.
- Toolchain variance: document tested matrix (GHDL 4.x, ghdl-yosys-plugin, Vivado/Quartus smoke).

## Open Questions
- Do we expose a pragma to force `std_logic` on all ports for compatibility?
- Should we encode enums as `std_logic_vector` by default for synthesis friendliness?
- Policy for vendor-specific attributes (e.g., `KEEP_HIERARCHY`, `MARK_DEBUG`)—mirror Verilog or keep minimal?
