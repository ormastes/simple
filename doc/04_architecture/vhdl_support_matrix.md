# VHDL Backend Support Matrix

**Date:** 2026-04-23
**Status:** Active
**Canonical reference for VHDL backend support claims.**

Note: this matrix distinguishes implemented Rust MIR backend behavior,
Simple-side source-facade compatibility behavior, and the intended pure Simple
compiler source of truth. A feature is not considered pure-Simple-owned until a
`test/system/compiler/pure_simple_*vhdl*_spec.spl` acceptance spec is runnable.

## Quick Summary

The VHDL backend compiles a documented hardware-oriented Simple subset to synthesizable VHDL-2008 and validates generated designs through GHDL analysis, elaboration, synthesis, and simulation proof where available. Existing coverage is split across the Rust MIR backend, the Simple MIR VHDL backend, and a Simple-side source facade. The 2026-04-23 parity slice adds deterministic source-map sidecars, payload-enum hard diagnostics, enum literal collision checks, and optional vendor-smoke skip coverage. Full broad HLS ownership remains deferred for helper subprogram inference, ROM/RAM inference, tagged-record payload enums, and generated testbench conversion.

## Type Support

| Type | VHDL Mapping | Emission | GHDL Analysis | Elaboration | Synthesis | Status |
|------|-------------|----------|---------------|-------------|-----------|--------|
| `i8` | `signed(7 downto 0)` | stable | stable | stable | supported | **stable** |
| `i16` | `signed(15 downto 0)` | stable | stable | stable | supported | **stable** |
| `i32` | `signed(31 downto 0)` | stable | stable | stable | supported | **stable** |
| `i64` | `signed(63 downto 0)` | stable | stable | stable | supported | **stable** |
| `u8` | `unsigned(7 downto 0)` | stable | stable | stable | supported | **stable** |
| `u16` | `unsigned(15 downto 0)` | stable | stable | stable | supported | **stable** |
| `u32` | `unsigned(31 downto 0)` | stable | stable | stable | supported | **stable** |
| `u64` | `unsigned(63 downto 0)` | stable | stable | stable | supported | **stable** |
| `Bool` (unresolved) | `bit` | stable | stable | stable | supported | **stable** |
| `Bool` (resolved) | `std_logic` | stable | stable | stable | supported | **stable** |
| `Array(elem, N)` | `array (0 to N-1) of T` | stable | stable | stable | supported | **stable** |
| Tuple | generated record type with `fN` fields | supported | stable | stable | supported | **supported** |
| Struct | `record ... end record` | stable | stable | stable | supported | **stable** |
| Payloadless Enum | `type T is (A, B, C)` and variant literal assignments | stable | stable | stable | supported | **stable** |
| Payload Enum | — | error | — | — | — | **deferred** |
| `f16/f32/f64` | — | error | — | — | — | **deferred** |
| `Unit` | — | error | — | — | — | **deferred** |
| Pointer | — | error | — | — | — | **deferred** |

## Constant Support

| Constant Kind | VHDL Literal | Status |
|--------------|-------------|--------|
| Integer (signed) | `to_signed(v, w)` | **stable** |
| Integer (unsigned) | `to_unsigned(v, w)` | **stable** |
| Boolean | `'1'` / `'0'` | **stable** |
| String | `"..."` | **stable** |
| Zero aggregate | `(others => '0')` | **stable** |
| Float | — (hard error) | **deferred** |

## Instruction Support

| MIR Instruction | VHDL Output | Status |
|----------------|------------|--------|
| `Const` | Signal/variable assignment | **stable** |
| `Copy` / `Move` | Signal assignment | **stable** |
| `BinOp` (Add, Sub, Mul, Div) | Arithmetic expression | **stable** |
| `BinOp` (Eq, Ne, Lt, Le, Gt, Ge) | Conditional expression | **stable** |
| `BinOp` (BitAnd, BitOr, BitXor) | Logic expression | **stable** |
| `BinOp` (Shl, Shr) | `shift_left/right` | **stable** |
| `UnaryOp` (Neg, Not) | `-` / `not` | **stable** |
| `VhdlProcess` (Combinational) | `process(sens) begin...end` | **stable** |
| `VhdlProcess` (Clocked) | `process(clk) if rising_edge...` | **stable** |
| `VhdlProcess` (AsyncReset) | `process(clk,rst) if rst...` | **stable** |
| `VhdlSignalAssign` | `<=` with optional delay | **stable** |
| `VhdlVarAssign` | `:=` | **stable** |
| `VhdlPortMap` | Component instantiation | **stable** |
| `VhdlResize` | `resize(sig, w)` | **stable** |
| `VhdlSlice` | `sig(hi downto lo)` | **stable** |
| `VhdlConcat` | `a & b & c` | **stable** |
| `Aggregate` (struct/array/tuple) | Record/array/tuple aggregate expression | **stable** |
| `Aggregate` (payloadless enum) | Variant literal | **supported** |
| `GetField` | Record field select | **stable** |
| `SetField` | Record update through aggregate lowering | **supported** |
| `Nop` | (no output) | **stable** |
| `Alloc` | — (hard error) | **deferred** |
| `GetElementPtr` | — (hard error) | **deferred** |
| Generic `Call` | — (hard error unless explicitly handled) | **deferred** |
| `CallIndirect` | — (hard error) | **deferred** |
| Stateful/general memory MIR | — (hard error) | **deferred** |
| All other unsupported MIR | — (hard error) | **deferred** |

## Control Flow Support

| MIR Terminator Pattern | VHDL Output | Status |
|------------------------|-------------|--------|
| Direct `Return(value)` | Concurrent result assignment | **stable** |
| Direct `Return()` | Empty entity body / no result assignment | **stable** |
| `Goto` chain to return | Followed to final return block | **stable** |
| `If` with return-only arms | Concurrent conditional result expression | **stable** |
| `If` with computed arms | `comb: process(all)` with process variables and nested `if` | **stable** |
| `Switch` with return-only targets | Concurrent selected result lowering | **stable** |
| `Switch` with computed targets | `comb: process(all)` with `if`/`elsif`/`else` chain | **stable** |
| Cyclic control flow in combinational lowering | Hard error | **supported** |

## Process Forms

| Process Kind | Sensitivity | Status |
|-------------|------------|--------|
| Combinational | Explicit list | **stable** |
| Compiler-generated combinational branch process | `process(all)` | **stable** |
| Process-local struct/array aggregates | Variables and aggregate expressions inside process | **stable** |
| Clocked (rising edge) | Clock signal | **stable** |
| Clocked (falling edge) | Clock signal | **stable** |
| Async reset | Clock + reset | **stable** |

## Entity Structure

| Feature | Status |
|---------|--------|
| Entity/architecture pairs | **stable** |
| Port declaration (in/out) | **stable** |
| Internal signal declarations | **stable** |
| Package generation | **stable** |
| Record type in package | **stable** |
| Enum type in package | **stable** |
| Constant in package | **stable** |
| Component instantiation | **stable** |
| Generic parameters | **supported** |
| Architecture naming (rtl) | **stable** |

## Constraint Verification (E07xx)

| Code | Constraint | Detection | Status |
|------|-----------|-----------|--------|
| E0700 | Width mismatch | Compile-time | **stable** |
| E0701 | Width overflow | Compile-time | **stable** |
| E0710 | Clock domain crossing | Compile-time | **stable** |
| E0720 | Incomplete sensitivity list | Compile-time | **stable** |
| E0721 | Combinational loop (Tarjan SCC) | Compile-time | **stable** |
| E0722 | Latch inference | Compile-time | **stable** |
| E0730 | Unbounded loop | Compile-time | **stable** |
| E0740 | Multiple drivers | Compile-time | **stable** |

## Toolchain Integration

| Tool | Operation | Status |
|------|----------|--------|
| `simple compile --backend=vhdl` | CLI entry point for the conservative synthesizable subset | **supported** |
| `aot_vhdl_file()` | Driver API | **stable** |
| VHDL source-map sidecar | `<output>.map.json` with generated entity and port anchors | **supported** |
| Pure Simple source facade | Conservative single-function compatibility path: fixed-width integers, bools, arithmetic, comparisons, boolean logic, literal shifts, unary neg/not, casts, simple muxes, `@hardware`, labeled tuple output ports, selected `@generic`/`@clocked` forms, nested tuple input flattening, and narrow slice/concat support. This is not yet the structured pure Simple compiler source of truth. | **partial** |
| Labeled multi-return hardware outputs | `@hardware fn f(...) -> (sum: bool, carry: bool)` lowers labels to VHDL `out` ports; duplicate labels after VHDL identifier sanitization are rejected | **supported** |
| Anonymous hardware outputs | Distinct-type anonymous returns use positional tuple semantics in Simple; labeled outputs are required for stable VHDL public APIs | **partial** |
| Full pure Simple compiler VHDL path | Structured AST/HIR/MIR metadata to VHDL without source-facade parsing or Rust-only source-of-truth behavior | **deferred** |
| GHDL `-a --std=08` | Analysis | **supported** |
| GHDL `-e --std=08` | Elaboration | **supported** |
| GHDL `-r` | Simulation | **supported** |
| GHDL `--synth` | Synthesis | **supported** |
| Optional vendor synthesis smoke | `SIMPLE_VHDL_VENDOR_SMOKE=1`, clear skip when disabled or tool missing | **supported** |
| Yosys | Synthesis | **deferred** |

## MIR Backend Source-of-Truth Parity Specs

The Rust MIR backend parity handoff is tracked by pending system specs as a
reference implementation path. These specs do not by themselves satisfy the
pure Simple compiler source-of-truth requirement:

- `test/system/compiler/vhdl_mir_backend_multi_output_spec.spl` covers labeled
  tuple return ABI ports, same-type labeled outputs, anonymous-output rejection,
  sanitized collision diagnostics, and GHDL analyze/elaborate/synth acceptance.
- `test/system/compiler/vhdl_mir_backend_call_port_map_spec.spl` covers direct
  `@hardware` call instance emission, named `port map` wiring, deterministic
  temp signals, field access over virtual aggregates, runtime tuple rejection,
  and GHDL analyze/elaborate/synth acceptance.

When those specs are promoted from pending to runnable, duplicate source-facade
assertions should be reduced to compatibility smoke coverage.

## Pure Simple Source-of-Truth Specs

The pure Simple compiler parity handoff is tracked separately by:

- `test/system/compiler/pure_simple_vhdl_source_of_truth_spec.spl`

This file covers the implementation-worker acceptance surface for structured
pure Simple metadata, return ABI, direct hardware-call `port map` lowering,
fixed-width operations, reset/domain metadata, diagnostics, and GHDL
analyze/elaborate/synth checks. The examples remain pending until the behavior
is implemented in `src/compiler/**/*.spl` rather than only in Rust codegen or
the source facade.

## Simulation Targets

| Target | Status | Notes |
|--------|--------|-------|
| `riscv32_sim_vhdl` | **deferred** | Quarantined per simulation milestone decision |
| GHDL counter simulation | **partial** | CI smoke test exists |

## Python-HDL Parity Backlog

Pending and migrated SSpec coverage lives in
`test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip` and is surfaced by
`bin/simple test --only-skipped --list-skip-features --pending`. The tracked
gaps are clocked processes, reset/domain modeling, composite ports, fixed-width
bit operations, VHDL subprogram emission, ROM/RAM inference, generics,
interface bundles, enum encoding, payload enums, testbench conversion, source
maps, and vendor synthesis smoke. Runnable coverage for the implemented slice
is in `test/unit/compiler/backend/vhdl_backend_spec.spl`,
`test/system/compiler/vhdl_source_facade_spec.spl`, and
`test/system/compiler/vhdl_vendor_synthesis_smoke_spec.spl`.

## Status Definitions

| Status | Meaning |
|--------|---------|
| **stable** | Fully implemented, tested, and verified. Covered by unit tests and golden file regression. |
| **supported** | Implemented and working. May have limited test coverage. |
| **partial** | Partially implemented. Known gaps documented. |
| **deferred** | Explicitly out of scope for current milestone. Unsupported input produces hard compile error. |

## See Also

- `doc/04_architecture/vhdl_hardware_subset_contract.md` — Formal subset contract
- `doc/04_architecture/vhdl_simulation_milestone_decision.md` — Simulation milestone decision
- `doc/05_design/VHDL_BACKEND_DESIGN.md` — Design document
- `doc/03_plan/vhdl_backend_completion_plan_2026-04-04.md` — Completion plan
