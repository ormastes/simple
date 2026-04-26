# VHDL Backend Support Matrix

**Date:** 2026-04-23
**Status:** Active
**Canonical reference for VHDL backend support claims.**

Note: this matrix distinguishes implemented Rust MIR backend behavior,
Simple-side source-facade compatibility behavior, and the intended pure Simple
compiler source of truth. A feature is not considered pure-Simple-owned until a
`test/system/compiler/pure_simple_*vhdl*_spec.spl` acceptance spec is runnable.

## Quick Summary

The VHDL backend compiles a documented hardware-oriented Simple subset to synthesizable VHDL-2008 and validates generated designs through GHDL analysis, elaboration, synthesis, and simulation proof where available. Existing coverage is split across the Rust MIR backend, the Simple MIR VHDL backend, and a Simple-side source facade. The 2026-04-23 selected parity milestone adds reset/domain metadata, deterministic source-map sidecars, source-facade bundle and port collision diagnostics, tagged-record payload enum ports/results, aggregate construction, payload field projection, tag-based switch matching, payload-free enum literal sanitization/collision checks, unit-return no-output entities, conservative fixed-width operations, helper subprogram support, conservative ROM/RAM templates with memory deferrals, optional vendor-smoke skip/report/log coverage, and deterministic one-DUT plus multi-DUT/multi-phase testbench rendering. Broad HLS ownership remains deferred for floats, pointers, unconstrained memories, unsupported MIR instructions, ordinary-function helper inference outside explicit `@hardware` helper entities, implicit-width behavior outside the supported source-facade subset, and the pure-Simple compiler source-of-truth path. Implicit heap allocation, pointer wrappers, pointer dereference, and dynamic pointer-like addressing fail before VHDL file emission with diagnostics that name the unsupported source form and direct authors to explicit ROM/RAM memory-interface boundaries.

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
| Payloadless Enum | `type T is (A, B, C)` and variant literal assignments; MIR literals are sanitized and checked for VHDL collisions | stable | stable | stable | supported | **stable** |
| Payload Enum | tagged record with `tag` plus deterministic payload fields | supported | stable | stable | supported for supported record operations | **supported** |
| `f16/f32/f64` | explicit fixed-point must be encoded as fixed-width integer ports/signals with documented scale/rounding/saturation; bare float hardware values emit actionable diagnostics or require an explicit float IP boundary | fixed-point via integer: supported; bare float: error | fixed-point stable | fixed-point stable | fixed-point supported | **contracted/deferred** |
| `Unit` return | no output port | supported | stable | stable | supported | **supported** |
| Pointer | — (unsupported pointer-type diagnostic; use explicit ROM/RAM memory-interface ports/templates) | error | — | — | — | **deferred** |

## Constant Support

| Constant Kind | VHDL Literal | Status |
|--------------|-------------|--------|
| Integer (signed) | `to_signed(v, w)` | **stable** |
| Integer (unsigned) | `to_unsigned(v, w)` | **stable** |
| Boolean | `'1'` / `'0'` | **stable** |
| String | `"..."` | **stable** |
| Zero aggregate | `(others => '0')` | **stable** |
| Float | — (unsupported constant diagnostic) | **deferred** |

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
| `GcAlloc` / implicit heap allocation | — (memory-boundary diagnostic before VHDL emission; source form named) | **deferred** |
| `PointerNew` / `PointerRef` / `PointerDeref` | — (memory-boundary diagnostic before VHDL emission; explicit memory-interface action named) | **deferred** |
| `GetElementPtr` / non-local `Load` / non-local `Store` / indexed collection memory | — (pointer-like addressing diagnostic before VHDL emission; explicit address/data/control interface required) | **deferred** |
| Generic `Call` | — (pre-emission diagnostic unless target is a VHDL intrinsic or direct `@hardware` entity) | **deferred** |
| `CallIndirect` / closure dispatch / virtual method dispatch | — (pre-emission diagnostic; direct `@hardware` calls required) | **deferred** |
| Stateful/general memory MIR | — (`VHDL-MEM-*` or unsupported-stateful hard error unless matched by explicit ROM/RAM template renderer or explicit memory-interface ports) | **deferred** |
| Async/actor/generator MIR and state-machine metadata | — (pre-emission runtime-only state transition diagnostic; no HLS state-machine lowering) | **deferred** |
| All other unsupported MIR | — (unsupported-MIR hard diagnostic) | **deferred** |

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
| Clocked (rising edge) | Clock signal, with no-reset clock-only emission when reset metadata is absent | **stable** |
| Clocked (falling edge) | Clock signal | **stable** |
| Async reset | Clock + reset; active-low names ending in `_n`, otherwise active-high | **stable** |
| Source-facade sync reset | Clock only sensitivity with reset branch under `rising_edge` | **supported** |

## Entity Structure

| Feature | Status |
|---------|--------|
| Entity/architecture pairs | **stable** |
| Port declaration (in/out) | **stable** |
| Internal signal declarations | **stable** |
| Package generation | **stable** |
| Record type in package | **stable** |
| Enum type in package | **stable** |
| Helper function/procedure declarations and bodies | **supported** |
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
| Pure Simple source facade | Conservative single-function compatibility path: fixed-width integers, bools, arithmetic, comparisons, boolean logic, literal shifts, unary neg/not, casts, simple muxes, `@hardware`, labeled tuple output ports, deterministic anonymous tuple output ports, named/nested bundle input flattening, sanitized port collision diagnostics, payload-free enum coverage where compiler metadata exists, narrow slice/concat support, and hard diagnostics for unsupported implicit-width behavior. Structured `@generic` and `@clocked` metadata are now owned by the compiler VHDL path instead of the source facade. | **supported** |
| Labeled multi-return hardware outputs | `@hardware fn f(...) -> (sum: bool, carry: bool)` lowers labels to VHDL `out` ports; duplicate labels after VHDL identifier sanitization are rejected | **supported** |
| Anonymous hardware outputs | Source-facade hardware tuple returns without field labels lower to deterministic `out_N` output ports, validate collisions before VHDL emission, and are covered by GHDL analysis/elaboration | **supported** |
| Pure Simple compiler VHDL path | `simple compile --backend=vhdl` owns the runnable scalar entity, tuple-output ABI, direct hardware-call instance/port-map, selected pure combinational helpers expressed as explicit `@hardware` entities, deterministic temp-signal, field-access, typed signed comparison, explicit fixed-point-by-fixed-width-integer contract, unsigned fixed-width literal shift, fixed-width slice/concat, structured `@generic` declarations, structured `@clocked` process metadata including sync/async/no-reset named-domain forms, E0710 cross-domain rejection, stale-artifact cleanup on failed lowering, actionable bare-float diagnostics, and GHDL analyze/elaborate checks. Ordinary-function helper inference and broader HLS behavior remain deferred with hard diagnostics. | **partial** |
| GHDL `-a --std=08` | Analysis | **supported** |
| GHDL `-e --std=08` | Elaboration | **supported** |
| GHDL `-r` | Simulation | **supported** |
| GHDL `--synth` | Synthesis | **supported** |
| Optional vendor synthesis smoke | `SIMPLE_VHDL_VENDOR_SMOKE=1`, clear diagnostics with deterministic command, report, and log paths when disabled, missing, or executed | **supported** |
| VHDL testbench renderer | One-DUT artifacts and ordered multi-DUT/multi-phase suites with literal stimuli, optional clock/reset driving, named port maps, equality assertions with `severity failure`, and source-map anchors for test name, DUTs, phases, ports, port-map lines, and expectations | **supported** |
| Explicit memory-interface boundary | Fixed address/data/control ports or explicit ROM/RAM templates; this is the accepted path for storage, rather than inferred heap or pointer lowering | **supported** |
| ROM/RAM template renderer | Static ROM, registered ROM read, and single-port synchronous RAM with explicit vendor-safe read-during-write policy; ambiguous or unconstrained memory semantics reject with `VHDL-MEM-*` diagnostics before VHDL output | **supported** |
| Yosys | Synthesis | **deferred** |

## MIR Backend Source-of-Truth Parity Specs

The Rust MIR backend parity handoff remains a reference implementation path.
These specs do not by themselves satisfy the broad pure Simple compiler
source-of-truth requirement:

- `test/system/compiler/vhdl_mir_backend_multi_output_spec.spl` covers labeled
  tuple return ABI ports, same-type labeled outputs, sanitized collision
  diagnostics, and GHDL analyze/elaborate/synth acceptance.
- `test/system/compiler/vhdl_mir_backend_call_port_map_spec.spl` covers direct
  `@hardware` call instance emission, named `port map` wiring, deterministic
  temp signals, field access over virtual aggregates, runtime tuple rejection,
  and GHDL analyze/elaborate/synth acceptance.

These runnable MIR specs remain reference coverage; duplicate source-facade
assertions should stay limited to compatibility smoke coverage.

## Pure Simple Source-of-Truth Specs

The broad pure Simple compiler handoff is tracked separately by:

- `test/system/compiler/pure_simple_vhdl_source_of_truth_spec.spl`

This file now has runnable coverage for the pure Simple CLI path over scalar
hardware entities, tuple output ABI, direct hardware-call `port map` lowering,
selected pure combinational helpers expressed as explicit `@hardware` entities,
hard diagnostics for ordinary-function helper inference, deterministic temp
signals, labeled field access, typed signed comparisons, unsigned fixed-width
literal shifts, fixed-width slice/concat, stale-artifact cleanup on failed
lowering, and GHDL analyze/elaborate checks. Remaining skipped examples track
structured `@generic`/`@clocked` metadata, domain semantics, and broad HLS
ownership other than the helper-inference hard-error boundary.

## Simulation Targets

| Target | Status | Notes |
|--------|--------|-------|
| `riscv32_sim_vhdl` | **deferred** | Quarantined per simulation milestone decision |
| GHDL counter simulation | **supported** | CI smoke test exists |

## Python-HDL Parity Backlog

Deferred and migrated SPipe coverage is surfaced by
`bin/simple test --only-skipped --list-skip-features --pending` where present.
The remaining tracked gaps are milestone-out-of-scope broad HLS work:
float IP lowering, pointers, unconstrained memories, unsupported MIR instructions,
ordinary-function helper inference outside explicit `@hardware` helper
entities, implicit-width behavior outside the supported source-facade subset,
and the remaining structured pure-Simple generic/clock-domain
handoff. Runnable coverage for the selected milestone is in
`test/unit/compiler/backend/vhdl_backend_spec.spl`,
`test/unit/compiler/backend/vhdl_type_mapper_spec.spl`,
`test/unit/compiler/backend/vhdl_constraints_spec.spl`,
`test/unit/compiler/backend/vhdl_memory_templates_spec.spl`,
`test/unit/compiler/backend/vhdl_testbench_spec.spl`,
`test/system/compiler/vhdl_source_facade_spec.spl`, and
`test/unit/compiler/backend/vhdl_vendor_synthesis_smoke_spec.spl`.

## Status Definitions

| Status | Meaning |
|--------|---------|
| **stable** | Fully implemented, tested, and verified. Covered by unit tests and golden file regression. |
| **supported** | Implemented and working. May have limited test coverage. |
| **deferred** | Explicitly out of scope for current milestone. Unsupported input produces hard compile error. |

## See Also

- `doc/04_architecture/vhdl_hardware_subset_contract.md` — Formal subset contract
- `doc/04_architecture/vhdl_simulation_milestone_decision.md` — Simulation milestone decision
- `doc/05_design/VHDL_BACKEND_DESIGN.md` — Design document
- `doc/03_plan/vhdl_backend_completion_plan_2026-04-04.md` — Completion plan
