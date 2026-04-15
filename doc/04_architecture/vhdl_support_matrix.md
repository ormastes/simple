# VHDL Backend Support Matrix

**Date:** 2026-04-04
**Status:** Active
**Canonical reference for VHDL backend support claims.**

## Quick Summary

The VHDL backend compiles a documented hardware-oriented Simple subset to synthesizable VHDL-2008, validates generated designs through GHDL analysis, and supports an authoritative simulation-backed proof path for supported targets.

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
| Struct | `record ... end record` | stable | stable | stable | supported | **stable** |
| Enum | `type T is (A, B, C)` | stable | stable | stable | supported | **stable** |
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
| `Nop` | (no output) | **stable** |
| All other MIR | — (hard error) | **deferred** |

## Process Forms

| Process Kind | Sensitivity | Status |
|-------------|------------|--------|
| Combinational | Explicit list | **stable** |
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
| `simple compile --backend=vhdl` | CLI entry point | **supported** |
| `aot_vhdl_file()` | Driver API | **stable** |
| GHDL `-a --std=08` | Analysis | **supported** |
| GHDL `-e --std=08` | Elaboration | **supported** |
| GHDL `-r` | Simulation | **deferred** (follow-on milestone) |
| GHDL `--synth` | Synthesis | **deferred** |
| Yosys | Synthesis | **deferred** |

## Simulation Targets

| Target | Status | Notes |
|--------|--------|-------|
| `riscv32_sim_vhdl` | **deferred** | Quarantined per simulation milestone decision |
| GHDL counter simulation | **partial** | CI smoke test exists |

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
