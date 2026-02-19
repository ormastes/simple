# VHDL Backend Design Document

This document describes the architecture and design of VHDL hardware description support in the Simple compiler.

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Type System Extensions](#type-system-extensions)
4. [MIR VHDL Instructions](#mir-vhdl-instructions)
5. [Verification Constraint System](#verification-constraint-system)
6. [Code Generation Pipeline](#code-generation-pipeline)
7. [VHDL Backend](#vhdl-backend)
8. [Runtime Integration](#runtime-integration)
9. [File Locations](#file-locations)
10. [Future Extensions](#future-extensions)

---

## Overview

### Goals

1. **Synthesizable Output**: Emit VHDL-2008 for synthesis and simulation
2. **Type Safety**: Compile-time width, CDC, and latch verification
3. **Consistency**: Follow the same backend architecture as GPU (CUDA/Vulkan)
4. **Extensibility**: Easy to add VHDL-2019 features and vendor targets

### Non-Goals (v1)

1. Behavioral simulation (wait statements, textio)
2. Protected types, shared variables
3. VHPI/foreign imports, PSL
4. Vendor IP generators

### Design Principles

- **Fail-fast**: All verification constraints checked before VHDL emission
- **Unresolved by default**: Use `bit`/`bit_vector` unless multi-driver detected
- **Static over dynamic**: Require static loop bounds, reject unbounded constructs
- **Backend-agnostic API**: Same MIR interface as GPU backends

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                      Simple Source Code                          │
│   fn adder(a: u8, b: u8) -> u8: a + b                          │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                         Lexer/Parser                             │
│   - --backend=vhdl flag triggers VHDL pipeline                   │
│   - No new syntax for v1                                         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                            HIR                                   │
│   - Annotate functions with ClockDomain metadata                 │
│   - ProcessKind: Combinational / Clocked / AsyncReset            │
│   - SignalKind: Wire / Register / Latch / Port                   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                            MIR                                   │
│   - VhdlProcess, VhdlSignalAssign, VhdlVarAssign                │
│   - VhdlPortMap, VhdlResize, VhdlSlice, VhdlConcat              │
│   - Standard MIR: BinOp, UnaryOp, Const, Copy, etc.             │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│              VhdlConstraintChecker                                │
│   - Width constraints  → DimSolver                               │
│   - CDC detection      → Graph coloring                          │
│   - Latch prevention   → Branch coverage                         │
│   - Comb loop detect   → Tarjan SCC                              │
│   - Loop bounds        → DimSolver                               │
│   - Single driver      → Driver count                            │
│   FAIL FAST: all constraints checked before emission             │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      VHDL Backend                                │
│   ┌─────────────────┐                                            │
│   │ VhdlTypeMapper  │  Maps Simple types → VHDL types            │
│   └─────────────────┘                                            │
│   ┌─────────────────┐                                            │
│   │  VhdlBuilder    │  Emits VHDL-2008 source text               │
│   └─────────────────┘                                            │
│   ┌─────────────────┐                                            │
│   │  VhdlBackend    │  Orchestrates compilation                   │
│   └─────────────────┘                                            │
│              │                                                    │
│              ▼                                                    │
│   ┌──────────────────────────────┐                               │
│   │  <unit>_pkg.vhd  (package)  │                                │
│   │  <module>.vhd    (entity)   │                                │
│   └──────────────────────────────┘                               │
│              │                                                    │
│              ▼                                                    │
│   ┌──────────────────────────────┐                               │
│   │  VHDL Toolchain FFI         │                                │
│   │  (GHDL, Yosys via SFFI)     │                                │
│   └──────────────────────────────┘                               │
└─────────────────────────────────────────────────────────────────┘
```

---

## Type System Extensions

### Signal Types

Location: `src/compiler/mir_data.spl`

```simple
enum VhdlSignalKind:       Wire | Register | Latch | Constant | Port(dir: VhdlPortDirection)
enum VhdlPortDirection:    In | Out | InOut | Buffer
enum VhdlClockEdge:        Rising | Falling
enum VhdlProcessKind:      Combinational(sensitivity: [text]) | Clocked(domain: VhdlClockDomain) | AsyncReset(domain: VhdlClockDomain)
enum VhdlSignalResolution: Unresolved | Resolved
enum VhdlNumericKind:      Signed(width: i64) | Unsigned(width: i64) | Integer(lo: i64, hi: i64) | Natural | Positive
struct VhdlClockDomain:    name: text, clock_signal: text, reset_signal: text?, edge: VhdlClockEdge
```

### Type Mapping (VhdlTypeMapper)

Location: `src/compiler/backend/vhdl_type_mapper.spl`

| Simple | VHDL (unresolved) | VHDL (resolved) |
|--------|-------------------|-----------------|
| `bool` | `bit` | `std_logic` |
| `i8`/`i16`/`i32`/`i64` | `signed(W-1 downto 0)` | same |
| `u8`/`u16`/`u32`/`u64` | `unsigned(W-1 downto 0)` | same |
| `[bool; N]` | `bit_vector(N-1 downto 0)` | `std_logic_vector(N-1 downto 0)` |
| `struct` | `record` | `record` |
| `enum` | `type ... is (...)` | same |
| `f32`/`f64` | **error** (not synthesizable) | **error** |

---

## MIR VHDL Instructions

Location: `src/compiler/mir_data.spl`

### Process Definition

```simple
VhdlProcess(kind: VhdlProcessKind, body_block: BlockId)
```

Defines a VHDL process. Process kinds:
- `Combinational(sensitivity)`: Combinational logic with explicit sensitivity list
- `Clocked(domain)`: Registered logic with clock domain
- `AsyncReset(domain)`: Registered logic with asynchronous reset

### Signal/Variable Assignment

```simple
VhdlSignalAssign(target: MirOperand, value: MirOperand, delay_ns: i64?)
VhdlVarAssign(target: MirOperand, value: MirOperand)
```

Signal assignment (`<=`) with optional delay; variable assignment (`:=`) for process-local variables.

### Component Instantiation

```simple
VhdlPortMap(entity: text, instance: text, connections: [(text, MirOperand)])
```

Instantiates a VHDL entity with named port connections.

### Bit Manipulation

```simple
VhdlResize(dest: LocalId, operand: MirOperand, new_width: i64, signed: bool)
VhdlSlice(dest: LocalId, signal: MirOperand, hi: i64, lo: i64)
VhdlConcat(dest: LocalId, parts: [MirOperand])
```

Width manipulation: resize (zero/sign extend or truncate), slice (`hi downto lo`), concatenation (`&`).

---

## Verification Constraint System

This is the centerpiece of the VHDL backend design. A two-layer architecture ensures correctness before any VHDL is emitted.

### Layer 1: Numeric/Width Constraints (DimSolver)

Reuses the existing `DimSolver` from `src/compiler/dim_constraints.spl`.

New `DimConstraint` variants in `src/compiler/dim_constraints_types.spl`:

| Constraint | Variant | Error Code |
|-----------|---------|-----------|
| Width matching | `WidthMatch(signal1, signal2, operation, span)` | E0700 |
| Width overflow | `WidthSafe(operands, operator, result_width, span)` | E0701 |
| Bounded loops | `BoundedLoop(bound, max_allowed, span)` | E0730 |
| Valid ranges | `ValidRange(hi, lo, span)` | E0740 |

### Layer 2: Structural/Graph Constraints (VhdlConstraintChecker)

New checker in `src/compiler/vhdl_constraints.spl`:

| Constraint | Implementation | Error Code |
|-----------|---------------|-----------|
| Width equal | Direct comparison | E0700 |
| Width safe | Operand width analysis | E0701 |
| Same clock domain | Graph coloring lookup | E0710 |
| CDC violation | Domain edge detection | E0710 |
| Sensitivity complete | Set comparison | E0720 |
| No comb loop | Tarjan SCC (self-loop check) | E0721 |
| No latch inference | Branch coverage analysis | E0722 |
| Loop bounded | DimSolver delegation | E0730 |
| Single driver | Driver count | E0740 |
| Resolved type | Multi-driver policy | (info) |

### Constraint Classification (Compile-time vs Runtime)

**Compile-time only** (fail before VHDL emission):

| Constraint | Reuses |
|-----------|--------|
| Width resolution | `DimSolver.unify()` + `DimConstraint.WidthMatch` |
| Bounded loops | `DimConstraint.BoundedLoop` |
| Sensitivity list completeness | Set comparison |
| Combinational loop detection | Tarjan SCC |
| Latch inference prevention | Branch coverage analysis |
| CDC domain tracking | Graph coloring |
| Single-driver enforcement | Driver count |
| Unsynthesizable construct ban | AST/MIR pattern match |

**Runtime/simulation** (emitted as VHDL `assert` with `translate_off`):

| Constraint | VHDL Output |
|-----------|-------------|
| Timing assertions | `assert ... severity error;` |
| Protocol compliance | `assert` + `report` in testbench |
| Value range checks | `assert value >= lo and value <= hi;` |

**Mixed** (compile-time where static, runtime assertion as fallback):

| Constraint | Compile-time | Runtime Fallback |
|-----------|-------------|------------------|
| Width overflow | `DimConstraint.WidthSafe` (static widths) | `assert` (generic-dependent) |
| Generic range bounds | `DimConstraint.InRange` (known constants) | `assert N <= MAX_N severity failure;` |

### Error Code Range

VHDL errors use **E07xx** (E0700-E0799):
- E0700: Width mismatch
- E0701: Width overflow
- E0710: Clock domain crossing violation
- E0720: Incomplete sensitivity list
- E0721: Combinational loop detected
- E0722: Latch inferred
- E0730: Unbounded loop
- E0740: Multiple drivers on unresolved signal
- E0750: Unsynthesizable construct

---

## Code Generation Pipeline

### Phase 1: Parsing

No new syntax for v1. `--backend=vhdl` flag triggers the VHDL pipeline.

### Phase 2: HIR Lowering

- Annotate functions with `ClockDomain` and `ProcessKind` metadata
- Detect signal kinds (Wire/Register/Port)
- Validate no unsynthesizable constructs

### Phase 3: MIR Generation

- Lower to VHDL MIR instructions (`VhdlProcess`, `VhdlSignalAssign`, etc.)
- Standard MIR instructions (BinOp, Const, etc.) used for combinational logic

### Phase 4: VHDL Code Generation

1. Run `VhdlConstraintChecker.check_all()` — fail fast on any violation
2. `VhdlTypeMapper` maps types to VHDL
3. `VhdlBuilder` emits:
   - Package (`<unit>_pkg.vhd`) with records, enums, constants
   - Entity/architecture (`<module>.vhd`)
4. Emit elaboration-time assertions for mixed constraints

---

## VHDL Backend

### VhdlTypeMapper

Location: `src/compiler/backend/vhdl_type_mapper.spl`

Maps Simple types to VHDL types using `ieee.numeric_std`:
- `signed(W-1 downto 0)` for signed integers
- `unsigned(W-1 downto 0)` for unsigned integers
- `bit` or `std_logic` for booleans (policy-dependent)
- Records for structs, enumeration types for enums
- Error for floating point (not synthesizable)

### VhdlBuilder

Location: `src/compiler/backend/vhdl/vhdl_builder.spl`

Generates VHDL-2008 source code:

```vhdl
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity adder is
    port (
        a : in unsigned(7 downto 0);
        b : in unsigned(7 downto 0);
        result_out : out unsigned(7 downto 0)
    );
end entity adder;

architecture rtl of adder is
begin
    result_out <= a + b;
end architecture rtl;
```

Key features:
- Library/use clause generation
- Package declaration (types, constants)
- Entity/port declaration
- Architecture with signal declarations
- Process generation (combinational + clocked)
- Component instantiation with port maps
- Assertion emission with synthesis pragmas

### VhdlBackend

Location: `src/compiler/backend/vhdl_backend.spl`

Orchestrates VHDL code generation:

1. Create type mapper (resolved/unresolved policy)
2. Create VHDL builder
3. Generate package for types/constants
4. For each function:
   - Emit entity with ports
   - Emit architecture with signals
   - Compile MIR instructions to VHDL statements
5. Produce final `.vhd` files

---

## Runtime Integration

### SFFI Architecture

Two-tier pattern for VHDL toolchain FFI:

```simple
# Tier 1: Raw extern declarations (process/file operations)
extern fn rt_process_run_capture(command: text, args: [text]) -> (i64, text, text)

# Tier 2: VHDL-specific wrappers
fn ghdl_analyze(vhdl_file: text) -> VhdlToolResult:
    val result = rt_process_run_capture("ghdl", ["-a", "--std=08", vhdl_file])
    vhdl_tool_result(result.0, result.1, result.2)
```

### VHDL FFI

Location: `src/app/io/vhdl_ffi.spl`

Categories:
- GHDL analysis: `ghdl_analyze`, `ghdl_elaborate`
- GHDL simulation: `ghdl_run`
- GHDL synthesis: `ghdl_synth`
- Yosys synthesis: `yosys_synth_ghdl`
- File operations: `vhdl_write_file`, `vhdl_read_file`

---

## File Locations

| Component | File |
|-----------|------|
| CoreBackendKind (Vhdl variant) | `src/compiler_core/backend_types.spl` |
| BackendKind (Vhdl variant) | `src/compiler/backend/backend_types.spl` |
| Backend helpers (vhdl name) | `src/compiler/backend/backend_helpers.spl` |
| Backend factory (Vhdl case) | `src/compiler/backend/backend_factory.spl` |
| VHDL MIR instructions | `src/compiler/mir_data.spl` |
| DimConstraint VHDL variants | `src/compiler/dim_constraints_types.spl` |
| DimSolver VHDL solving logic | `src/compiler/dim_constraints.spl` |
| VhdlConstraintChecker | `src/compiler/vhdl_constraints.spl` |
| VhdlTypeMapper | `src/compiler/backend/vhdl_type_mapper.spl` |
| VhdlBuilder | `src/compiler/backend/vhdl/vhdl_builder.spl` |
| VhdlBackend | `src/compiler/backend/vhdl_backend.spl` |
| VHDL module | `src/compiler/backend/vhdl/mod.spl` |
| VHDL FFI | `src/app/io/vhdl_ffi.spl` |

---

## Future Extensions

### VHDL-2019 Features

- Protected types for shared variables
- Conditional expressions (`when ... else`)
- Enhanced generics (type generics, subprogram generics)

### Testbench Generation

Automatic testbench generation:

```vhdl
-- Future: auto-generated testbench
entity adder_tb is end entity;
architecture sim of adder_tb is
    signal a, b, result : unsigned(7 downto 0);
begin
    uut: entity work.adder port map(a => a, b => b, result_out => result);
    stimulus: process begin
        a <= x"01"; b <= x"02"; wait for 10 ns;
        assert result = x"03" report "Test failed" severity error;
        wait;
    end process;
end architecture;
```

### Vendor-Specific Attributes

Support for FPGA vendor attributes:

```simple
# Future syntax
@vhdl_attr("KEEP_HIERARCHY", "yes")
@vhdl_attr("MARK_DEBUG", "true")
fn critical_path(...):
```

### Mixed-Language Support

Co-simulation with Verilog backend outputs via GHDL + Verilator for cross-verification.

---

## See Also

- [VHDL Support Research](../research/VHDL_SUPPORT_RESEARCH.md) - Research and toolchain analysis
- [VHDL Backend Plan](../plan/VHDL_BACKEND_PLAN.md) - Implementation milestones
- [GPU Backend Design](gpu_backend_design.md) - Pattern reference (CUDA/Vulkan)
- [Pipeline Operators Design](pipeline_operators_design.md) - Related: `~>` layer connect
