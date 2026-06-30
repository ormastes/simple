# VHDL Hardware Subset Contract

**Date:** 2026-04-04
**Status:** Active
**Scope:** Defines the exact supported hardware subset for the Simple-to-VHDL-2008 backend. All constructs outside this contract produce a hard compile error.

The VHDL backend compiles MIR to synthesizable VHDL-2008. It generates entity/architecture pairs from functions, packages from type/constant definitions, and processes from VHDL-specific MIR instructions. The backend enforces strict synthesizability: floating-point types, pointers, dynamic allocation, and general-purpose runtime features are rejected at compile time. A two-layer constraint checker (numeric width via DimSolver, structural via graph analysis) catches hardware-specific errors before any VHDL is emitted.

## 1. Quick Reference: Supported / Unsupported

| Category | Supported | Unsupported (hard error) |
|----------|-----------|--------------------------|
| **Integer types** | `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64` | -- |
| **Boolean** | `Bool` (`bit` or `std_logic`) | -- |
| **Floating-point** | -- | `f16`, `f32`, `f64` (not synthesizable) |
| **Unit** | -- | `Unit` (no VHDL signal representation) |
| **Pointers** | -- | All pointer types (not synthesizable) |
| **Arrays** | Fixed-size `Array(elem, size)` | Dynamic/unbounded arrays |
| **Structs** | Record types in packages | -- |
| **Enums** | Enumeration types in packages | -- |
| **Arithmetic** | `+`, `-`, `*`, `/` | Modulo, power |
| **Comparison** | `==`, `!=`, `<`, `<=`, `>`, `>=` | -- |
| **Bitwise** | `and`, `or`, `xor`, `shl`, `shr` | Rotate |
| **Unary** | `neg`, `not` | -- |
| **Processes** | Combinational, Clocked (rising/falling), AsyncReset | -- |
| **Instantiation** | Component port map | -- |
| **Bit manipulation** | Resize, slice, concatenation | -- |
| **Dynamic allocation** | -- | Heap, GC, closures |
| **Polymorphism** | -- | Generic without hardware lowering |
| **Side effects** | -- | I/O, print, network, filesystem |

## 2. Supported Types

Source: `vhdl_type_mapper.spl` (`VhdlTypeMapper`) and `vhdl_backend.spl` (`mir_type_to_vhdl`)

### 2.1 Integer Types

| Simple Type | VHDL Type | IEEE Library |
|-------------|-----------|--------------|
| `i8` | `signed(7 downto 0)` | `ieee.numeric_std` |
| `i16` | `signed(15 downto 0)` | `ieee.numeric_std` |
| `i32` | `signed(31 downto 0)` | `ieee.numeric_std` |
| `i64` | `signed(63 downto 0)` | `ieee.numeric_std` |
| `u8` | `unsigned(7 downto 0)` | `ieee.numeric_std` |
| `u16` | `unsigned(15 downto 0)` | `ieee.numeric_std` |
| `u32` | `unsigned(31 downto 0)` | `ieee.numeric_std` |
| `u64` | `unsigned(63 downto 0)` | `ieee.numeric_std` |

### 2.2 Boolean

| Mode | VHDL Type | When |
|------|-----------|------|
| Unresolved (default) | `bit` | `VhdlBackend.create()` |
| Resolved | `std_logic` | `VhdlBackend.create_resolved()` |

Resolved mode (`std_logic`) is required when a signal has multiple drivers (tri-state, bus). The constraint checker enforces this via `ResolvedType` and `SingleDriver` constraints.

### 2.3 Composite Types

| Simple Type | VHDL Type | Example |
|-------------|-----------|---------|
| `Array(elem, size)` | `array (0 to size-1) of elem_type` | `array (0 to 7) of signed(31 downto 0)` |
| `[Bool; N]` (vector) | `bit_vector(N-1 downto 0)` or `std_logic_vector(N-1 downto 0)` | Resolved mode selects `std_logic_vector` |
| Struct | `record ... end record` | Emitted in package |
| Enum | `type T is (V1, V2, ...)` | Emitted in package |

### 2.4 Explicitly Unsupported Types

| Type | Reason | Error |
|------|--------|-------|
| `f16`, `f32`, `f64` | Not synthesizable in standard VHDL | `"-- ERROR: fNN not synthesizable"` |
| `Unit` | No VHDL signal representation | `"Unit values cannot be lowered to a VHDL signal type"` |
| Pointers | No hardware equivalent | `"-- ERROR: pointers not synthesizable in VHDL"` |
| All others | Catch-all | `"Unsupported VHDL type: {ty.kind}"` |

## 3. Supported Constants

Source: `vhdl_backend.spl` (`const_value_to_vhdl`)

| Constant Kind | VHDL Literal | Example |
|---------------|-------------|---------|
| `Int(v)` with signed type | `to_signed(v, w)` | `to_signed(42, 32)` |
| `Int(v)` with unsigned type | `to_unsigned(v, w)` | `to_unsigned(255, 8)` |
| `Bool(true)` | `'1'` | -- |
| `Bool(false)` | `'0'` | -- |
| `Str(v)` | `"v"` | VHDL string literal |
| `Zero` | `(others => '0')` | Zero-fill aggregate |

**Unsupported constants:**

| Constant Kind | Error |
|---------------|-------|
| `Float(v)` | `"Floating-point constant {v} is not synthesizable for the VHDL backend"` |
| `Int(v)` with non-integer type | `"Integer constant requires fixed-width integer type, got {ty.kind}"` |
| All others | `"Unsupported VHDL constant: {value}"` |

## 4. Supported MIR Instructions

Source: `vhdl_backend.spl` (`compile_instruction`)

Every MIR instruction not in this table produces a hard compile error: `"Unsupported instruction: {inst.kind}"`.

### 4.1 Data Movement

| Instruction | VHDL Output | Semantics |
|-------------|------------|-----------|
| `Const(dest, value, ty)` | `dest <= literal;` | Assign constant to signal |
| `Copy(dest, src)` | `dest <= src;` | Signal copy |
| `Move(dest, src)` | `dest <= src;` | Signal copy (same as Copy in hardware) |

### 4.2 Binary Operations

| Instruction | Form |
|-------------|------|
| `BinOp(dest, op, left, right)` | `dest <= expr;` |

Supported operators and their VHDL expressions:

| MIR Operator | VHDL Expression |
|-------------|----------------|
| `Add` | `left + right` |
| `Sub` | `left - right` |
| `Mul` | `left * right` |
| `Div` | `left / right` |
| `Eq` | `'1' when left = right else '0'` |
| `Ne` | `'1' when left /= right else '0'` |
| `Lt` | `'1' when left < right else '0'` |
| `Le` | `'1' when left <= right else '0'` |
| `Gt` | `'1' when left > right else '0'` |
| `Ge` | `'1' when left >= right else '0'` |
| `BitAnd` | `left and right` |
| `BitOr` | `left or right` |
| `BitXor` | `left xor right` |
| `Shl` | `shift_left(left, to_integer(right))` |
| `Shr` | `shift_right(left, to_integer(right))` |

Any other `MirBinOp` variant produces: `"Unsupported VHDL binary operator: {op}"`.

### 4.3 Unary Operations

| MIR Operator | VHDL Expression |
|-------------|----------------|
| `Neg` | `-operand` |
| `Not` | `not operand` |

Any other `MirUnaryOp` variant produces: `"Unsupported VHDL unary operator: {op}"`.

### 4.4 VHDL-Specific Instructions

| Instruction | Purpose | VHDL Output |
|-------------|---------|------------|
| `VhdlProcess(kind, body_block)` | Process generation | See Section 5 |
| `VhdlSignalAssign(target, value, delay_ns)` | Signal assignment | `target <= value;` or `target <= value after N ns;` |
| `VhdlVarAssign(target, value)` | Variable assignment | `target := value;` |
| `VhdlPortMap(entity, instance, connections)` | Component instantiation | `label: entity work.E port map (...)` |
| `VhdlResize(dest, operand, new_width, signed)` | Bit width change | `dest <= resize(operand, new_width);` |
| `VhdlSlice(dest, signal, hi, lo)` | Bit extraction | `dest <= signal(hi downto lo);` |
| `VhdlConcat(dest, parts)` | Concatenation | `dest <= a & b & c;` |
| `Nop` | No operation | (nothing emitted) |

## 5. Supported Process Forms

Source: `vhdl_backend.spl` (`compile_process_into`)

### 5.1 Combinational Process

```vhdl
label_N: process(sensitivity_list)
begin
    -- body instructions
end process label_N;
```

The sensitivity list is provided by the `Combinational(sensitivity: [text])` variant. The constraint checker (E0720) verifies completeness.

### 5.2 Clocked Process (Rising Edge)

```vhdl
label_N: process(clk)
begin
    if rising_edge(clk) then
        -- body instructions
    end if;
end process label_N;
```

### 5.3 Clocked Process (Falling Edge)

```vhdl
label_N: process(clk)
begin
    if falling_edge(clk) then
        -- body instructions
    end if;
end process label_N;
```

### 5.4 Asynchronous Reset Process

```vhdl
label_N: process(clk, rst)
begin
    if rst = '1' then
        -- async reset branch
    elsif rising_edge(clk) then
        -- body instructions
    end if;
end process label_N;
```

The clock edge (rising or falling) is determined by the `VhdlClockDomain.edge` field. The reset signal is optional in `VhdlClockDomain.reset_signal`.

### 5.5 Clock Domain Definition

```simple
struct VhdlClockDomain:
    name: text
    clock_signal: text
    reset_signal: text?
    edge: VhdlClockEdge       # Rising | Falling
```

## 6. Entity/Architecture Structure

Source: `vhdl_backend.spl` (`compile_function`)

Each MIR function compiles to one entity/architecture pair.

### 6.1 Entity Ports

| MIR Local Kind | Port Direction | Naming |
|----------------|---------------|--------|
| `Arg(idx)` | `in` | Named parameter or `p{idx}` |
| `Return` | `out` | Always `result_out` |

### 6.2 Architecture Signals

| MIR Local Kind | Declaration | Naming |
|----------------|------------|--------|
| `Var` | `signal name : type;` | Named variable or `sig_{id}` |
| `Temp` | `signal name : type;` | Named variable or `sig_{id}` |

### 6.3 Generated Structure

```vhdl
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity func_name is
    port (
        param1 : in signed(31 downto 0);
        param2 : in signed(31 downto 0);
        result_out : out signed(31 downto 0)
    );
end entity func_name;

architecture rtl of func_name is
    signal sig_3 : signed(31 downto 0);
begin
    -- Block BB0
    sig_3 <= param1 + param2;
    result_out <= sig_3;
end architecture rtl;
```

The architecture name is always `rtl`.

## 7. Package Support

Source: `vhdl_backend.spl` (`compile_package_into`)

Packages are generated when the module has type or constant definitions. The package name is `{module_name}_pkg`.

### 7.1 Supported Package Contents

| Definition | VHDL Output |
|-----------|------------|
| `Struct(fields)` | `type T is record ... end record;` |
| `Enum(variants)` | `type T is (V1, V2, V3);` |
| Constants | `constant N : type := value;` |

### 7.2 Unsupported Package Types

Any type definition kind other than `Struct` or `Enum` produces: `"Unsupported VHDL package type definition: {type_def.name}"`.

## 8. Constraint Verification (E07xx)

Source: `vhdl_constraints.spl` (`VhdlConstraintChecker`)

All constraints are checked at compile time before VHDL emission. The checker uses two layers: numeric/width constraints delegated to `DimSolver`, and structural/graph constraints analyzed directly.

### 8.1 Error Codes

| Code | Constraint | Detection Method | Message Pattern |
|------|-----------|------------------|-----------------|
| **E0700** | Width mismatch | `WidthEqual` — direct comparison | `"width mismatch: signal '{s1}' is {w1} bits, '{s2}' is {w2} bits"` |
| **E0701** | Width overflow | `WidthSafe` — operator-aware needed-width calculation | `"width overflow: '{op}' needs {n} bits, result has {r}"` |
| **E0710** | Clock domain crossing | `SameClockDomain` — domain registry lookup; `ClockDomainCrossing` — explicit unsafe crossing | `"clock domain crossing: ..."` or `"unsynchronized clock domain crossing: ..."` |
| **E0720** | Incomplete sensitivity list | `SensitivityComplete` — set difference of used signals vs. sensitivity list | `"incomplete sensitivity list in process '{label}': missing {sigs}"` |
| **E0721** | Combinational loop | `NoCombLoop` — Tarjan SCC on signal dependency graph | `"combinational loop detected: a -> b -> a"` |
| **E0722** | Latch inference | `NoLatchInference` — branch coverage analysis per signal | `"latch inferred in process '{label}': signals {sigs} not assigned in all branches"` |
| **E0730** | Unbounded loop | `LoopBounded` — iteration count policy check | `"loop bound must be positive: '{expr}' evaluates to {n}"` |
| **E0740** | Multiple drivers on unresolved signal | `SingleDriver` — driver count per signal | `"multiple drivers on unresolved signal '{sig}': driven by {drivers}"` |

### 8.2 Width Overflow Calculation

The `WidthSafe` constraint computes the minimum needed width based on the operator:

| Operator | Needed Width |
|----------|-------------|
| `+`, `-` | `max(operand widths) + 1` |
| `*` | `sum(operand widths)` |
| All others | `max(operand widths)` |

### 8.3 Combinational Loop Detection

The checker uses Tarjan's Strongly Connected Components algorithm (`TarjanSCC` class) on the signal dependency graph. Any SCC with size > 1 is a multi-signal cycle. A size-1 SCC with a self-edge is a self-loop. Both are reported as E0721.

### 8.4 Constraint Enum

```simple
enum VhdlConstraint:
    WidthEqual(signal1, signal2, width1, width2, span)
    WidthSafe(operands, operator, result_width, span)
    SameClockDomain(signal1, signal2, span)
    ClockDomainCrossing(source, dest, source_domain, dest_domain, span)
    SensitivityComplete(process_label, used_signals, sensitivity, span)
    NoCombLoop(signals, dependencies, span)
    NoLatchInference(process_label, assigned_signals, branch_coverage, span)
    LoopBounded(bound_expr, max_iterations, span)
    SingleDriver(signal, drivers, span)
    ResolvedType(signal, has_multiple_drivers, span)
```

## 9. VHDL Builder Capabilities

Source: `vhdl_builder.spl` (`VhdlBuilder`)

The builder emits VHDL-2008 source text with automatic indentation management and label allocation.

### 9.1 Library Header

Every generated file starts with:

```vhdl
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
```

### 9.2 Supported Constructs

| Builder Method | VHDL Construct |
|---------------|---------------|
| `emit_entity_begin/end` | Entity declaration |
| `emit_port` | Port declaration (`in`, `out`, `inout`, `buffer`) |
| `emit_generic_param` | Generic parameter (with optional default) |
| `emit_architecture_begin/end` | Architecture body |
| `emit_signal_decl` | Signal declaration (optional default) |
| `emit_process_begin/end` | Combinational process |
| `emit_clocked_process_begin` | Clocked process (with optional reset) |
| `emit_signal_assign` | Signal assignment (`<=`) |
| `emit_signal_assign_delay` | Signal assignment with delay (`<= ... after N ns`) |
| `emit_var_assign` | Variable assignment (`:=`) |
| `emit_if_begin/elsif/else/end` | Conditional statements |
| `emit_rising_edge_check` | `if rising_edge(clk) then` |
| `emit_falling_edge_check` | `if falling_edge(clk) then` |
| `emit_for_loop_begin/end` | Statically bounded for loop |
| `emit_instance_begin` | Component instantiation (`entity work.E`) |
| `emit_port_map_begin/entry/end` | Port map association |
| `emit_resize` | `resize(signal, width)` |
| `emit_slice` | `signal(hi downto lo)` |
| `emit_concat` | `a & b & c` |
| `emit_assert` | Assertion with report and severity |
| `emit_synthesis_translate_off/on` | Synthesis pragmas |
| `emit_package_begin/end` | Package declaration |
| `emit_type_decl` | Type definition |
| `emit_constant_decl` | Constant declaration |

## 10. Trait Implementations

### 10.1 Codegen Trait

The `VhdlBackend` implements the `Codegen` trait:
- `backend_kind()` returns `BackendKind.Vhdl`
- `backend_name()` returns `"vhdl"`
- `supports_target()` returns `true` for all targets
- `output_kind()` returns `CodegenOutputKind.TextSource`
- `compile_module()` produces combined package + entity VHDL text

### 10.2 HardwareCodegen Trait

The `VhdlBackend` implements the `HardwareCodegen` trait:
- `compile_entity(func_name, body)` compiles a single function body to entity/architecture VHDL
- `compile_package(module)` compiles type/constant definitions to a VHDL package
- `compile_process(kind, body_block)` compiles a single process (Combinational, Clocked, or AsyncReset)

## 11. Explicitly Deferred

The following are out of scope for this backend and produce compile errors if encountered:

- **Floating-point types** -- `f16`, `f32`, `f64` are not synthesizable in standard VHDL
- **Dynamic heap allocation** -- no `new`, no GC, no closures
- **General polymorphism** -- generic type parameters must be monomorphized before reaching the VHDL backend
- **Open-ended runtime features** -- no I/O, no print, no network, no filesystem
- **Arbitrary side effects** -- all effects must be expressible as signal/variable assignments or process bodies
- **General-purpose Simple-to-hardware compilation** -- only the MIR instructions listed in Section 4 are accepted; the backend is not a general HLS tool

## 12. Source Files

| File | Lines | Role |
|------|-------|------|
| `src/compiler/70.backend/backend/vhdl_backend.spl` | ~680 | Main backend: MIR-to-VHDL compilation, type mapping, operator mapping |
| `src/compiler/70.backend/backend/vhdl_type_mapper.spl` | ~212 | Type mapper: MIR types to VHDL type strings, synthesizability checks |
| `src/compiler/70.backend/vhdl_constraints.spl` | ~404 | Constraint checker: width, CDC, sensitivity, comb loops, latches, drivers |
| `src/compiler/70.backend/backend/vhdl/vhdl_builder.spl` | ~358 | Code emitter: VHDL-2008 text generation with indentation management |
