# VHDL Backend User Guide

**Version:** 0.1.0
**Status:** In Progress
**Last Updated:** 2026-02-11

## Table of Contents

1. [Introduction](#introduction)
2. [Setup](#setup)
3. [Quick Start](#quick-start)
4. [Type Mapping](#type-mapping)
5. [Entity Generation](#entity-generation)
6. [Process Model](#process-model)
7. [Verification Constraints](#verification-constraints)
8. [Examples](#examples)
9. [Toolchain Integration](#toolchain-integration)
10. [Troubleshooting](#troubleshooting)
11. [Limitations](#limitations)

## Introduction

The VHDL backend generates synthesizable VHDL-2008 source code from Simple programs. It produces `.vhd` files suitable for FPGA synthesis and ASIC simulation.

### When to Use the VHDL Backend

**Good Use Cases:**
- FPGA design and prototyping
- Digital logic synthesis (counters, ALUs, FSMs)
- Hardware description from high-level Simple specifications
- Generating testable VHDL with compile-time verification

**Not Recommended:**
- Software-only applications (use Cranelift/LLVM backends)
- Floating-point heavy workloads (f32/f64 are not synthesizable)
- Dynamic memory allocation (no pointers in VHDL)

## Setup

### Prerequisites

**Required:**
- Simple compiler (`bin/simple`)

**Optional (for verification):**
- [GHDL](https://github.com/ghdl/ghdl) - VHDL analysis, elaboration, and simulation
- [Yosys](https://github.com/YosysHQ/yosys) + ghdl-yosys-plugin - Open-source synthesis

### Installing GHDL

#### Ubuntu/Debian

```bash
sudo apt-get install ghdl
```

#### macOS (Homebrew)

```bash
brew install ghdl
```

#### From Source

```bash
git clone https://github.com/ghdl/ghdl.git
cd ghdl
./configure --with-llvm-config
make && sudo make install
```

### Installing Yosys (Optional)

```bash
# Ubuntu/Debian
sudo apt-get install yosys

# macOS
brew install yosys
```

### Verify Installation

```bash
ghdl --version
yosys --version  # optional
```

## Quick Start

### 1. Compile Simple to VHDL

```bash
simple compile --backend=vhdl -o counter.vhd examples/vhdl/counter.spl
```

### 2. Verify with GHDL

```bash
ghdl -a --std=08 counter.vhd   # Analyze (syntax + semantic check)
ghdl -e --std=08 counter        # Elaborate
ghdl -r --std=08 counter --stop-time=100ns  # Simulate
```

### 3. Synthesize with Yosys (optional)

```bash
yosys -m ghdl -p "ghdl --std=08 -a counter.vhd; ghdl --std=08 counter; synth -top counter"
```

## Type Mapping

The VHDL backend maps Simple types to IEEE 1076-2008 types:

| Simple Type | VHDL (Unresolved) | VHDL (Resolved) |
|-------------|-------------------|-----------------|
| `bool` | `bit` | `std_logic` |
| `i8` | `signed(7 downto 0)` | same |
| `i16` | `signed(15 downto 0)` | same |
| `i32` | `signed(31 downto 0)` | same |
| `i64` | `signed(63 downto 0)` | same |
| `u8` | `unsigned(7 downto 0)` | same |
| `u16` | `unsigned(15 downto 0)` | same |
| `u32` | `unsigned(31 downto 0)` | same |
| `u64` | `unsigned(63 downto 0)` | same |
| `[bool; N]` | `bit_vector(N-1 downto 0)` | `std_logic_vector(N-1 downto 0)` |
| `struct` | `record` | `record` |
| `enum` | `type ... is (...)` | same |
| `f32`/`f64` | **Error** (not synthesizable) | **Error** |

### Resolved vs Unresolved Types

By default, the backend uses **unresolved** types (`bit`, `bit_vector`). Use resolved types (`std_logic`, `std_logic_vector`) when:
- Multiple drivers exist on a signal (tri-state buses)
- Interfacing with existing std_logic-based IP
- Using vendor-specific primitives

## Entity Generation

Simple functions compile to VHDL entity/architecture pairs:

```simple
# Simple source
fn adder(a: i32, b: i32) -> i32:
    a + b
```

Produces:

```vhdl
entity adder is
    port (
        a : in signed(31 downto 0);
        b : in signed(31 downto 0);
        result_out : out signed(31 downto 0)
    );
end entity adder;

architecture rtl of adder is
begin
    result_out <= a + b;
end architecture rtl;
```

### Packages

Shared types and constants are emitted in a package (`<module>_pkg.vhd`):

```vhdl
package my_module_pkg is
    type state_t is (Idle, Running, Done);
    constant WIDTH : integer := 32;
end package my_module_pkg;
```

## Process Model

The VHDL backend supports three process types:

### Combinational Process

Sensitivity list includes all read signals. No clock or reset.

```vhdl
process(a, b, sel)
begin
    if sel = '1' then
        y <= a;
    else
        y <= b;
    end if;
end process;
```

### Clocked Process

Rising or falling edge of a clock signal.

```vhdl
process(clk)
begin
    if rising_edge(clk) then
        q <= d;
    end if;
end process;
```

### Clocked Process with Async Reset

```vhdl
process(clk, rst)
begin
    if rst = '1' then
        q <= (others => '0');
    elsif rising_edge(clk) then
        q <= d;
    end if;
end process;
```

## Verification Constraints

The VHDL backend enforces compile-time verification constraints before emitting code. All constraints produce errors in the **E07xx** range.

### Width Matching (E0700)

Signal widths must match for assignments:

```
error[E0700]: width mismatch: signal 'a' is 8 bits, 'b' is 16 bits
```

### Width Overflow (E0701)

Arithmetic results must fit in the destination:

```
error[E0701]: width overflow: '*' needs 64 bits, result has 32
```

### Clock Domain Crossing (E0710)

Signals must not cross clock domains without synchronization:

```
error[E0710]: clock domain crossing: 'tx_data' (clk_tx) and 'rx_data' (clk_rx) are in different domains
```

### Incomplete Sensitivity List (E0720)

Combinational processes must list all read signals:

```
error[E0720]: incomplete sensitivity list in process 'comb': missing sel
```

### Combinational Loop (E0721)

No signal may depend on itself combinationally:

```
error[E0721]: combinational loop detected: signal 'x' depends on itself
```

### Latch Inference (E0722)

All signals must be assigned in all branches:

```
error[E0722]: latch inferred in process 'mux': signals out2 not assigned in all branches
```

### Unbounded Loop (E0730)

Loops must have statically bounded iteration counts:

```
error[E0730]: loop bound must be positive: '0' evaluates to 0
```

### Multiple Drivers (E0740)

Unresolved signals must have exactly one driver:

```
error[E0740]: multiple drivers on unresolved signal 'bus': driven by proc_a, proc_b
```

## Examples

### 8-bit Counter with Reset

See `examples/vhdl/counter.spl` -> `examples/vhdl/golden/counter.vhd`

### Simple ALU

See `examples/vhdl/alu.spl` -> `examples/vhdl/golden/alu.vhd`

### Traffic Light FSM

See `examples/vhdl/fsm.spl` -> `examples/vhdl/golden/fsm.vhd`

## Toolchain Integration

### SFFI Functions

The VHDL FFI module (`src/app/io/vhdl_ffi.spl`) provides:

```simple
# Check tool availability
ghdl_available() -> bool
yosys_available() -> bool

# GHDL operations
ghdl_analyze(vhdl_file: text) -> VhdlToolResult
ghdl_elaborate(entity_name: text) -> VhdlToolResult
ghdl_run(entity_name: text, stop_time: text?) -> VhdlToolResult
ghdl_synth(entity_name: text) -> VhdlToolResult
ghdl_analyze_and_elaborate(vhdl_file: text, entity_name: text) -> VhdlToolResult

# Yosys synthesis
yosys_synth_ghdl(vhdl_file: text, entity_name: text, output_json: text) -> VhdlToolResult

# File operations
vhdl_write_file(path: text, content: text) -> bool
vhdl_read_file(path: text) -> text?
vhdl_file_exists(path: text) -> bool
```

### CI Integration

A GitHub Actions workflow (`.github/workflows/vhdl-tests.yml`) runs GHDL analysis and elaboration on golden files for every push to `main`.

## Troubleshooting

### GHDL: "entity not found"

Ensure you analyze the file before elaborating:
```bash
ghdl -a --std=08 file.vhd  # Must come first
ghdl -e --std=08 entity_name
```

### E0700: Width mismatch

Check that both sides of an assignment have the same bit width. Use `resize()` for explicit width conversion.

### E0710: Clock domain crossing

Add a two-flop synchronizer between clock domains, or use the `--allow-cdc` flag for simulation-only code.

### E0722: Latch inferred

Add a default assignment at the start of the process:
```vhdl
process(a, b, sel)
begin
    y <= '0';  -- Default prevents latch
    if sel = '1' then
        y <= a;
    end if;
end process;
```

## Limitations

### Current Limitations (v0.1)

- **No floating-point**: `f16`, `f32`, `f64` are not synthesizable
- **No pointers**: Hardware has no pointer concept
- **No dynamic allocation**: All sizes must be known at compile time
- **No recursion**: Recursive functions cannot be synthesized
- **Bounded loops only**: All loops must have static iteration bounds
- **Full MIR pipeline not yet wired**: `simple compile --backend=vhdl` delegates to runtime; direct source-to-VHDL compilation is in progress

### Planned Improvements

- Generic entity parameters from Simple compile-time constants
- Automatic FSM conversion from bounded while loops
- Mixed resolved/unresolved type inference
- Testbench generation from SSpec test cases
- Waveform dump integration for debugging
