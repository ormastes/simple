# SFFI-to-VHDL Hardware Guide

**Version:** 1.0.0
**Status:** Active

---

## Overview

Simple's SFFI (Simple Foreign Function Interface) extends beyond C/C++/Rust to
cover the **hardware domain**: writing synthesizable RTL in `.spl`, compiling it
to VHDL-2008 through the VHDL backend, simulating with GHDL, and synthesizing
for FPGA targets. This guide covers the complete workflow from Simple source to
running hardware.

**Key distinction:** The standard SFFI guide (`doc/07_guide/ffi/sffi.md`) covers
software FFI (C/C++/Rust interop). This guide covers the **hardware FFI path**:
Simple source to VHDL to silicon.

---

## Architecture

The hardware SFFI has two complementary paths:

```
Path 1: Compilation (Simple -> VHDL)
   .spl source  ->  MIR  ->  VHDL Backend  ->  .vhd files
                                |
                          VhdlBuilder (code emitter)
                          VhdlTypeMapper (type conversion)
                          VhdlConstraintChecker (E07xx errors)

Path 2: Tool Invocation (SFFI -> GHDL/Yosys)
   .spl source  ->  vhdl_ffi.spl  ->  rt_process_run_capture()
                          |
                    ghdl_analyze() / ghdl_elaborate() / ghdl_run()
                    yosys_synth_ghdl()
```

Path 1 **generates** VHDL from Simple source. Path 2 **invokes** EDA tools on
the generated VHDL. Both use the SFFI pattern (extern declarations + safe
wrappers) but target different audiences:

| Path | Who uses it | What it does |
|------|-------------|-------------|
| Compilation | The compiler | Translates `.spl` RTL modules to `.vhd` |
| Tool Invocation | Build scripts, test runners | Drives GHDL/Yosys from Simple code |

---

## ABI Layer (VHDL-PARITY-020)

The ABI layer (`src/compiler/70.backend/backend/vhdl/vhdl_abi.spl`) resolves
how MIR function signatures map to VHDL entity ports. It handles type-to-signal
mapping, port name sanitization, and return ABI decomposition.

**Key structs:**

| Struct | Purpose |
|--------|---------|
| `VhdlAbiPort` | Single entity port (name, direction, VHDL type) |
| `VhdlAbiReturnField` | One output port from return ABI (name, type, index) |
| `VhdlAbiReturn` | Resolved return ABI — scalar or tuple |

**Return ABI rules:**

| Return Type | Port Mapping |
|-------------|-------------|
| `Unit` | No output ports |
| Scalar (`i32`, `bool`, etc.) | Single `result_out` port |
| Labeled tuple `(sum: bool, cout: bool)` | Named ports from labels (`sum`, `cout`) |
| Anonymous tuple `(bool, bool)` | Numbered ports (`out_0`, `out_1`) |

**Functions:**

| Function | What it does |
|----------|-------------|
| `vhdl_data_width_bits(ty)` | Data width in bits (nil for unsynthesizable) |
| `vhdl_signal_type_for(ty, mapper)` | MIR type to VHDL signal type string |
| `vhdl_abi_sanitize_port_name(name)` | VHDL-safe port identifier |
| `vhdl_resolve_return_abi(func, mapper)` | Return type to output port list |
| `vhdl_resolve_input_ports(func, mapper)` | Parameters to input port list |
| `vhdl_resolve_all_ports(func, mapper)` | Combined input + output ports |
| `vhdl_abi_check_port_collisions(ports)` | Duplicate name diagnostics |
| `vhdl_abi_validate_output(func)` | Unsynthesizable return type diagnostics |

Test coverage: 37 cases in `test/unit/compiler/backend/vhdl_abi_spec.spl`.

---

## Prerequisites

Install the required EDA tools:

```bash
# GHDL (VHDL simulator + synthesis frontend)
# Ubuntu/Debian:
sudo apt install ghdl

# Yosys (optional, for synthesis)
sudo apt install yosys

# RISC-V cross-toolchain (for baremetal software tests)
sudo apt install gcc-riscv64-linux-gnu binutils-riscv64-linux-gnu

# Verify installation
ghdl --version
yosys --version  # optional
```

---

## Quick Start: Write, Compile, Simulate

### Step 1: Write RTL in Simple

Create a hardware module using only the synthesizable subset. The VHDL backend
enforces this — unsupported constructs produce hard compile errors.

```simple
# my_adder.spl — A simple combinational adder

struct AdderPorts:
    a_in: i32
    b_in: i32
    sum_out: i32

fn adder(a: i32, b: i32) -> i32:
    a + b
```

**Hardware subset rules** (full reference: `doc/04_architecture/vhdl_hardware_subset_contract.md`):

| Allowed | NOT allowed |
|---------|-------------|
| `i8`-`i64`, `u8`-`u64`, `Bool` | `f16`, `f32`, `f64` (not synthesizable) |
| Fixed-size arrays `[i32; 8]` | Dynamic arrays, heap, GC |
| Structs, Enums | Closures, polymorphism, pointers |
| `+`, `-`, `*`, `/`, bitwise ops | I/O, print, network, filesystem |
| Combinational / Clocked / AsyncReset processes | Arbitrary side effects |

### Step 2: Compile to VHDL

The VHDL backend (`src/compiler/70.backend/backend/vhdl/`) compiles MIR to
VHDL-2008. Each function becomes an entity/architecture pair:

```simple
# compile_to_vhdl.spl — Example compilation script
use std.io.vhdl_ffi.*

fn main():
    # The VHDL backend produces .vhd output from .spl source.
    # In practice, the compiler pipeline handles this:
    #   bin/simple build --backend=vhdl my_adder.spl -o my_adder.vhd
    #
    # The generated VHDL follows this structure:
    #   library ieee;
    #   use ieee.std_logic_1164.all;
    #   use ieee.numeric_std.all;
    #
    #   entity adder is
    #       port (
    #           a : in signed(31 downto 0);
    #           b : in signed(31 downto 0);
    #           result_out : out signed(31 downto 0)
    #       );
    #   end entity adder;
    #
    #   architecture rtl of adder is
    #   begin
    #       result_out <= a + b;
    #   end architecture rtl;

    print "VHDL backend compiles .spl -> .vhd via MIR pipeline"
```

### Step 3: Simulate with GHDL

Use the SFFI tool wrappers to drive GHDL:

```simple
# simulate.spl — Run GHDL simulation from Simple
use std.io.vhdl_ffi.*

fn main():
    if not ghdl_available():
        print "GHDL not installed"
        return

    # Analyze VHDL source
    val analyze = ghdl_analyze("/tmp/my_adder.vhd")
    if not analyze.success:
        print "Analysis failed: {analyze.stderr}"
        return

    # Elaborate top entity
    val elab = ghdl_elaborate("adder")
    if not elab.success:
        print "Elaboration failed: {elab.stderr}"
        return

    # Run simulation
    val sim = ghdl_run("adder", Some("100ns"))
    if sim.success:
        print "Simulation passed"
        print sim.stdout
    else:
        print "Simulation failed: {sim.stderr}"
```

### Step 4: Synthesize (Optional)

For FPGA synthesis via Yosys + GHDL plugin:

```simple
use std.io.vhdl_ffi.*

fn main():
    if not yosys_available():
        print "Yosys not installed"
        return

    val result = yosys_synth_ghdl(
        "/tmp/my_adder.vhd",
        "adder",
        "/tmp/adder_synth.json"
    )
    if result.success:
        print "Synthesis complete: /tmp/adder_synth.json"
```

---

## SFFI Tool Bindings Reference

All hardware tool bindings live in `src/lib/nogc_sync_mut/io/vhdl_ffi.spl`.

### Tier 1: Raw Externs

```simple
extern fn rt_process_run(command: text, args: [text]) -> i64
extern fn rt_process_run_capture(command: text, args: [text]) -> (i64, text, text)
extern fn rt_file_exists(path: text) -> bool
extern fn rt_file_read_text(path: text) -> text
extern fn rt_file_write_text(path: text, content: text) -> bool
```

### Tier 2: Safe Wrappers

| Function | Signature | Description |
|----------|-----------|-------------|
| `ghdl_available` | `() -> bool` | Check if GHDL is installed |
| `ghdl_analyze` | `(vhdl_file: text) -> VhdlToolResult` | VHDL syntax + semantic check |
| `ghdl_elaborate` | `(entity_name: text) -> VhdlToolResult` | Elaborate entity for simulation |
| `ghdl_run` | `(entity_name: text, stop_time: text?) -> VhdlToolResult` | Run simulation |
| `ghdl_synth` | `(entity_name: text) -> VhdlToolResult` | Synthesize (produce netlists) |
| `ghdl_analyze_and_elaborate` | `(vhdl_file: text, entity_name: text) -> VhdlToolResult` | Combined analyze + elaborate |
| `yosys_available` | `() -> bool` | Check if Yosys is installed |
| `yosys_synth_ghdl` | `(vhdl_file: text, entity_name: text, output_json: text) -> VhdlToolResult` | Synthesize via Yosys+GHDL plugin |
| `vhdl_write_file` | `(path: text, content: text) -> bool` | Write VHDL source |
| `vhdl_read_file` | `(path: text) -> text?` | Read VHDL source |
| `vhdl_file_exists` | `(path: text) -> bool` | Check VHDL file existence |

### VhdlToolResult Struct

```simple
struct VhdlToolResult:
    success: bool       # true if exit_code == 0
    exit_code: i64      # process exit code
    stdout: text        # standard output
    stderr: text        # standard error
```

---

## VHDL Backend Internals

### Type Mappings

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
| `Bool` (default) | `bit` | built-in |
| `Bool` (resolved) | `std_logic` | `ieee.std_logic_1164` |
| Fixed-size array | `array (0 to N-1) of elem_type` | -- |
| Struct | `record ... end record` | in package |
| Enum | `type T is (V1, V2, ...)` | in package |

### Operator Mappings

| Simple | VHDL | Notes |
|--------|------|-------|
| `+` | `+` | Width overflow checked (E0701) |
| `-` | `-` | Width overflow checked (E0701) |
| `*` | `*` | Product width = sum of operand widths |
| `/` | `/` | -- |
| `==` | `= '1' when ... else '0'` | Returns bit/std_logic |
| `and` | `and` | Bitwise AND |
| `or` | `or` | Bitwise OR |
| `xor` | `xor` | Bitwise XOR |
| `shl` | `shift_left(...)` | -- |
| `shr` | `shift_right(...)` | -- |
| `not` | `not` | -- |
| `neg` | `-` | Unary negation |

### Process Forms

Three hardware process forms are supported via `VhdlProcessKind`:

**Combinational** — sensitivity-list driven, no clock:
```simple
# Compiles to: process(a, b) begin ... end process;
```

**Clocked** — rising or falling edge:
```simple
# Compiles to: process(clk) begin if rising_edge(clk) then ... end if; end process;
```

**AsyncReset** — asynchronous reset with clock:
```simple
# Compiles to: process(clk, rst) begin
#   if rst = '1' then ... elsif rising_edge(clk) then ... end if;
# end process;
```

### Constraint Checker (E07xx Errors)

The VHDL backend runs a two-layer constraint checker **before** emitting any VHDL:

| Code | What it catches | Fix |
|------|----------------|-----|
| E0700 | Width mismatch between signals | Match bit widths explicitly |
| E0701 | Width overflow from arithmetic | Use wider result type |
| E0710 | Clock domain crossing (CDC) | Add synchronizer or use same domain |
| E0720 | Incomplete sensitivity list | Add all read signals to sensitivity |
| E0721 | Combinational loop | Break the cycle with a register |
| E0722 | Latch inference | Assign all signals in all branches |
| E0730 | Unbounded loop | Use statically bounded loop |
| E0740 | Multiple drivers on unresolved signal | Use `std_logic` (resolved mode) or single driver |

---

## RISC-V RTL Modules

The repo contains behavioral RISC-V hardware models written in Simple:

### Width-Agnostic Common Modules

```
src/lib/hardware/riscv_common/
    xlen.spl        -- Xlen enum (Xlen32/Xlen64) + XlenConfig
    registers.spl   -- RegisterFile: 32 registers, x0 hardwired zero
    decode.spl      -- DecodedInsn from 32-bit instruction (all 6 formats)
    alu.spl         -- ALU: ADD/SUB/SLL/SLT/SLTU/XOR/SRL/SRA/OR/AND
    memory.spl      -- MemoryBus trait + FlatMemory
    csr_defs.spl    -- CSR address constants
    platform.spl    -- RiscvPlatform contract
```

### RTL Core Modules (for VHDL compilation)

```
src/lib/hardware/rv32i_rtl/
    pc.spl          -- Program counter, branch/jump mux
    decode.spl      -- Combinational instruction decoder
    regfile.spl     -- 32x32 register file (2R1W, x0=0)
    alu.spl         -- RV32I ALU
    lsu.spl         -- Load/store unit
    core.spl        -- Single-cycle top-level
    csr.spl         -- M-mode CSRs
    trap.spl        -- Trap controller FSM
    mmu_sv32.spl    -- Sv32 page table walker + TLB
    csr_s.spl       -- S-mode CSRs
```

### SoC Peripherals

```
src/lib/hardware/soc_rtl/
    uart16550.spl       -- UART with 16-byte FIFOs, Wishbone slave
    clint.spl           -- CLINT: mtime, mtimecmp, msip
    plic.spl            -- PLIC: 32 sources, priority, claim/complete
    bootrom.spl         -- 4KB ROM at 0x00001000
    ram.spl             -- Synchronous SRAM (BRAM on FPGA)
    wb_interconnect.spl -- Wishbone B4 bus, address decode
    soc_top.spl         -- Full SoC wiring
    eth_mac.spl         -- Ethernet MAC stub
```

### Reference VHDL (Handwritten)

```
examples/09_embedded/fpga_riscv/rtl/
    rv32i_pkg.vhd       -- Type package
    alu.vhd             -- ALU
    decoder.vhd         -- Instruction decoder
    regfile.vhd         -- Register file
    rv32i_core.vhd      -- Full RV32I core
    tb_*.vhd            -- 13 GHDL testbenches
```

---

## FPGA Bundle Generation

Generate a complete FPGA RTL bundle with board profile:

```bash
# List supported boards
bin/simple run src/lib/hardware/fpga_linux/riscv_fpga_linux.spl -- --list-boards

# Generate generic bundle
bin/simple run src/lib/hardware/fpga_linux/riscv_fpga_linux.spl -- /tmp/fpga_bundle

# Generate for specific board
bin/simple run src/lib/hardware/fpga_linux/riscv_fpga_linux.spl -- --board=mlk_s02_100t /tmp/mlk_bundle
```

The bundle contains:
- `riscv_fpga_rtl_manifest.sdn` -- Build manifest
- `vivado_project_plan.tcl` -- Vivado TCL scaffold
- `board_interface_contract.sdn` -- Logical I/O contract
- `rv64/rtl/simple_rv64gc_core.spl` -- Generated Simple RTL sketch
- `rv64/rtl/simple_rv64gc_core.vhd` -- Generated VHDL

Supported boards: `xilinx_generic`, `mlk_s02_100t`, `kria_k26`

See `doc/07_guide/hardware/simple_generated_fpga_rtl.md` for bundle details.

---

## GHDL Simulation Runners

Pre-built runner scripts drive GHDL simulation for RISC-V cores:

```bash
# RV32 smoke test (uses reference VHDL)
bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv32_runner.shs \
    examples/09_embedded/fpga_riscv/sw/generated_rv32_smoke.s

# RV32 mailbox test
bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv32_mailbox_runner.shs \
    examples/09_embedded/fpga_riscv/sw/generated_rv32_mailbox.s

# RV64 (currently skips — no RV64 VHDL core yet)
bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_runner.shs \
    examples/09_embedded/fpga_riscv/sw/generated_rv64_smoke.s
```

Run via the test framework:

```bash
# All GHDL tests
bin/simple test test/feature/baremetal/

# Specific test
bin/simple test test/feature/baremetal/ghdl_generated_riscv32_smoke_spec.spl

# Slow tests only (GHDL simulation)
bin/simple test --only-slow test/feature/baremetal/
```

---

## End-to-End Workflow

### From Simple to FPGA Bitstream

```
1. Write RTL in .spl (hardware subset only)
       |
2. Compile: bin/simple build --backend=vhdl module.spl -o module.vhd
       |
3. Verify constraints: E07xx checker runs automatically during compilation
       |
4. Simulate: ghdl_analyze() + ghdl_elaborate() + ghdl_run()
       |       or: use runner scripts for RISC-V cores
       |
5. Generate FPGA bundle: riscv_fpga_linux.spl -- --board=<board> <output>
       |
6. Synthesize: yosys_synth_ghdl() or Vivado via generated TCL
       |
7. Program FPGA: vendor tools (Vivado, openFPGALoader)
```

### Current Status and Gaps

| Step | Status | Notes |
|------|--------|-------|
| Write .spl RTL | Done | `rv32i_rtl/`, `soc_rtl/` modules exist |
| VHDL backend compilation | Done | 18-file backend, type mapper, constraint checker |
| SFFI tool bindings | Done | `vhdl_ffi.spl` wraps GHDL + Yosys |
| GHDL simulation (reference VHDL) | Working | Handwritten VHDL at `examples/09_embedded/` passes |
| GHDL simulation (generated VHDL) | Gap | `write_stub_rtl()` produces placeholders, not real VHDL |
| FPGA bundle generation | Working | Board profiles, manifests, TCL scaffolds |
| Synthesis | Gap | Requires generated VHDL, not stubs |
| RV64 VHDL core | Gap | No RV64 reference or generated VHDL exists |

The critical remaining step is wiring the VHDL backend to compile the `.spl` RTL
modules in `rv32i_rtl/` and `soc_rtl/` into real `.vhd` files, replacing the
current placeholder stubs in `riscv_fpga_linux.spl:write_stub_rtl()`.

---

## VHDL Backend Source Files

| File | Role |
|------|------|
| `src/compiler/70.backend/backend/vhdl/vhdl_backend.spl` | Main backend: MIR to VHDL |
| `src/compiler/70.backend/backend/vhdl/vhdl_type_mapper.spl` | Type conversion |
| `src/compiler/70.backend/backend/vhdl/vhdl_builder.spl` | VHDL-2008 code emitter |
| `src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl` | Shared utilities |
| `src/compiler/70.backend/backend/vhdl/vhdl_rv32i_decode.spl` | RV32I decode template |
| `src/compiler/70.backend/backend/vhdl/vhdl_register_file.spl` | Register file template |
| `src/compiler/70.backend/backend/vhdl/vhdl_memory_templates.spl` | Block RAM/ROM templates |
| `src/compiler/70.backend/backend/vhdl/vhdl_testbench.spl` | Testbench renderer |
| `src/compiler/70.backend/backend/vhdl/vhdl_testbench_converter.spl` | Testbench conversion |
| `src/compiler/70.backend/backend/vhdl/vhdl_abi.spl` | Hardware ABI definitions |
| `src/compiler/70.backend/backend/hardware_codegen_types.spl` | `HardwareCodegen` trait |
| `src/compiler/70.backend/vhdl_constraints.spl` | E07xx constraint checker |
| `src/lib/nogc_sync_mut/io/vhdl_ffi.spl` | SFFI bindings for GHDL/Yosys |

---

## Related Documentation

| Document | Scope |
|----------|-------|
| `doc/07_guide/ffi/sffi.md` | Software SFFI (C/C++/Rust) |
| `doc/07_guide/hardware/simple_generated_fpga_rtl.md` | FPGA bundle generation |
| `doc/07_guide/hardware/xilinx_fpga_board_bringup.md` | Board bringup workflow |
| `doc/04_architecture/vhdl_hardware_subset_contract.md` | Full hardware subset spec |
| `doc/04_architecture/riscv_architecture.md` | RISC-V system architecture |
| `doc/05_design/VHDL_BACKEND_DESIGN.md` | VHDL backend design rationale |
| `doc/05_design/rtl_riscv_mdsoc_capsules.md` | RTL capsule organization |
| `doc/07_guide/riscv_guide.md` | RISC-V comprehensive guide |
