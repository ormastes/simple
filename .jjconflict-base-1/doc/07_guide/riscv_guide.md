# RISC-V Guide for Simple

This guide covers everything needed to work with RISC-V targets in the Simple
language: compiling for RV32/RV64, baremetal programming, FPGA synthesis,
hardware simulation, and testing.

---

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [Target Presets and Contracts](#target-presets-and-contracts)
3. [Compiling for RISC-V](#compiling-for-risc-v)
4. [Baremetal Programming](#baremetal-programming)
5. [FPGA Synthesis](#fpga-synthesis)
6. [Hardware Simulation](#hardware-simulation)
7. [RVV (Vector Extension)](#rvv-vector-extension)
8. [Intrinsic Lowering](#intrinsic-lowering)
9. [Debug Adapters](#debug-adapters)
10. [Testing](#testing)
11. [File Map](#file-map)

---

## Architecture Overview

Simple provides full-stack RISC-V support spanning four layers:

| Layer | What it does | Key modules |
|-------|-------------|-------------|
| **Compiler backend** | MIR to native RV32/RV64 code | ISel, encoder, assembler |
| **Baremetal runtime** | Machine-mode startup, CSR, MMU, PLIC, CLINT | `std.baremetal.riscv` / `riscv32` |
| **VHDL backend** | Synthesizable hardware from MIR | VHDL builder, RV32I decode, register file |
| **FPGA toolchain** | Vivado project generation, XDC constraints | `std.hardware.fpga_linux` |

Supported ISA profiles:

- **RV32IMAC** -- 32-bit base integer + multiply + atomics + compressed
- **RV32GC** (RV32IMAFDC) -- adds single/double float
- **RV64GC** (RV64IMAFDC) -- 64-bit general-purpose
- **RVV v1.0** -- vector extension (integer, float, fixed-point, mask, permute, crypto)

---

## Target Presets and Contracts

### Presets

Two RISC-V presets are available via `preset_by_name()`:

```spl
use compiler.backend.target_presets.{preset_by_name, preset_riscv32_baremetal, preset_riscv64_linux}

# Direct factory functions
val rv32 = preset_riscv32_baremetal()
val rv64 = preset_riscv64_linux()

# Or by name
val rv32_alt = preset_by_name("riscv32-baremetal")
val rv64_alt = preset_by_name("riscv64-linux")
```

Each `TargetPreset` carries:

| Field | RV32 baremetal | RV64 Linux |
|-------|---------------|------------|
| `arch` | `"riscv32"` | `"riscv64"` |
| `os` | `"none"` | `"linux"` |
| `no_std` | `true` | `false` |
| `no_gc` | `true` | `false` |
| `pointer_width` | 32 | 64 |
| `float_support` | `false` | `true` |

### Target Contracts

Target contracts provide the full codegen configuration. They are derived from
presets and the portable numeric capability registry:

```spl
use compiler.backend.backend.riscv_target.{
    RiscvTargetContract,
    riscv_linux_target_contract,
    riscv_baremetal_target_contract
}
use compiler.backend.backend.backend_types.{CodegenTarget}

# Linux target (RV32 or RV64)
val linux_rv64 = riscv_linux_target_contract(CodegenTarget.Riscv64)
# -> triple: riscv64-unknown-linux-gnu, march: rv64gc, abi: lp64d

val linux_rv32 = riscv_linux_target_contract(CodegenTarget.Riscv32)
# -> triple: riscv32-unknown-linux-gnu, march: rv32gc, abi: ilp32d

# Baremetal target
val bare_rv32 = riscv_baremetal_target_contract(CodegenTarget.Riscv32)
# -> triple: riscv32-unknown-none-elf, march: rv32imac, abi: ilp32

val bare_rv64 = riscv_baremetal_target_contract(CodegenTarget.Riscv64)
# -> triple: riscv64-unknown-none-elf, march: rv64gc, abi: lp64d
```

Key `RiscvTargetContract` fields:

| Field | Description |
|-------|-------------|
| `arch` | Architecture string (`"riscv32"` or `"riscv64"`) |
| `march` | ISA string for linker/assembler (`"rv32gc"`, `"rv64gc"`, etc.) |
| `abi` | ABI enum (`ILP32`, `ILP32D`, `LP64`, `LP64D`) |
| `features` | ISA extension flags (`["+m", "+a", "+f", "+d", "+c"]`) |
| `pointer_bits` | 32 or 64 |
| `linker` | Default linker binary name |
| `triple()` | Returns the full target triple string |
| `march_flag()` | Returns `"-march=rv64gc"` etc. |
| `abi_flag()` | Returns `"-mabi=lp64d"` etc. |

The capability registry (`portable_numeric_capabilities_for_preset`) auto-detects
which ISA extensions are available and adjusts the contract accordingly:

- If `has_riscv_d`: full GC profile (F+D extensions)
- If `has_riscv_f` only: F extension, no double-precision
- Otherwise: integer-only (IMAC)

---

## Compiling for RISC-V

### Compiler Pipeline

The compiler backend follows this pipeline for RISC-V targets:

```
Simple source -> Parse -> MIR -> ISel -> RegAlloc -> Encode -> ELF
```

1. **Instruction Selection (ISel)**: Pattern-matches `MirInstKind` nodes to
   produce `MachInst` sequences using RISC-V opcodes.
   - `isel_riscv32.spl` -- RV32 ISel (ILP32 calling convention)
   - `isel_riscv64.spl` -- RV64 ISel (LP64D calling convention)

2. **Register Allocation**: Maps virtual registers to physical RV registers
   (x0-x31). Calling convention: a0-a7 for arguments, s0-s11 callee-saved,
   t0-t6 temporaries.

3. **Encoding**: Emits exact 4-byte little-endian instruction words.
   - `riscv_encoding.spl` -- shared format encoders (R/I/S/B/U/J types)
   - `encode_riscv32.spl` -- RV32-specific encoding + ELF32 output
   - `encode_riscv64.spl` -- RV64-specific encoding + ELF64 output

4. **Assembly**: For inline assembly support.
   - `riscv_asm.spl` -- RV64 inline assembly backend
   - `riscv32_asm.spl` -- RV32 inline assembly backend

### Instruction Encoding Formats

All RISC-V instructions are 32-bit fixed-width, little-endian:

| Format | Layout |
|--------|--------|
| R-type | `funct7[31:25] \| rs2[24:20] \| rs1[19:15] \| funct3[14:12] \| rd[11:7] \| opcode[6:0]` |
| I-type | `imm[31:20] \| rs1[19:15] \| funct3[14:12] \| rd[11:7] \| opcode[6:0]` |
| S-type | `imm[31:25] \| rs2[24:20] \| rs1[19:15] \| funct3[14:12] \| imm[11:7] \| opcode[6:0]` |
| B-type | `imm[12\|10:5] \| rs2[24:20] \| rs1[19:15] \| funct3[14:12] \| imm[4:1\|11] \| opcode[6:0]` |
| U-type | `imm[31:12] \| rd[11:7] \| opcode[6:0]` |
| J-type | `imm[20\|10:1\|11\|19:12] \| rd[11:7] \| opcode[6:0]` |

The shared encoder functions in `riscv_encoding.spl` handle these formats:

```spl
use compiler.backend.native.riscv_encoding.{
    riscv_encode_r_type,
    riscv_encode_i_type,
    riscv_encode_s_type,
    riscv_encode_b_type,
    riscv_emit_u32_le
}
```

### RV32 vs RV64 Differences

| Aspect | RV32 | RV64 |
|--------|------|------|
| Pointer load/store | `LW`/`SW` | `LD`/`SD` |
| ALU opcode | `0x33` (no W-suffix) | `0x33` + `0x3B` (W-suffix variants) |
| ELF class | `ELFCLASS32` | `ELFCLASS64` |
| LI expansion | `LUI + ADDI` (32-bit) | `LUI + ADDI + SLLI + ADDI` (64-bit) |
| Pointer width | 4 bytes | 8 bytes |

---

## Baremetal Programming

### XLEN Configuration

The `riscv_common` module provides width-agnostic abstractions:

```spl
use std.baremetal.riscv_common.xlen.{Xlen, XlenConfig, xlen_config}

# Get config for RV32
val cfg32 = xlen_config(Xlen.Xlen32)
# cfg32.bits == 32, cfg32.bytes == 4, cfg32.sign_bit == 0x80000000

# Get config for RV64
val cfg64 = xlen_config(Xlen.Xlen64)
# cfg64.bits == 64, cfg64.bytes == 8, cfg64.sign_bit == 0x8000000000000000
```

### Platform Contracts

Define hardware platform parameters (memory map, UART address, etc.):

```spl
use std.baremetal.riscv_common.platform.{
    RiscvPlatform,
    PLATFORM_QEMU_VIRT,
    PLATFORM_SIFIVE_U
}

# QEMU virt machine provides:
# 0x80000000 - RAM base (128MB default)
# 0x0C000000 - PLIC
# 0x10000000 - UART0
# 0x02000000 - CLINT
```

### Startup and Trap Handling

The startup module provides the machine-mode entry point:

**RV64 startup** (`src/lib/nogc_async_mut_noalloc/baremetal/riscv/startup.spl`):
- Sets up per-hart stacks (configurable stack size)
- Initializes CSRs (mstatus, mtvec, mie)
- Configures PLIC for external interrupts
- Provides trap handler with full register save/restore
- Multi-hart support (hart 0 boots, others wait)

**RV32 startup** (`src/lib/nogc_async_mut_noalloc/baremetal/riscv32/startup.spl`):
- Same architecture as RV64 but with 32-bit registers
- Uses `lw`/`sw` instead of `ld`/`sd`
- Trap frame offsets are 4 bytes apart (not 8)
- `CAUSE_INTERRUPT_BIT` is bit 31 (not bit 63)

### CSR Access

The CSR module provides typed addresses and read/write wrappers:

```spl
use std.baremetal.riscv.csr (
    CSR_MSTATUS, CSR_MIE, CSR_MTVEC, CSR_MSCRATCH,
    CSR_MEPC, CSR_MCAUSE, CSR_MTVAL, CSR_MIP, CSR_MHARTID,
    MSTATUS_MIE, MSTATUS_MPIE,
    MIE_MSIE, MIE_MTIE, MIE_MEIE,
    CAUSE_INTERRUPT_BIT
)
```

CSR categories covered:

| Category | CSRs | Description |
|----------|------|-------------|
| Machine Info | `mvendorid`, `marchid`, `mimpid`, `mhartid` | Read-only identification |
| Trap Setup | `mstatus`, `misa`, `mie`, `mtvec` | Interrupt/exception config |
| Trap Handling | `mscratch`, `mepc`, `mcause`, `mtval`, `mip` | Trap state |
| Memory Protection | `pmpcfg0-3`, `pmpaddr0-15` | PMP configuration |
| Counters | `mcycle`, `minstret`, `mhpmcounter3-31` | Performance counters |
| Supervisor | `sstatus`, `sie`, `stvec`, `sscratch`, `sepc`, `scause`, `stval`, `sip`, `satp` | S-mode CSRs |

### MMU and Virtual Memory

The MMU module supports Sv32, Sv39, Sv48, and Sv57 virtual memory modes:

```spl
use std.baremetal.riscv.mmu (
    PRIV_USER, PRIV_SUPERVISOR, PRIV_MACHINE,
    SATP_MODE_BARE, SATP_MODE_SV39, SATP_MODE_SV48, SATP_MODE_SV57,
    SATP32_MODE_BARE, SATP32_MODE_SV32
)
```

SATP register layouts:

- **RV64**: MODE[63:60] | ASID[59:44] | PPN[43:0]
- **RV32**: MODE[31] | ASID[30:22] | PPN[21:0]

### PLIC (External Interrupts)

The Platform-Level Interrupt Controller handles external device interrupts:

```spl
use std.baremetal.riscv.plic (
    PlicContext, plic_init, plic_claim, plic_complete, handle_interrupt
)
```

PLIC features:
- Up to 1023 interrupt sources
- Configurable priority levels (1-7, 0 = disabled)
- Context-based interrupt routing (hart + privilege level)
- Claim/complete mechanism

Memory-mapped registers (base `0x0C000000`):

| Register | Offset | Description |
|----------|--------|-------------|
| Source Priority | `base + (source * 4)` | Priority per source |
| Pending Bits | `base + 0x1000` | Which interrupts are pending |
| Enable Bits | `base + 0x2000 + (ctx * 0x80)` | Per-context enable mask |
| Threshold | `base + 0x200000 + (ctx * 0x1000)` | Priority threshold |
| Claim/Complete | `base + 0x200004 + (ctx * 0x1000)` | Claim or complete |

### CLINT (Timer and Software Interrupts)

The Core Local Interruptor provides per-hart timers:

```spl
use std.baremetal.riscv.clint (...)
```

Registers (base `0x02000000` on QEMU virt):

| Register | Offset | Description |
|----------|--------|-------------|
| MSIP[hartid] | `0x0000 + (hartid * 4)` | Software interrupt pending |
| MTIMECMP[hartid] | `0x4000 + (hartid * 8)` | Timer compare value |
| MTIME | `0xBFF8` | Global timer counter |

### SBI (Supervisor Binary Interface)

The SBI module provides ecall-based services:

```spl
use std.baremetal.riscv.sbi (...)

# SBI ecall convention:
# a7 = extension ID (EID)
# a6 = function ID (FID)
# a0-a5 = arguments
# Return: a0 = error code, a1 = value
```

Supported extensions: IPI (inter-processor interrupt), Console I/O.

### Semihosting

Both RV32 and RV64 support semihosting for debugger-mediated I/O:

```spl
use std.baremetal.riscv.semihost (...)    # RV64
use std.baremetal.riscv32.semihost (...)  # RV32
```

The semihosting mechanism uses a magic instruction sequence:
```
slli zero, zero, 0x1f   # Entry NOP (magic marker)
ebreak                   # Breakpoint triggers debugger
srai zero, zero, 0x7    # Exit NOP (magic marker)
```

Supported debuggers: OpenOCD, SEGGER Ozone, Trace32.

### Cache Management (Zicbom/Zicboz/Zicbop)

```spl
use std.baremetal.riscv.cmo (
    fence_i, cbo_clean, cbo_inval, cbo_flush, cbo_zero,
    prefetch_r, prefetch_w, prefetch_i,
    CmoCapSnapshot
)
```

### Device Tree Scanning

Parse FDT blobs to enumerate harts and capabilities:

```spl
use std.baremetal.riscv.dtb_scan (
    dtb_scan_init_from_bytes,
    cached_cpu_count,
    cached_cbom_block_size,
    cached_isa_string
)
```

### Shared Hardware Abstractions (riscv_common)

The `riscv_common` module provides width-agnostic building blocks:

| Module | Description |
|--------|-------------|
| `xlen.spl` | XLEN descriptor (RV32 vs RV64 constants) |
| `registers.spl` | Unified register file abstraction (x0 hardwired to zero) |
| `decode.spl` | Instruction decoder (all R/I/S/B/U/J formats) |
| `alu.spl` | ALU operations (ADD, SUB, SLL, SLT, XOR, SRL, SRA, OR, AND + RV64 W-ops) |
| `memory.spl` | Memory bus trait + FlatMemory for simulation |
| `csr_defs.spl` | Shared CSR address constants |
| `platform.spl` | Platform contract (QEMU virt, SiFive, FPGA boards) |

---

## FPGA Synthesis

### Overview

The FPGA integration layer generates synthesis-ready artifacts for Xilinx boards:

```spl
use std.hardware.fpga_linux.riscv_fpga_linux (...)
use std.hardware.fpga_linux.synthesis_wrapper (...)
use std.hardware.fpga_linux.xdc_gen (...)
```

### Synthesis Wrapper

Generates Vivado TCL scripts and project structure. This module does not call
Vivado directly -- it produces the scripts that Vivado will consume:

```spl
use std.hardware.fpga_linux.synthesis_wrapper.{SynthesisProject}
```

### XDC Constraint Generation

Pin assignments, clock definitions, I/O standards, and timing constraints:

```spl
use std.hardware.fpga_linux.xdc_gen.{PinAssignment, ClockConstraint, TimingConstraint}

# Pin assignment
val uart_tx = PinAssignment.create("uart_tx", "D10", "LVCMOS33")
val uart_rx = PinAssignment.with_comment("uart_rx", "A9", "LVCMOS33", "UART receive")

# Clock constraint from frequency
val clk = ClockConstraint.from_hz("sys_clk", 100000000, "E3")
# Produces: create_clock -period 10.000 -name sys_clk -waveform {0.000 5.000} [get_ports E3]

# Serialize to XDC
val xdc_text = uart_tx.to_xdc()
# Produces:
# set_property PACKAGE_PIN D10 [get_ports uart_tx]
# set_property IOSTANDARD LVCMOS33 [get_ports uart_tx]
```

### RISC-V FPGA Linux Integration

The `riscv_fpga_linux` module orchestrates dual-arch (RV32 + RV64) FPGA builds:

- Board profile management (Xilinx boards)
- Lane contracts for proof validation
- RTL bundle generation
- Boot product metadata (DTB, boot ROM)
- Vivado materialization for Xilinx targets

---

## Hardware Simulation

### QEMU

The QEMU adapter launches `qemu-system-riscv32` or `qemu-system-riscv64` and
connects via GDB-MI for execution control:

```spl
use std.nogc_sync_mut.debug.remote.exec.adapter_qemu_rv32.{QemuRv32Adapter}
use std.nogc_sync_mut.debug.remote.exec.adapter_qemu_rv64.{QemuRv64Adapter}

# Check availability
val adapter = QemuRv32Adapter.new()
if adapter.is_available():
    # Launches QEMU halted (-S flag), waits for GDB connection
    val result = adapter.connect()
```

Prerequisites:
- `qemu-system-riscv32` / `qemu-system-riscv64` in PATH
- GDB with RISC-V support (`gdb-multiarch`, `riscv32-unknown-elf-gdb`, or
  `riscv64-unknown-elf-gdb`)

### GHDL (VHDL Simulation)

The GHDL adapter connects to a running GHDL simulation with a GDB remote stub:

```spl
use std.nogc_sync_mut.debug.remote.exec.adapter_ghdl_rv32.{GhdlRv32Adapter}

# Connects to GHDL simulation via GDB remote protocol
```

### Hybrid Simulation (mllvm_qemu_rtl)

The `examples/mllvm_qemu_rtl/` project provides a hybrid RTL simulation with
RISC-V guest CPU models:

- `src/guest/riscv/cpu32.spl` -- RV32I CPU definition (32 x 32-bit registers)
- `src/guest/riscv/cpu64.spl` -- RV64 CPU definition
- `src/guest/riscv/decoder32.spl` / `decoder64.spl` -- instruction decoders
- `src/guest/riscv/decoder_common.spl` -- shared decoder logic

---

## RVV (Vector Extension)

Eight dedicated encoders cover the RVV v1.0 specification:

| Encoder | RVV Sections | Operations |
|---------|-------------|------------|
| `encode_rvv_int.spl` | 11.1, 11.4, 11.6, 11.10 | vadd, vsub, vand, vor, vxor, vsll, vsrl, vmul |
| `encode_rvv_float.spl` | Float arithmetic | Vector FP operations |
| `encode_rvv_fixedpt.spl` | Fixed-point | Saturating add/sub, averaging |
| `encode_rvv_mask.spl` | Mask operations | vmand, vmor, vmxor, etc. |
| `encode_rvv_misc.spl` | Miscellaneous | vmv, vmerge, vid, etc. |
| `encode_rvv_permute.spl` | Permutation | vrgather, vslide, vcompress |
| `encode_rvv_widen.spl` | Widening | vwadd, vwmul, etc. |
| `encode_rvv_zvk.spl` | Zvk crypto | AES, SHA-256, SHA-512, GHASH |

All RVV instructions use the OP-V major opcode (`0x57`) with 32-bit fixed-width
encoding:

```
bits[31:26] = funct6
bit[25]     = vm   (1=unmasked, 0=masked)
bits[24:20] = vs2
bits[19:15] = vs1
bits[14:12] = funct3 (OPIVV=0, OPMVV=2, OPFVV=1, etc.)
bits[11:7]  = vd
bits[6:0]   = opcode 0x57
```

Example (integer vector add):

```spl
use compiler.backend.native.encode_rvv_int.{emit_vadd_vv, emit_vsub_vv, emit_vmul_vv}

# Emit vadd.vv v1, v2, v3
val bytes = emit_vadd_vv(1, 2, 3)
# Returns [0xD7, 0x80, 0x21, 0x02] (4 bytes, little-endian)
```

---

## Intrinsic Lowering

The intrinsic lowering module maps high-level intrinsic names to native RISC-V
instruction sequences:

```spl
use compiler.backend.lowering.intrinsic_lowering_riscv (...)
```

### Supported Intrinsics

**Zvk Crypto (vector)**:

| Intrinsic | RISC-V Instruction | Args |
|-----------|-------------------|------|
| `crypto_aes_round` | `vaesem.vv` | vd, vs2 |
| `crypto_aes_round_last` | `vaesef.vv` | vd, vs2 |
| `crypto_aes_inv_round` | `vaesdm.vv` | vd, vs2 |
| `crypto_aes_inv_round_last` | `vaesdf.vv` | vd, vs2 |
| `crypto_sha256_rnds2` | `vsha2cl.vv + vsha2ch.vv` | vd, vs2, vs1 |
| `crypto_sha512_rnds2` | `vsha2cl.vv + vsha2ch.vv` (SEW=64) | vd, vs2, vs1 |
| `clmul_lo` | `vghsh.vv` | vd, vs2, vs1 |
| `clmul_hi` | `vgmul.vv` | vd, vs2 |

**Zbb/Zbkb Scalar Bit-Manipulation**:

| Intrinsic | RISC-V Instruction | Args |
|-----------|-------------------|------|
| `bit_rotate_left` | `rol` | rd, rs1, rs2 |
| `bit_rotate_right` | `ror` | rd, rs1, rs2 |
| `bit_popcount` | `cpop` | rd, rs |
| `bit_parity` | `cpop + andi 1` | rd, rs |
| `bit_clz` | `clz` | rd, rs |
| `bit_ctz` | `ctz` | rd, rs |
| `bit_bswap` | `rev8` | rd, rs |
| `bit_bitreverse` | `brev8 + rev8` | rd, rs |

Lowering results indicate success or failure:
- `""` -- success, bytes is non-empty
- `"unknown"` -- unrecognised intrinsic name
- `"no-cap"` -- capability not present in `Rv64Caps`
- `"bad-arity"` -- argument count mismatch

---

## Debug Adapters

Debug target definitions provide register layouts and calling convention info:

```spl
use std.nogc_sync_mut.debug.remote.target.riscv32.{RiscV32Target}
use std.nogc_sync_mut.debug.remote.target.riscv64.{RiscV64Target}

val target = RiscV32Target.create()
# target.name() -> "RISC-V32 (RV32IMAC)"
# target.register_count() -> 33 (x0-x31 + pc)
# target.register_name(0) -> "zero"
# target.register_name(1) -> "ra"
# target.endianness() -> Endianness.Little
```

---

## Testing

### Unit Tests

Located in `test/unit/hardware/`:

**RV32IMAC** (`test/unit/hardware/rv32imac/`):
- `rv32_decode_spec.spl` -- instruction decoding
- `rv32_alu_spec.spl` -- ALU operations
- `rv32_csr_spec.spl` -- CSR read/write
- `rv32_pipeline_spec.spl` -- pipeline stages
- `rv32_muldiv_spec.spl` -- multiply/divide
- `rv32_compressed_spec.spl` -- C extension
- `rv32_regfile_spec.spl` -- register file

**RV64GC** (`test/unit/hardware/rv64gc/`):
- `rv64_decode_spec.spl`, `rv64_alu_spec.spl`, `rv64_alu_imm_spec.spl`,
  `rv64_alu_word_spec.spl` -- base integer
- `rv64_csr_spec.spl`, `rv64_clint_spec.spl` -- system
- `rv64_compressed_spec.spl` -- C extension
- `rv64_atomics_spec.spl`, `rv64_atomics_ordering_spec.spl` -- A extension
- `rv64_fp_arith_s_spec.spl`, `rv64_fp_arith_d_spec.spl` -- F/D floating point
- `rv64_fp_compare_s_spec.spl`, `rv64_fp_compare_d_spec.spl` -- FP compare
- `rv64_fp_convert_s_spec.spl`, `rv64_fp_convert_d_spec.spl` -- FP convert
- `rv64_fp_fused_s_spec.spl`, `rv64_fp_fused_d_spec.spl` -- Fused multiply-add
- `rv64_fp_csr_spec.spl` -- FP CSR (fflags, frm, fcsr)

**riscv_common** (`test/unit/hardware/riscv_common/`):
- `riscv_formal_contract_spec.spl`
- `riscv_generated_core_spec.spl`
- `riscv_linux_profile_spec.spl`

**FPGA Linux** (`test/unit/hardware/fpga_linux/`):
- `riscv_fpga_linux_spec.spl`
- Board-specific specs for RTL/synthesis validation

**Shared library tests** (`src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/test/`):
- `riscv_common_decode_spec.spl`, `riscv_common_alu_spec.spl`,
  `riscv_common_csr_defs_spec.spl`, `riscv_common_memory_spec.spl`,
  `riscv_common_platform_spec.spl`, `riscv_common_registers_spec.spl`,
  `riscv_common_xlen_spec.spl`

### Integration Tests

Located in `test/integration/hardware/`:

- `rv32imac/` -- RV32 compliance, core smoke, hello world
- `rv32gc/` -- RV32 Linux platform contract
- `rv64gc/` -- RV64 compliance, core smoke, hello world, FP compliance,
  Linux platform contract, multicore

### System Tests

- `test/system/hardware/rv32_external_formal_harness_spec.spl`

### Running Tests

```bash
# Run all tests
bin/simple test

# Run a specific RISC-V test
bin/simple test test/unit/hardware/rv32imac/rv32_decode_spec.spl

# Run riscv_common library tests
bin/simple test src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/test/riscv_common_decode_spec.spl
```

Note: Hardware integration tests are tagged `only-compiled` and `slow` -- they
require compilation mode (not interpreter) and may take longer to execute.

---

## File Map

### Compiler Backend (`src/compiler/70.backend/`)

```
backend/native/
    encode_riscv32.spl          # RV32 instruction encoder + ELF32 output
    encode_riscv64.spl          # RV64 instruction encoder + ELF64 output
    riscv_encoding.spl          # Shared R/I/S/B/U/J format encoders
    isel_riscv32.spl            # RV32 instruction selection (MIR -> MachInst)
    isel_riscv64.spl            # RV64 instruction selection
    encode_rvv_int.spl          # RVV integer (vadd, vsub, vmul, etc.)
    encode_rvv_float.spl        # RVV floating-point
    encode_rvv_fixedpt.spl      # RVV fixed-point
    encode_rvv_mask.spl         # RVV mask operations
    encode_rvv_misc.spl         # RVV miscellaneous
    encode_rvv_permute.spl      # RVV permutation
    encode_rvv_widen.spl        # RVV widening
    encode_rvv_zvk.spl          # RVV Zvk crypto
backend/
    riscv_asm.spl               # RV64 inline assembly backend
    riscv32_asm.spl             # RV32 inline assembly backend
    riscv_target.spl            # Target contracts (RiscvTargetContract)
    vhdl_backend.spl            # VHDL-2008 code generation backend
    vhdl_type_mapper.spl        # MIR type to VHDL type mapping
    vhdl/
        vhdl_builder.spl        # VHDL code generation engine
        vhdl_helpers.spl        # VHDL generation helpers
        vhdl_rv32i_decode.spl   # RV32I instruction decode VHDL template
        vhdl_register_file.spl  # Multi-port register file VHDL template
        vhdl_memory_templates.spl  # Block RAM / ROM VHDL templates
        vhdl_testbench.spl      # VHDL testbench renderer
        vhdl_testbench_converter.spl  # Test conversion to VHDL stimuli
        vhdl_abi.spl            # VHDL ABI helpers
lowering/
    intrinsic_lowering_riscv.spl  # Zvk + Zbb/Zbkb intrinsic lowering
target/
    riscv32.spl                 # RV32 target configuration (register info, ABI, data layout)
target_presets.spl              # Cross-compilation presets (riscv32-baremetal, riscv64-linux)
vhdl_constraints.spl            # VHDL constraint checker (width, CDC, latch)
```

### Baremetal Runtime (`src/lib/nogc_async_mut_noalloc/baremetal/`)

```
riscv_common/                   # Width-agnostic (RV32/RV64) abstractions
    xlen.spl                    # XLEN descriptor
    registers.spl               # Register file interface
    decode.spl                  # Instruction decoder
    alu.spl                     # ALU operations
    memory.spl                  # Memory bus trait + FlatMemory
    csr_defs.spl                # Shared CSR constants
    platform.spl                # Platform contract
    test/                       # Unit specs for each module

riscv/                          # RV64 machine-mode runtime
    startup.spl                 # Boot entry + trap handling
    csr.spl                     # CSR registry + read/write wrappers
    mmu.spl                     # MMU + page table (Sv39/Sv48/Sv57)
    plic.spl                    # Platform-Level Interrupt Controller
    clint.spl                   # Core Local Interruptor (timer)
    sbi.spl                     # SBI ecall interface
    semihost.spl                # Semihosting support
    dtb_scan.spl                # Device tree blob parser
    dtb_gen.spl                 # Device tree generator
    cmo.spl                     # Cache management (Zicbom/Zicboz/Zicbop)
    linker.ld                   # RV64 linker script

riscv32/                        # RV32 machine-mode runtime
    startup.spl                 # RV32 boot entry + trap handling
    semihost.spl                # RV32 semihosting
    linker.ld                   # RV32 linker script
```

### Hardware Library (`src/lib/hardware/fpga_linux/`)

```
riscv_fpga_linux.spl            # Dual-arch FPGA orchestration
synthesis_wrapper.spl           # Vivado TCL script generation
xdc_gen.spl                     # XDC constraint file generation
```

### Debug Adapters (`src/lib/nogc_sync_mut/debug/`)

```
remote/exec/
    adapter_qemu_rv32.spl       # QEMU RV32 GDB-MI adapter
    adapter_qemu_rv64.spl       # QEMU RV64 GDB-MI adapter
    adapter_ghdl_rv32.spl       # GHDL VHDL simulation adapter
remote/target/
    riscv32.spl                 # RV32 register layout + debug info
    riscv64.spl                 # RV64 register layout + debug info
formats/test/
    target_riscv64_spec.spl     # Debug format test
```

### Examples (`examples/mllvm_qemu_rtl/`)

```
src/guest/riscv/
    cpu32.spl                   # RV32I guest CPU definition
    cpu64.spl                   # RV64 guest CPU definition
    decoder32.spl               # RV32 instruction decoder
    decoder64.spl               # RV64 instruction decoder
    decoder_common.spl          # Shared decoder logic
    common.spl                  # Shared RV types
```

### Related Documentation

- `doc/04_architecture/riscv_fpga_linux.md` -- FPGA Linux architecture
- `doc/04_architecture/riscv_generated_core_migration.md` -- Generated core migration
- `doc/04_architecture/riscv_linux_rtl_dual_arch_completion.md` -- Dual-arch completion
- `doc/05_design/riscv_smp_cache_hal.md` -- SMP + cache HAL design
- `doc/05_design/rtl_riscv_mdsoc_capsules.md` -- RTL MDSOC capsule design
- `doc/07_guide/hardware/` -- FPGA board-specific guides
