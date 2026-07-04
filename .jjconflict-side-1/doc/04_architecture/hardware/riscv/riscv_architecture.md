# RISC-V Architecture Reference

This document provides a top-level architecture overview of Simple's RISC-V
support. For detailed usage, see `doc/07_guide/riscv_guide.md`. For
domain-specific architecture details, see the linked documents below.

---

## Table of Contents

1. [System Overview](#system-overview)
2. [Compiler Backend Pipeline](#compiler-backend-pipeline)
3. [Hardware Module Design](#hardware-module-design)
4. [VHDL Backend Integration](#vhdl-backend-integration)
5. [FPGA Toolchain Integration](#fpga-toolchain-integration)
6. [Target Contract System](#target-contract-system)
7. [Related Architecture Documents](#related-architecture-documents)

---

## System Overview

Simple's RISC-V support is organised into four architectural layers:

```
+---------------------------------------------------------------+
|                    Applications / Tests                        |
+---------------------------------------------------------------+
|  Compiler Backend          |  VHDL Backend                    |
|  (MIR -> ELF)              |  (MIR -> .vhd)                  |
|  ISel -> RegAlloc -> Encode |  Entity/Arch/Process Generation |
+---------------------------------------------------------------+
|  Baremetal Runtime (std.baremetal.riscv / riscv32 / riscv_common)
|  Startup, CSR, MMU, PLIC, CLINT, SBI, CMO, DTB               |
+---------------------------------------------------------------+
|  FPGA Toolchain (std.hardware.fpga_linux)                     |
|  Synthesis Wrapper, XDC Gen, Board Profiles                   |
+---------------------------------------------------------------+
|  Debug / Simulation Adapters                                  |
|  QEMU (GDB-MI), GHDL (GDB remote), hybrid sim                |
+---------------------------------------------------------------+
```

All modules are written in Simple (`.spl`). The architecture follows MDSOC
principles: each module has a single concern, communicates through explicit
data contracts, and avoids inheritance.

---

## Compiler Backend Pipeline

### Pipeline Stages

```
Simple Source
    |
    v
  Parse -> AST -> Lower -> MIR
    |
    v
  Instruction Selection (ISel)
    |  isel_riscv32.spl / isel_riscv64.spl
    |  Pattern-matches MirInstKind to MachInst sequences
    v
  Register Allocation
    |  Maps virtual registers to x0-x31
    |  Respects calling convention (a0-a7, s0-s11, t0-t6)
    v
  Encoding
    |  riscv_encoding.spl (shared R/I/S/B/U/J format encoders)
    |  encode_riscv32.spl / encode_riscv64.spl (target-specific)
    v
  ELF Output (ELFCLASS32 or ELFCLASS64)
```

### Instruction Selection

The ISel modules translate MIR to machine instructions:

- **Input**: `MirModule` containing `MirFunction`s with `MirBlock`s
- **Output**: `MachModule` containing `MachFunction`s with `MachBlock`s
- **Pattern matching**: Each `MirInstKind` variant (BinOp, UnaryOp, Load,
  Store, Call, Return, etc.) maps to one or more `MachInst`s
- **Operand lowering**: `MirOperand` -> `LoweredOperand` (handles Copy, Move,
  Const with instruction emission)
- **Shared context**: `ISelContext` tracks virtual register allocation, frame
  slots, string data, and extern symbols

Key modules:
- `src/compiler/70.backend/backend/native/isel_riscv32.spl`
- `src/compiler/70.backend/backend/native/isel_riscv64.spl`
- `src/compiler/70.backend/backend/common/isel_common.spl` (shared helpers)
- `src/compiler/70.backend/backend/common/isel_context.spl` (state management)

### Encoding

The encoder converts `MachInst` to raw bytes:

- **Format encoders** (`riscv_encoding.spl`): `riscv_encode_r_type()`,
  `riscv_encode_i_type()`, `riscv_encode_s_type()`, `riscv_encode_b_type()`
- **Emit helper**: `riscv_emit_u32_le()` -- emits 32-bit instruction as 4
  little-endian bytes using division/modulo (avoids negative-bit-op hazards
  in interpreter mode)
- **Jump resolution**: Two-pass with `block_offsets` and `pending_jumps`
- **Relocations**: CALL relocation for AUIPC+JALR pairs (reloc type 19)

Target-specific encoders handle ELF header differences:
- RV32: ELFCLASS32, 32-bit headers, LW/SW for pointer access
- RV64: ELFCLASS64, 64-bit headers, LD/SD for pointer access

### Inline Assembly

Two assembly backends generate RISC-V assembly from inline asm blocks:

- `riscv_asm.spl` -- RV64 (LD/SD, 64-bit addresses)
- `riscv32_asm.spl` -- RV32 (LW/SW, 32-bit addresses, `.attribute` for RV32IM)

Both provide register allocation for inline asm operands.

### RVV Extension Encoders

Eight modules cover the RVV v1.0 specification, each producing exact 4-byte
little-endian instruction words:

| Module | Coverage |
|--------|----------|
| `encode_rvv_int.spl` | Integer arithmetic: vadd, vsub, vand, vor, vxor, vsll, vsrl, vmul |
| `encode_rvv_float.spl` | Floating-point vector operations |
| `encode_rvv_fixedpt.spl` | Fixed-point (saturating, averaging) |
| `encode_rvv_mask.spl` | Mask operations |
| `encode_rvv_misc.spl` | Moves, merges, vid |
| `encode_rvv_permute.spl` | Gather, slide, compress |
| `encode_rvv_widen.spl` | Widening arithmetic |
| `encode_rvv_zvk.spl` | Zvk crypto (AES, SHA, GHASH) |

All use the OP-V major opcode (0x57). Encoding uses multiplication/division
(not bit-shifts) to avoid negative-bit-op hazards in interpreter mode.

### Intrinsic Lowering

`intrinsic_lowering_riscv.spl` maps canonical `MirInstKind.Intrinsic` name
strings to raw byte sequences, gated by `Rv64Caps`:

- **Zvk crypto**: AES rounds, SHA-256/512, GHASH/GMUL
- **Zbb/Zbkb scalar**: rotate, popcount, clz, ctz, bswap, bitreverse

---

## Hardware Module Design

### riscv_common -- Width-Agnostic Abstractions

The `riscv_common` package provides building blocks shared between RV32 and RV64.
All modules parameterize on `XlenConfig` to handle width differences:

```
src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/
    xlen.spl        -- Xlen enum (Xlen32/Xlen64) + XlenConfig struct
    registers.spl   -- RegisterFile: x0 hardwired zero, XLEN-wide values as i64
    decode.spl      -- DecodedInsn from 32-bit instruction word (all 6 formats)
    alu.spl         -- ALU evaluator (ADD..AND + RV64 W-variants)
    memory.spl      -- MemoryBus trait + FlatMemory (byte-array backed)
    csr_defs.spl    -- CSR address constants (M/S/U mode)
    platform.spl    -- RiscvPlatform contract (QEMU virt, SiFive, FPGA)
```

Design decisions:

- **XLEN abstraction**: `XlenConfig` carries `bits`, `bytes`, `sign_bit`,
  `sign_mask`, and `addr_mask`. ALU and register file truncate/sign-extend
  results via config.
- **Decoder is XLEN-agnostic**: Operates on raw 32-bit encoding. Width-dependent
  behaviour (ADDW vs ADD) handled by ALU/execution.
- **MemoryBus trait**: Abstract load/store interface. `FlatMemory` implements
  it for simulation/testing with a simple byte array.
- **No inheritance**: All composition via structs and traits.

### RV64 Runtime Modules

```
src/lib/nogc_async_mut_noalloc/baremetal/riscv/
    startup.spl    -- Multi-hart M-mode boot, per-hart stacks, trap handler
    csr.spl        -- Full CSR registry (M/S/U), typed read/write via inline asm
    mmu.spl        -- SATP encode/decode, Sv32/39/48/57, privilege levels
    plic.spl       -- PLIC: source priority, enable, threshold, claim/complete
    clint.spl      -- CLINT: MSIP, MTIMECMP, MTIME
    sbi.spl        -- SBI ecall (IPI extension, legacy fallback to CLINT MSIP)
    semihost.spl   -- Semihosting (EBREAK + magic NOP sequence)
    dtb_scan.spl   -- FDT parser (hart enumeration, ISA strings, CBOM)
    dtb_gen.spl    -- FDT blob generator (for testing)
    cmo.spl        -- Cache management (Zicbom/Zicboz/Zicbop)
```

### RV32 Runtime Modules

```
src/lib/nogc_async_mut_noalloc/baremetal/riscv32/
    startup.spl    -- RV32 M-mode boot (32-bit registers, lw/sw, bit 31 interrupt flag)
    semihost.spl   -- RV32 semihosting
```

The RV32 runtime is a narrower subset -- modules like PLIC, CLINT, and CSR
are shared from the RV64 side or from riscv_common.

---

## VHDL Backend Integration

### Architecture

The VHDL backend compiles MIR to synthesizable VHDL-2008:

```
MIR Module
    |
    v
  VhdlBackend.compile()
    |  - VhdlTypeMapper: MIR types -> VHDL types (std_logic_vector, signed, etc.)
    |  - VhdlBuilder: entity/architecture/process generation
    v
  .vhd files (entity + architecture + package)
```

Key modules:
- `vhdl_backend.spl` -- Top-level backend (MIR -> VHDL compilation)
- `vhdl_type_mapper.spl` -- Type conversion (MIR to VHDL)
- `vhdl_builder.spl` -- Code generation engine (library headers, entity
  declarations, architecture bodies, signals, processes, instances)
- `vhdl_constraints.spl` -- Two-layer constraint checker:
  - Layer 1: Numeric/width constraints (delegated to DimSolver)
  - Layer 2: Structural/graph constraints (CDC, latch, combinational loops)

### RV32I-Specific Templates

- `vhdl_rv32i_decode.spl` -- Generates synthesizable VHDL for RV32I instruction
  decoding: opcode constants, funct3/funct7 constants, field extraction signals,
  ALU control decode logic. Output is deterministic and GHDL-compatible.
- `vhdl_register_file.spl` -- Multi-port register file template with explicit
  reset, write-enable, and x0=0 hardwiring. Vendor-safe (no inferred
  read-during-write ambiguity).
- `vhdl_memory_templates.spl` -- Block RAM / ROM templates with explicit
  `VhdlReadDuringWritePolicy` (ReadFirst, WriteFirst, NoChange, Ambiguous).
- `vhdl_testbench.spl` -- Testbench renderer: DUT instantiation, clock/reset,
  stimulus phases, expect/assert checks.

---

## FPGA Toolchain Integration

### Synthesis Flow

```
Simple Source (.spl)
    |
    v
  VHDL Backend -> .vhd files
    |
    v
  XDC Generator -> .xdc constraint files
    |
    v
  Synthesis Wrapper -> Vivado TCL scripts + project structure
    |
    v
  Vivado / open-source flow -> bitstream
```

Key modules (`src/lib/hardware/fpga_linux/`):

- **`riscv_fpga_linux.spl`** -- Dual-arch orchestration layer. Manages board
  profiles, lane contracts (proof validation), RTL bundle generation, and boot
  product metadata (DTB, boot ROM). Tracks six plan items from the FPGA Linux
  agent task.

- **`synthesis_wrapper.spl`** -- Generates Vivado TCL scripts and project
  structure. Does not invoke Vivado directly -- produces consumable artifacts.
  `SynthesisProject` struct encapsulates the project configuration.

- **`xdc_gen.spl`** -- Generates Xilinx Design Constraints files. Three struct
  types: `PinAssignment`, `ClockConstraint`, `TimingConstraint`. Each serializes
  to XDC text via `.to_xdc()`.

### Board Support

Board-specific guides and validation specs are in:
- `doc/07_guide/hardware/` -- Board bringup guides
- `test/01_unit/hardware/fpga_linux/` -- Board-specific RTL validation specs

---

## Target Contract System

### Two-Level Design

1. **`TargetPreset`** (high-level): Captures arch, OS, ABI, no_std/no_gc flags,
   stack/heap sizes, pointer width, float support. Used for preset lookup
   (`preset_by_name("riscv32-baremetal")`).

2. **`RiscvTargetContract`** (low-level): Full codegen configuration derived
   from presets + capability registry. Carries triple, march, ABI, CPU,
   features, linker, sysroot, pointer bits, stack alignment, arg register
   count, and PLT relocation type.

### Contract Derivation

```
preset_riscv32_baremetal()
    |
    v
portable_numeric_capabilities_for_preset(preset)
    |  Probes: has_riscv_f, has_riscv_d
    v
riscv_baremetal_target_contract(CodegenTarget.Riscv32)
    |  Selects: ILP32 / ILP32D, rv32imac / rv32gc, features
    v
RiscvTargetContract { arch, march, abi, features, ... }
```

### Available Contracts

| Factory Function | Environment | Default Profile |
|-----------------|-------------|-----------------|
| `riscv_linux_target_contract(Riscv32)` | Linux | RV32GC, ILP32D |
| `riscv_linux_target_contract(Riscv64)` | Linux | RV64GC, LP64D |
| `riscv_baremetal_target_contract(Riscv32)` | Baremetal | RV32IMAC, ILP32 |
| `riscv_baremetal_target_contract(Riscv64)` | Baremetal | RV64GC, LP64D |

The `_portable_numeric` variants are thin delegates to the above -- the
capability registry logic is now inlined in the main contract functions.

### RV32 Target Configuration

`src/compiler/70.backend/target/riscv32.spl` defines:

- Target triples (baremetal and Linux)
- CPU and feature defaults
- LLVM data layout string (`e-m:e-p:32:32-i64:64-n32-S128`)
- Register info (x0-x31 integer, f0-f31 optional float)
- ILP32 calling convention (a0-a7 args, s0-s11 saved, t0-t6 temporaries)
- Type sizes (bool=1, i32=4, i64=8, pointer=4, long=4)

---

## Related Architecture Documents

| Document | Scope |
|----------|-------|
| `doc/04_architecture/hardware/riscv/riscv_fpga_linux.md` | FPGA Linux dual-arch architecture |
| `doc/04_architecture/hardware/riscv/riscv_generated_core_migration.md` | Generated core migration path |
| `doc/04_architecture/hardware/riscv/riscv_linux_rtl_dual_arch_completion.md` | RTL dual-arch completion plan |
| `doc/05_design/riscv_smp_cache_hal.md` | SMP + cache HAL design |
| `doc/05_design/rtl_riscv_mdsoc_capsules.md` | RTL MDSOC capsule design |
| `doc/07_guide/riscv_guide.md` | Comprehensive usage guide |
| `doc/07_guide/hardware/` | FPGA board-specific guides |
