# Target Architecture Design

**Date**: 2026-02-05
**Status**: Draft
**Related**: `src/std/common/target.spl`, `src/compiler/type_layout.spl`

---

## Overview

This document defines how Simple supports multiple CPU architectures (8/16/32/64-bit) with proper type sizing, calling conventions, and architecture-specific features.

---

## Supported Architectures

### 8-bit Architectures

| Architecture | Family | Pointer Size | Data Bus | Notes |
|-------------|--------|--------------|----------|-------|
| AVR | ATmega, ATtiny | 16-bit | 8-bit | Harvard, Arduino |
| MCS51 | 8051 | 16-bit | 8-bit | Multiple memory spaces |

### 16-bit Architectures

| Architecture | Family | Pointer Size | Data Bus | Notes |
|-------------|--------|--------------|----------|-------|
| MSP430 | TI MSP430 | 16-bit | 16-bit | Ultra low power |

### 32-bit Architectures

| Architecture | Family | Pointer Size | Data Bus | Notes |
|-------------|--------|--------------|----------|-------|
| X86 | i686 | 32-bit | 32-bit | Legacy PC |
| ARM | Cortex-M | 32-bit | 32-bit | Embedded |
| RISC-V 32 | RV32 | 32-bit | 32-bit | Open ISA |

### 64-bit Architectures

| Architecture | Family | Pointer Size | Data Bus | Notes |
|-------------|--------|--------------|----------|-------|
| X86_64 | AMD64 | 64-bit | 64-bit | Modern PC |
| AArch64 | ARM64 | 64-bit | 64-bit | Mobile/Server |
| RISC-V 64 | RV64 | 64-bit | 64-bit | Open ISA |

---

## Architecture Properties

### TargetArch Enum

```simple
enum TargetArch:
    # 8-bit
    AVR           # Atmel AVR (ATmega, ATtiny)
    MCS51         # Intel 8051 family

    # 16-bit
    MSP430        # TI MSP430

    # 32-bit
    X86           # Intel x86 (i686)
    Arm           # ARM Cortex-M (thumbv7m)
    Riscv32       # RISC-V 32-bit

    # 64-bit
    X86_64        # AMD64/Intel 64
    Aarch64       # ARM 64-bit
    Riscv64       # RISC-V 64-bit
```

### Core Properties

```simple
impl TargetArch:
    # Bit width of native word
    fn bits() -> i64:
        match self:
            case AVR | MCS51: 8
            case MSP430: 16
            case X86 | Arm | Riscv32: 32
            case X86_64 | Aarch64 | Riscv64: 64

    # Pointer size in bytes
    fn pointer_size() -> i64:
        match self:
            case AVR | MCS51 | MSP430: 2  # 16-bit pointers
            case X86 | Arm | Riscv32: 4
            case X86_64 | Aarch64 | Riscv64: 8

    # Stack alignment in bytes
    fn stack_align() -> i64:
        match self:
            case AVR | MCS51: 1
            case MSP430: 2
            case X86 | Arm | Riscv32: 4
            case X86_64 | Aarch64 | Riscv64: 16

    # Maximum atomic operation width in bits
    fn max_atomic_width() -> i64:
        match self:
            case AVR | MCS51: 8
            case MSP430: 16
            case X86: 64         # cmpxchg8b
            case X86_64: 128     # cmpxchg16b
            case Arm | Riscv32: 32
            case Aarch64 | Riscv64: 64

    # Has hardware FPU
    fn has_fpu() -> bool:
        match self:
            case AVR | MCS51 | MSP430: false
            case Arm: false      # Cortex-M0/M3 (M4F has FPU)
            case _: true

    # Byte order
    fn endianness() -> Endian:
        match self:
            case MCS51: Endian.Big
            case _: Endian.Little

    # Harvard architecture (separate code/data memory)
    fn is_harvard() -> bool:
        match self:
            case AVR | MCS51: true
            case _: false
```

---

## Pointer-Sized Types

### usize and isize

These types scale with the target architecture's pointer size:

| Architecture | usize | isize | Range |
|-------------|-------|-------|-------|
| 8-bit* | u16 | i16 | 0..65535 |
| 16-bit | u16 | i16 | 0..65535 |
| 32-bit | u32 | i32 | 0..4B |
| 64-bit | u64 | i64 | 0..18E |

*Note: 8-bit architectures use 16-bit pointers for addressing

### Implementation

```simple
# In type system
fn resolve_usize(arch: TargetArch) -> HirType:
    match arch.pointer_size():
        case 2: HirType.U16
        case 4: HirType.U32
        case 8: HirType.U64

fn resolve_isize(arch: TargetArch) -> HirType:
    match arch.pointer_size():
        case 2: HirType.I16
        case 4: HirType.I32
        case 8: HirType.I64
```

---

## Calling Conventions

### Convention Types

```simple
enum CallingConvention:
    Simple          # Default Simple ABI (may differ from C)
    C               # Platform C ABI (cdecl, System V, etc.)
    Fastcall        # Register-heavy convention
    Stdcall         # Windows stdcall (x86 only)
    Interrupt       # Interrupt service routine
    Naked           # No prologue/epilogue
```

### ABI Information

```simple
struct AbiInfo:
    arg_regs: [text]        # Registers for arguments
    ret_regs: [text]        # Registers for return value
    callee_saved: [text]    # Must preserve across calls
    stack_align: i64        # Stack alignment requirement
    red_zone: i64           # Red zone size (bytes below SP)
    struct_return: StructReturn  # How structs are returned
```

### Platform ABIs

#### x86 (32-bit) - cdecl
```simple
AbiInfo(
    arg_regs: [],                    # All on stack
    ret_regs: ["eax", "edx"],        # 64-bit in edx:eax
    callee_saved: ["ebx", "esi", "edi", "ebp"],
    stack_align: 4,
    red_zone: 0,
    struct_return: StructReturn.Hidden  # Via hidden pointer
)
```

#### x86_64 (64-bit) - System V AMD64
```simple
AbiInfo(
    arg_regs: ["rdi", "rsi", "rdx", "rcx", "r8", "r9"],
    ret_regs: ["rax", "rdx"],
    callee_saved: ["rbx", "rbp", "r12", "r13", "r14", "r15"],
    stack_align: 16,
    red_zone: 128,
    struct_return: StructReturn.InRegs  # Small structs in regs
)
```

#### AVR (8-bit)
```simple
AbiInfo(
    arg_regs: ["r24", "r22", "r20", "r18"],  # Pairs for 16-bit
    ret_regs: ["r24", "r25"],
    callee_saved: ["r2".."r17", "r28", "r29"],
    stack_align: 1,
    red_zone: 0,
    struct_return: StructReturn.Hidden
)
```

#### ARM Cortex-M
```simple
AbiInfo(
    arg_regs: ["r0", "r1", "r2", "r3"],
    ret_regs: ["r0", "r1"],
    callee_saved: ["r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11"],
    stack_align: 8,
    red_zone: 0,
    struct_return: StructReturn.InRegs  # Up to 4 words
)
```

---

## Data Type Alignment

### Type Sizes by Architecture

| Type | 8-bit | 16-bit | 32-bit | 64-bit |
|------|-------|--------|--------|--------|
| bool | 1 | 1 | 1 | 1 |
| i8/u8 | 1 | 1 | 1 | 1 |
| i16/u16 | 2 | 2 | 2 | 2 |
| i32/u32 | 4 | 4 | 4 | 4 |
| i64/u64 | 8 | 8 | 8 | 8 |
| f32 | 4 | 4 | 4 | 4 |
| f64 | 8 | 8 | 8 | 8 |
| usize | 2 | 2 | 4 | 8 |
| pointer | 2 | 2 | 4 | 8 |

### Alignment by Architecture

| Type | 8-bit | 16-bit | 32-bit | 64-bit |
|------|-------|--------|--------|--------|
| i64/u64 | 1 | 2 | 4 | 8 |
| f64 | 1 | 2 | 4 | 8 |
| pointer | 1 | 2 | 4 | 8 |

---

## Conditional Compilation

### @cfg Attribute

```simple
# Target architecture
@cfg("target_arch", "avr")
fn platform_init():
    # AVR-specific initialization

@cfg("target_arch", "x86_64")
fn platform_init():
    # x86_64-specific initialization

# Pointer width
@cfg("target_pointer_width", "16")
const MAX_ARRAY_SIZE: usize = 32768

@cfg("target_pointer_width", "64")
const MAX_ARRAY_SIZE: usize = 1 << 48

# Target OS
@cfg("target_os", "none")
fn print(msg: text):
    serial_write(msg)

@cfg("target_os", "linux")
fn print(msg: text):
    syscall_write(1, msg)

# Feature flags
@cfg("feature", "fpu")
fn sin(x: f64) -> f64:
    # Hardware FPU version

@cfg(not("feature", "fpu"))
fn sin(x: f64) -> f64:
    # Software implementation

# Combined conditions
@cfg(all("target_arch", "arm"), ("feature", "thumb"))
fn thumb_specific():
    pass

@cfg(any("target_arch", "x86"), ("target_arch", "x86_64"))
fn x86_family():
    pass
```

### Predefined cfg Values

| Key | Values | Description |
|-----|--------|-------------|
| `target_arch` | avr, mcs51, msp430, x86, arm, riscv32, x86_64, aarch64, riscv64 | CPU architecture |
| `target_os` | none, linux, windows, macos | Operating system |
| `target_pointer_width` | 8, 16, 32, 64 | Pointer size in bits |
| `target_endian` | little, big | Byte order |
| `target_has_atomic` | 8, 16, 32, 64, 128 | Atomic operation widths |
| `feature` | fpu, simd, thumb, etc. | Optional features |

---

## 8-bit Architecture Special Considerations

### AVR (Arduino)

1. **Harvard Architecture**: Separate program (flash) and data (SRAM) memory
   ```simple
   @memory("progmem")  # Store in flash
   const LOOKUP_TABLE: [u8] = [0, 1, 2, 3]

   # Read from program memory
   val x = pgm_read_byte(&LOOKUP_TABLE[i])
   ```

2. **Limited Stack**: Often 256-2048 bytes
   ```simple
   @stack_size(512)  # Warn if function uses more
   fn recursive_function():
       pass
   ```

3. **No Hardware Multiply** (some variants)
   ```simple
   @cfg("target_feature", "mul")
   fn fast_multiply(a: u8, b: u8) -> u16:
       a as u16 * b as u16

   @cfg(not("target_feature", "mul"))
   fn fast_multiply(a: u8, b: u8) -> u16:
       software_multiply(a, b)
   ```

### 8051 (MCS-51)

1. **Multiple Memory Spaces**
   ```simple
   @memory("code")   # 64KB program memory
   @memory("data")   # 128 bytes internal RAM
   @memory("idata")  # 256 bytes internal (indirect)
   @memory("xdata")  # 64KB external RAM
   @memory("pdata")  # 256 bytes paged external
   ```

2. **Bit-Addressable Region**
   ```simple
   @bit_addressable
   var FLAGS: u8 @ 0x20  # Bytes 0x20-0x2F are bit-addressable

   # Access individual bits
   FLAGS.0 = true  # Set bit 0
   if FLAGS.7:     # Check bit 7
       pass
   ```

3. **Bank Switching**
   ```simple
   @bank(0)
   fn bank0_function():
       pass

   @bank(1)
   fn bank1_function():
       pass
   ```

---

## Memory Layout Considerations

### Struct Packing

```simple
# Default: architecture-aligned
struct AlignedStruct:
    a: u8    # offset 0
    # padding for alignment
    b: u32   # offset 4 (32-bit), offset 2 (16-bit), offset 1 (8-bit)

# Packed: no padding
@packed
struct PackedStruct:
    a: u8    # offset 0
    b: u32   # offset 1 (always)
```

### Struct Size by Architecture

For `struct { a: u8, b: u32 }`:

| Repr | 8-bit | 16-bit | 32-bit | 64-bit |
|------|-------|--------|--------|--------|
| Default | 5 | 6 | 8 | 8 |
| Packed | 5 | 5 | 5 | 5 |

---

## Comparison with Other Languages

### Rust
- Uses `usize`/`isize` for pointer-sized types
- `#[cfg(target_arch = "...")]` for conditional compilation
- `#[repr(C)]` for C-compatible layout
- No native 8-bit target support (limited via AVR-rust fork)

### Zig
- `usize` resolves to `u16`/`u32`/`u64` based on target
- `@import("builtin").target` for compile-time target info
- First-class AVR support
- Comptime for conditional compilation

### C
- `size_t` defined per platform in `<stddef.h>`
- `#ifdef __AVR__` etc. for conditional compilation
- No language-level type safety for pointer sizes
- Relies on libc for platform abstraction

---

## Implementation Files

| File | Purpose |
|------|---------|
| `src/std/common/target.spl` | TargetArch enum and properties |
| `src/compiler/type_layout.spl` | Architecture-aware type sizing |
| `src/compiler/calling_convention.spl` | ABI definitions |
| `src/compiler/cfg.spl` | Conditional compilation |
| `src/compiler/codegen.spl` | Architecture-specific code generation |

---

## Future Considerations

1. **Cross-compilation toolchain**: Support building for embedded targets from desktop
2. **Emulator integration**: QEMU for x86/ARM, simavr for AVR
3. **Debug info**: DWARF generation for all architectures
4. **Inline assembly**: Architecture-specific asm syntax
5. **SIMD**: Vector extensions (SSE, NEON, etc.)
