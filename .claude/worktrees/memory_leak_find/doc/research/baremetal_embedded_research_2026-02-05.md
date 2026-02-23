# Bare-Metal Embedded Support Research for Simple Language

**Date**: 2026-02-05
**Status**: Research Complete
**Author**: Claude (AI Research Assistant)

---

## Executive Summary

This document analyzes the Simple language's readiness for bare-metal embedded programming and recommends improvements based on features from C, Rust, Zig, and Ada/SPARK. Simple has strong foundations (type system, SFFI, atomic operations, configurable targets) but lacks critical low-level features (bitfields, volatile, raw pointers, interrupts).

**Key Findings:**
- **Bitfields**: Designed in grammar, **not implemented** in compiler
- **Volatile**: **Not supported** - can simulate with atomics
- **Raw pointers**: **Not supported** - must use SFFI
- **Interrupts**: **Not supported** - must use SFFI
- **Linker scripts**: Layout SDN exists, **LD generation planned**
- **Minimal runtime**: Bootstrap profile achieves 9.3 MB, can reach ~2.5 MB

---

## Table of Contents

1. [Current Capabilities](#1-current-capabilities)
2. [Gap Analysis vs Research Paper](#2-gap-analysis-vs-research-paper)
3. [Bitfields and Custom Types](#3-bitfields-and-custom-types)
4. [Volatile and Memory Access](#4-volatile-and-memory-access)
5. [Interrupt Handling](#5-interrupt-handling)
6. [Compile-Time Features](#6-compile-time-features)
7. [Minimal Runtime](#7-minimal-runtime)
8. [Linker Script Generation](#8-linker-script-generation)
9. [Implementation Recommendations](#9-implementation-recommendations)
10. [Short Grammar for Embedded](#10-short-grammar-for-embedded)

---

## 1. Current Capabilities

### 1.1 What Simple Has

| Feature | Status | Notes |
|---------|--------|-------|
| **Type Aliases** | ✅ Complete | `type UserId = i64` |
| **Structs** | ✅ Complete | Value types with named fields |
| **Classes** | ✅ Complete | Reference types with methods |
| **Enums** | ✅ Complete | Sum types with pattern matching |
| **Generics** | ✅ Complete | `Container<T>`, monomorphization |
| **SFFI (FFI)** | ✅ Complete | Two-tier pattern for Rust interop |
| **Atomic Operations** | ✅ Complete | Full memory ordering semantics |
| **Embedded Target** | ✅ Complete | `--target=embedded` for immutable defaults |
| **Bootstrap Profile** | ✅ Complete | 9.3 MB minimal binary |
| **Layout SDN** | ✅ Designed | 4KB page locality optimization |

### 1.2 What Simple Lacks

| Feature | Status | Priority for Embedded |
|---------|--------|----------------------|
| **Bitfields** | ❌ Not implemented | **Critical** |
| **Volatile** | ❌ Not supported | **Critical** |
| **Raw pointers** | ❌ Not supported | **Critical** |
| **Memory barriers** | ⚠️ Via atomics only | High |
| **Inline assembly** | ❌ Not supported | High |
| **Interrupt handlers** | ❌ Not supported | High |
| **repr(C)/packed** | ❌ Not supported | High |
| **Unsafe blocks** | ⚠️ Designed, not impl | High |
| **Const fn/comptime** | ⚠️ Limited (FString only) | Medium |
| **Linker script gen** | ⚠️ Planned | Medium |

---

## 2. Gap Analysis vs Research Paper

### 2.1 Direct Memory Access

**Research Paper Recommendation:**
> Languages like C excel at this by allowing pointer arithmetic... In Zig embedded patterns, a register is represented as a pointer and read/written with *.

**Simple Current State:**
- ❌ No raw pointer syntax
- ❌ No `@intToPtr` equivalent
- ✅ Can use SFFI to call Rust/C for memory access

**Recommendation:**
```simple
# Proposed syntax for raw memory access
extern fn rt_read_u32(addr: u64) -> u32
extern fn rt_write_u32(addr: u64, value: u32)

# Or native syntax (future):
val reg = rawptr<u32>(0x40021000)
*reg = 0xFF  # Requires unsafe block
```

### 2.2 Volatile Memory Access

**Research Paper Recommendation:**
> C uses the `volatile` keyword to ensure each access happens exactly as written... Zig offers volatile pointers for the same purpose.

**Simple Current State:**
- ❌ No `volatile` keyword or attribute
- ✅ Can simulate with `AtomicI64.load(Relaxed)` for some cases
- ❌ No MMIO register support

**Recommendation:**
```simple
# Option 1: Volatile attribute on struct fields
struct GpioRegs:
    @volatile
    status: u32
    @volatile
    control: u32

# Option 2: Volatile pointer type
val status_reg: volatile ptr<u32> = rawptr(0x40020000)
val status = *status_reg  # Guaranteed memory read

# Option 3: Volatile access functions (SFFI)
extern fn rt_volatile_read_u32(addr: u64) -> u32
extern fn rt_volatile_write_u32(addr: u64, value: u32)
```

### 2.3 Memory Barriers

**Research Paper Recommendation:**
> It also provides explicit memory barrier instructions... using inline assembly.

**Simple Current State:**
- ✅ `atomic.fence(ordering)` function exists
- ✅ Memory ordering enum: Relaxed, Acquire, Release, AcqRel, SeqCst
- ❌ No CPU-specific barrier instructions
- ❌ No inline assembly

**Available in `src/lib/atomic.spl`:**
```simple
enum MemoryOrdering:
    Relaxed   # No ordering constraints
    Acquire   # Load-acquire
    Release   # Store-release
    AcqRel    # Both acquire and release
    SeqCst    # Sequentially consistent

fn fence(ordering: MemoryOrdering)
```

### 2.4 Interrupt Handling

**Research Paper Recommendation:**
> Most low-level languages offer ways to define an ISR and integrate it with the hardware's interrupt vector table.

**Simple Current State:**
- ❌ No `@interrupt` attribute
- ❌ No vector table integration
- ❌ No naked functions
- ✅ Can use SFFI to register handlers in Rust

**Recommendation:**
```simple
# Proposed interrupt syntax
@interrupt(vector: 15)  # SysTick on Cortex-M
@naked
fn systick_handler():
    tick_count.fetch_add(1, Relaxed)

# Or SFFI approach (current workaround)
extern fn rt_register_interrupt(vector: i32, handler_ptr: u64) -> bool
```

### 2.5 Compile-Time Computation

**Research Paper Recommendation:**
> Zig's `comptime` blocks or functions can execute during compilation... C++ has `constexpr`.

**Simple Current State:**
- ⚠️ Limited: FString const keys extraction only
- ❌ No `const fn` or `comptime` blocks
- ❌ No static assertions
- ✅ Const key sets for compile-time validation

**What Simple Has:**
```simple
# FString const keys (automatic extraction)
val template = "Hello {name}, you have {count} messages"
# Type: FString with const_keys = ["name", "count"]

# Const key sets
type ConfigKeys = const_keys("host", "port", "debug")
val config: Dict<ConfigKeys, text> = {}
config["portt"] = "8080"  # Compile error: "portt" not in ConfigKeys
```

**Recommendation:**
```simple
# Proposed const fn syntax
const fn compute_lookup_table() -> [u8; 256]:
    val table = [0u8; 256]
    for i in 0..256:
        table[i] = (i * 7 + 13) % 256
    table

val LOOKUP: const [u8; 256] = compute_lookup_table()

# Static assertions
static_assert(size_of<GpioRegs>() == 8, "GPIO regs must be 8 bytes")
```

### 2.6 Zero-Cost Abstractions

**Research Paper Recommendation:**
> Modern systems languages strive to give programmers abstraction without overhead.

**Simple Current State:**
- ✅ Monomorphization for generics
- ✅ Tagged pointer representation (no allocation for primitives)
- ⚠️ RefCell overhead for mutable collections (can disable with `--target=embedded`)
- ❌ No `inline` function attribute implemented

**Memory Representation:**
```
Tagged pointer (64-bit):
┌─────────────────────────────────────────────────────┬─────┐
│                 61 bits payload                      │ 3   │
│                                                      │bits │
└─────────────────────────────────────────────────────┴─────┘
- 0b000: Heap pointer
- 0b001: Immediate integer (61-bit)
- 0b010: Float (NaN-boxing)
- 0b011: Bool
- 0b100: Nil
```

### 2.7 Minimal Runtime

**Research Paper Recommendation:**
> C is minimal by nature... Rust supports bare-metal via `#![no_std]`.

**Simple Current State:**
- ✅ Bootstrap profile: 9.3 MB (down from 40 MB)
- ✅ With UPX compression: ~4.5 MB
- ⚠️ No `no_std` equivalent
- ⚠️ Self-hosting planned (500 lines Rust + 21K Simple)

**Binary Size Progression:**
| Profile | Size | Reduction |
|---------|------|-----------|
| Debug | 423 MB | - |
| Release | 40 MB | 90% |
| Bootstrap | 9.3 MB | 76.8% |
| Bootstrap + UPX | ~4.5 MB | 88.8% |
| All optimizations | ~2.5 MB | 93.8% |

### 2.8 Strong Typing and Safety

**Research Paper Recommendation:**
> Ada is strongly typed... Rust provides memory safety through ownership.

**Simple Current State:**
- ✅ Strong nominal typing (structs/classes/enums distinct)
- ✅ Type aliases are interchangeable
- ✅ Pattern matching with exhaustiveness checking
- ⚠️ Reference capabilities designed, partially exposed
- ❌ No borrow checker (designed but not implemented)
- ❌ No range constraints on numeric types

**Reference Capabilities (in type system):**
```simple
# Designed but not fully exposed:
iso T    # Unique/isolated (single owner)
&T       # Immutable borrow
&mut T   # Mutable borrow
```

---

## 3. Bitfields and Custom Types

### 3.1 Current Bitfield Design

Bitfields are **defined in the grammar** but **not implemented** in the compiler.

**Grammar Definition** (`doc/spec/parser/lexer_parser_grammar_definitions.md`):
```javascript
bitfield_definition: $ => seq(
  optional($.visibility),
  'bitfield',
  $.type_identifier,
  optional(seq('(', $.type, ')')),  // Base storage type
  ':',
  $._indent,
  repeat1($.bitfield_field),
  repeat($.bitfield_constant),
  $._dedent,
),

bitfield_field: $ => seq(
  $.identifier,              // Field name
  ':',
  choice(
    $.integer,               // Bit width: 1, 3, 8
    $.unit_with_repr,        // Unit with repr: cm:i12
  ),
  $._newline,
),
```

**Proposed Syntax** (`doc/design/type_system_features.md`):
```simple
# Packed bitfield struct
bitfield Flags(u8):
    readable: 1      # bit 0
    writable: 1      # bit 1
    executable: 1    # bit 2
    _reserved: 5     # bits 3-7 (padding)

# Usage
val f = Flags(readable: 1, writable: 1, executable: 0)
f.readable = 0       # set bit
val can_write = f.writable  # get bit

# Multi-bit fields
bitfield Color(u32):
    red: 8           # bits 0-7
    green: 8         # bits 8-15
    blue: 8          # bits 16-23
    alpha: 8         # bits 24-31

# Hardware register
bitfield GpioControl(u32):
    mode: 2          # 0=input, 1=output, 2=alt, 3=analog
    output_type: 1   # 0=push-pull, 1=open-drain
    speed: 2         # 0=low, 1=medium, 2=high, 3=very-high
    pull: 2          # 0=none, 1=up, 2=down
    _reserved: 1
    alternate: 4     # Alternate function selection
    _reserved2: 20
```

### 3.2 Implementation Tasks for Bitfields

| Task | Status | Effort |
|------|--------|--------|
| Bitfield declaration parsing | ❌ | 4h |
| Field width specification | ❌ | 2h |
| Automatic offset calculation | ❌ | 3h |
| Getter/setter generation (bit masking) | ❌ | 4h |
| Packed representation guarantee | ❌ | 2h |
| Validation (fields fit in backing type) | ❌ | 2h |
| MIR instructions for bit manipulation | ❌ | 4h |
| FFI compatibility (C struct packing) | ❌ | 3h |
| **Total** | | **24h** |

### 3.3 Unit Types with Bit-Width (Related Feature)

Simple has unit types that can specify bit-width storage:
```simple
unit length(base: f64): m = 1.0, km = 1000.0:
    repr:
        i8       # 8-bit signed
        i12      # 12-bit signed (useful for packed)
        i16, u16
        f32

# Usage with explicit representation:
val distance: length<i12> = 100_m  # Stored in 12 bits
```

---

## 4. Volatile and Memory Access

### 4.1 Current State

- ❌ No `volatile` keyword
- ❌ No MMIO register primitives
- ✅ Atomic operations can simulate some volatile behavior

### 4.2 Recommended Implementation

**Option A: Volatile Attribute on Fields**
```simple
struct PeripheralRegs:
    @volatile @addr(0x40020000)
    status: u32
    @volatile @addr(0x40020004)
    control: u32
    @volatile @addr(0x40020008)
    data: u32
```

**Option B: Volatile Pointer Type**
```simple
# New type: volatile ptr<T>
val status: volatile ptr<u32> = rawptr(0x40020000)
val value = *status  # Guaranteed memory read
*status = 0xFF       # Guaranteed memory write
```

**Option C: SFFI Functions (Current Workaround)**
```simple
# In src/app/io/mod.spl
extern fn rt_volatile_read_u8(addr: u64) -> u8
extern fn rt_volatile_read_u16(addr: u64) -> u16
extern fn rt_volatile_read_u32(addr: u64) -> u32
extern fn rt_volatile_write_u8(addr: u64, value: u8)
extern fn rt_volatile_write_u16(addr: u64, value: u16)
extern fn rt_volatile_write_u32(addr: u64, value: u32)

# Simple wrapper
fn mmio_read<T>(addr: u64) -> T:
    match T:
        u8: rt_volatile_read_u8(addr)
        u16: rt_volatile_read_u16(addr)
        u32: rt_volatile_read_u32(addr)
```

### 4.3 Memory Barrier Usage

Using existing atomic operations for barriers:
```simple
import std.atomic.{fence, MemoryOrdering}

fn write_to_device(data: u32):
    # Write data
    device_buffer = data

    # Ensure write completes before signaling
    fence(Release)

    # Signal device
    device_control = CONTROL_START

fn read_from_device() -> u32:
    # Wait for device ready
    while device_status & STATUS_READY == 0:
        pass

    # Ensure status read happens before data read
    fence(Acquire)

    # Read data
    device_data
```

---

## 5. Interrupt Handling

### 5.1 Proposed Syntax

**Option A: Attribute-Based Interrupts**
```simple
# Interrupt handler with vector number
@interrupt(vector: 15)  # SysTick on Cortex-M
fn systick_handler():
    system_ticks.fetch_add(1, Relaxed)

# Interrupt with priority
@interrupt(vector: 25, priority: 2)
fn uart_rx_handler():
    val byte = uart_read_byte()
    rx_buffer.push(byte)

# Naked function (no prologue/epilogue)
@naked
@interrupt(vector: 3)
fn hard_fault_handler():
    # Assembly-like operations
    asm("bkpt #0")
```

**Option B: SFFI Approach (Current Workaround)**
```simple
# Register interrupt handler via FFI
extern fn rt_interrupt_enable(vector: i32) -> bool
extern fn rt_interrupt_disable(vector: i32) -> bool
extern fn rt_interrupt_set_priority(vector: i32, priority: i32) -> bool
extern fn rt_interrupt_register(vector: i32, handler: fn() -> ()) -> bool

# Usage
fn setup_interrupts():
    rt_interrupt_register(15, systick_callback)
    rt_interrupt_set_priority(15, 0)  # Highest priority
    rt_interrupt_enable(15)

fn systick_callback():
    system_ticks += 1
```

### 5.2 Vector Table Generation

**Option A: Attribute-Based Vector Table**
```simple
# Module-level vector table declaration
@vector_table
val vectors: [fn(); 256] = [
    0: reset_handler,
    1: nmi_handler,
    2: hard_fault_handler,
    3..14: default_handler,
    15: systick_handler,
    16..255: default_handler,
]
```

**Option B: Linker Script Integration**
```sdn
# layout.sdn
vectors:
    section: .isr_vector
    address: 0x08000000
    entries:
        0: reset_handler
        1: nmi_handler
        2: hard_fault_handler
        15: systick_handler
```

---

## 6. Compile-Time Features

### 6.1 Current Compile-Time Capabilities

**FString Const Keys (Implemented):**
```simple
val greeting = "Hello {name}, welcome to {place}"
# Automatically extracts: const_keys = ["name", "place"]

fn render(template: FString, data: Dict<template.keys, text>) -> text:
    template.format(data)

render(greeting, {"name": "Alice", "place": "Wonderland"})  # OK
render(greeting, {"nam": "Alice"})  # Compile error: "nam" not in keys
```

**Const Key Sets (Implemented):**
```simple
type ConfigKeys = const_keys("host", "port", "debug", "timeout")
struct Config:
    settings: Dict<ConfigKeys, text>

val cfg = Config(settings: {
    "host": "localhost",
    "port": "8080",
})
cfg.settings["portt"] = "9000"  # Compile error
```

### 6.2 Proposed Compile-Time Features

**Const Functions:**
```simple
const fn fibonacci(n: i32) -> i32:
    if n <= 1: n
    else: fibonacci(n - 1) + fibonacci(n - 2)

# Computed at compile time
val FIB_10: const i32 = fibonacci(10)  # = 55

const fn crc32_table() -> [u32; 256]:
    val table = [0u32; 256]
    for i in 0..256:
        var crc = i as u32
        for _ in 0..8:
            crc = if crc & 1 != 0:
                (crc >> 1) xor 0xEDB88320
            else:
                crc >> 1
        table[i] = crc
    table

val CRC32_TABLE: const [u32; 256] = crc32_table()
```

**Static Assertions:**
```simple
static_assert(size_of<GpioRegs>() == 8)
static_assert(align_of<DmaDescriptor>() >= 4)
static_assert(BUFFER_SIZE >= 1024, "Buffer too small")
```

**Comptime Blocks:**
```simple
comptime:
    # These execute at compile time
    val NUM_PINS = 16
    val PIN_MASKS = [for i in 0..NUM_PINS: 1 << i]

fn get_pin_mask(pin: i32) -> u32:
    PIN_MASKS[pin]  # Zero-cost lookup
```

---

## 7. Minimal Runtime

### 7.1 Current Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│ Full Rust Runtime (Current: 40K lines, 27 MB)                   │
│ - Parser, type checker, codegen                                 │
│ - GC, memory management                                         │
│ - FFI wrappers                                                  │
└─────────────────────────────────────────────────────────────────┘
                           ↓ executes
┌─────────────────────────────────────────────────────────────────┐
│ User Code (Simple)                                              │
└─────────────────────────────────────────────────────────────────┘
```

### 7.2 Planned Self-Hosting Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│ Bootstrap Runtime (Rust, ~500 lines) - MINIMAL                  │
│ - Basic value representation                                    │
│ - Memory allocation (malloc/free)                               │
│ - FFI bridge (syscalls only)                                    │
└─────────────────────────────────────────────────────────────────┘
                           ↓ executes
┌─────────────────────────────────────────────────────────────────┐
│ Self-Hosted Runtime (Simple, 21,350 lines)                      │
│ src/app/interpreter/* (91 files)                                │
│ - Full interpreter                                              │
│ - GC implementation                                             │
│ - Advanced features                                             │
└─────────────────────────────────────────────────────────────────┘
                           ↓ executes
┌─────────────────────────────────────────────────────────────────┐
│ User Code (Simple)                                              │
└─────────────────────────────────────────────────────────────────┘
```

### 7.3 Bare-Metal Profile (Proposed)

For true bare-metal, a minimal profile would include:
```simple
# simple.toml configuration
[target.baremetal]
default-mutability = "immutable"
panic = "abort"
stack-size = 4096
heap-size = 0           # No heap
gc = false              # No garbage collector
std = false             # No standard library
allocator = "static"    # Static memory only

[target.baremetal.features]
refcell = false
fmt = false
collections = "fixed"   # Fixed-size only
```

**Estimated Size:**
| Component | Size | Notes |
|-----------|------|-------|
| MIR interpreter | ~100 KB | Minimal bytecode VM |
| Core types | ~50 KB | Integer, pointer, array |
| Startup code | ~10 KB | Entry point, stack init |
| **Total** | **~160 KB** | Without std library |

---

## 8. Linker Script Generation

### 8.1 Existing Layout SDN

Simple already has a layout configuration format (`doc/spec/layout.sdn`):

```sdn
layout:
    page_size: 4096
    budgets:
        startup: 8       # 32KB max
        first_frame: 4   # 16KB max
        steady: 0        # Unlimited
        cold: 0          # Unlimited

    patterns:
        startup = [parse_*, init_*, setup_*, load_config_*]
        first_frame = [render_first_*, ui_init_*]
        cold = [help_*, error_*, debug_*]

linker:
    sections:
        startup: .spl.startup
        first_frame: .spl.first_frame
        steady: .spl.steady
        cold: .spl.cold
    page_align: true
    generate_script: false
    script_path: layout.ld
```

### 8.2 Proposed Embedded Linker SDN

```sdn
# embedded.sdn - Linker configuration for bare-metal

memory:
    flash:
        origin: 0x08000000
        length: 512K
        permissions: rx

    sram:
        origin: 0x20000000
        length: 128K
        permissions: rwx

    ccm:
        origin: 0x10000000
        length: 64K
        permissions: rw

sections:
    .isr_vector:
        memory: flash
        address: 0x08000000
        keep: true
        contents:
            - reset_handler
            - nmi_handler
            - hard_fault_handler

    .text:
        memory: flash
        align: 4

    .rodata:
        memory: flash
        align: 4

    .data:
        memory: sram
        load_address: flash
        align: 4

    .bss:
        memory: sram
        align: 4
        type: nobits

    .heap:
        memory: sram
        size: 16K

    .stack:
        memory: ccm
        size: 8K
        direction: descending

symbols:
    _stack_start: .stack.end
    _heap_start: .heap.start
    _heap_end: .heap.end
    _data_start: .data.start
    _data_end: .data.end
    _bss_start: .bss.start
    _bss_end: .bss.end

entry: reset_handler
```

### 8.3 Generated Linker Script

The SDN above would generate:
```ld
/* Auto-generated from embedded.sdn */
MEMORY {
    FLASH (rx)  : ORIGIN = 0x08000000, LENGTH = 512K
    SRAM (rwx)  : ORIGIN = 0x20000000, LENGTH = 128K
    CCM (rw)    : ORIGIN = 0x10000000, LENGTH = 64K
}

SECTIONS {
    .isr_vector 0x08000000 : {
        KEEP(*(.isr_vector))
    } > FLASH

    .text : ALIGN(4) {
        *(.text*)
    } > FLASH

    .rodata : ALIGN(4) {
        *(.rodata*)
    } > FLASH

    .data : ALIGN(4) {
        _data_start = .;
        *(.data*)
        _data_end = .;
    } > SRAM AT > FLASH

    .bss (NOLOAD) : ALIGN(4) {
        _bss_start = .;
        *(.bss*)
        *(COMMON)
        _bss_end = .;
    } > SRAM

    .heap (NOLOAD) : {
        _heap_start = .;
        . = . + 16K;
        _heap_end = .;
    } > SRAM

    .stack (NOLOAD) : {
        . = . + 8K;
        _stack_start = .;
    } > CCM
}

ENTRY(reset_handler)
```

### 8.4 Implementation

```simple
# src/app/linker_gen/main.spl

fn generate_linker_script(config_path: text) -> text:
    val config = sdn_parse(file_read(config_path))
    var script = "/* Auto-generated from {config_path} */\n"

    # Generate MEMORY block
    script += "MEMORY {\n"
    for region in config.memory:
        val perms = region.permissions
        script += "    {region.name} ({perms}) : ORIGIN = {region.origin}, LENGTH = {region.length}\n"
    script += "}\n\n"

    # Generate SECTIONS block
    script += "SECTIONS {\n"
    for section in config.sections:
        script += generate_section(section)
    script += "}\n\n"

    # Generate ENTRY
    script += "ENTRY({config.entry})\n"

    script
```

---

## 9. Implementation Recommendations

### 9.1 Priority Matrix

| Feature | Impact | Effort | Priority |
|---------|--------|--------|----------|
| **Bitfields** | Critical | 24h | **P0** |
| **Volatile access (SFFI)** | Critical | 8h | **P0** |
| **Memory layout attrs** | High | 16h | **P1** |
| **Unsafe blocks** | High | 20h | **P1** |
| **Linker script gen** | High | 16h | **P1** |
| **Const fn** | Medium | 40h | **P2** |
| **Interrupt attrs** | Medium | 24h | **P2** |
| **Static assertions** | Medium | 8h | **P2** |
| **Inline assembly** | Low | 40h | **P3** |

### 9.2 Phase 1: Foundation (Week 1-2)

**Goal:** Enable basic hardware interaction

1. **Implement bitfields** (24h)
   - Parser: Bitfield declaration
   - Type checker: Field widths, offsets
   - Codegen: Getter/setter with bit masking

2. **Add volatile SFFI functions** (8h)
   ```simple
   extern fn rt_volatile_read_u32(addr: u64) -> u32
   extern fn rt_volatile_write_u32(addr: u64, value: u32)
   extern fn rt_memory_barrier()
   ```

3. **Add memory layout attributes** (16h)
   ```simple
   @repr(C)
   @packed
   @align(4)
   struct HardwareRegs:
       status: u32
       control: u32
   ```

### 9.3 Phase 2: Safety (Week 3-4)

**Goal:** Safe low-level access

1. **Implement unsafe blocks** (20h)
   ```simple
   unsafe:
       val ptr = rawptr<u32>(0x40020000)
       *ptr = 0xFF
   ```

2. **Add linker script generation** (16h)
   - Parse SDN configuration
   - Generate GNU LD script
   - Integrate with build system

3. **Static assertions** (8h)
   ```simple
   static_assert(size_of<Regs>() == 8)
   ```

### 9.4 Phase 3: Optimization (Week 5-6)

**Goal:** Zero-cost abstractions

1. **Const fn evaluation** (40h)
   - Parse `const fn` declarations
   - Compile-time evaluation engine
   - Const propagation

2. **Interrupt handling** (24h)
   - `@interrupt` attribute
   - Vector table generation
   - Priority configuration

### 9.5 Phase 4: Advanced (Future)

1. **Inline assembly** (40h)
2. **Full borrow checker** (80h)
3. **Range types** (24h)
4. **RAII/Drop traits** (32h)

---

## 10. Short Grammar for Embedded

### 10.1 Minimal Embedded Syntax

For embedded development, Simple could offer a streamlined subset:

```simple
# Embedded-friendly syntax highlights

# Bitfields (proposed)
bitfield Status(u8):
    ready: 1
    error: 1
    busy: 1
    _: 5

# Fixed arrays (existing)
val buffer: [u8; 1024]

# Volatile access (proposed)
@volatile val status: u32 @ 0x40020000

# Interrupt (proposed)
@interrupt(15)
fn tick():
    count += 1

# No-alloc functions (proposed)
@no_alloc
fn process_data(data: &[u8]) -> u8:
    var sum: u8 = 0
    for b in data:
        sum += b
    sum
```

### 10.2 Syntax Comparison

| Feature | C | Rust | Zig | Simple (Current) | Simple (Proposed) |
|---------|---|------|-----|------------------|-------------------|
| Bitfield | `struct { int x:3; }` | `bitflags!` crate | `packed struct` | ❌ | `bitfield X(u8): ...` |
| Volatile | `volatile int*` | `read_volatile()` | `@ptrCast(*volatile)` | ❌ | `@volatile val x` |
| Pointer | `int* p = (int*)addr` | `addr as *mut i32` | `@intToPtr(*T, addr)` | ❌ | `rawptr<T>(addr)` |
| Interrupt | `__attribute__((interrupt))` | `#[interrupt]` | N/A | ❌ | `@interrupt(n)` |
| Inline asm | `asm("nop")` | `asm!("nop")` | `asm { nop }` | ❌ | `asm("nop")` |
| Comptime | N/A | `const fn` | `comptime` | FString only | `const fn` |

### 10.3 Embedded Example Program

```simple
# blinky.spl - LED blink example for STM32F4
@target(embedded)

# Hardware definitions
bitfield GpioMode(u32):
    moder0: 2
    moder1: 2
    moder2: 2
    moder3: 2
    # ... etc

const GPIO_A_BASE: u64 = 0x40020000
const RCC_BASE: u64 = 0x40023800

@volatile val GPIOA_MODER: ptr<u32> @ GPIO_A_BASE + 0x00
@volatile val GPIOA_ODR: ptr<u32> @ GPIO_A_BASE + 0x14
@volatile val RCC_AHB1ENR: ptr<u32> @ RCC_BASE + 0x30

fn init_gpio():
    # Enable GPIOA clock
    *RCC_AHB1ENR = *RCC_AHB1ENR | (1 << 0)

    # Set PA5 as output (LED on Nucleo board)
    val mode = GpioMode(*GPIOA_MODER)
    mode.moder5 = 0b01  # Output
    *GPIOA_MODER = mode.as_u32()

fn toggle_led():
    *GPIOA_ODR = *GPIOA_ODR xor (1 << 5)

var ticks: u32 = 0

@interrupt(15)  # SysTick
fn systick_handler():
    ticks += 1
    if ticks >= 500:
        toggle_led()
        ticks = 0

@entry
fn main() -> !:
    init_gpio()
    setup_systick(1000)  # 1ms tick

    loop:
        wfi()  # Wait for interrupt
```

---

## Summary

Simple has strong foundations for embedded development:
- ✅ Solid type system with structs, enums, generics
- ✅ SFFI for Rust/C interop
- ✅ Atomic operations with memory ordering
- ✅ Embedded target mode with immutable defaults
- ✅ Bootstrap profile for small binaries

Key gaps to address:
- ❌ Bitfields (designed, needs implementation)
- ❌ Volatile memory access
- ❌ Raw pointer syntax
- ❌ Interrupt handling attributes
- ❌ Const fn / comptime evaluation
- ❌ Linker script generation from SDN

With the recommended Phase 1-2 implementations (~80 hours), Simple would be capable of basic bare-metal programming. Full embedded support comparable to Rust or Zig would require ~200 hours of development.

---

## References

1. Research paper: "Enhancing the 'simple' Language for Bare-Metal Embedded Programming"
2. `doc/design/type_system_features.md` - Bitfield design
3. `doc/design/embedded_immutable_defaults.md` - Embedded target configuration
4. `doc/spec/layout.sdn` - Layout configuration format
5. `doc/format/smf_specification.md` - Binary format with bare-metal support
6. `src/lib/atomic.spl` - Atomic operations and memory ordering
7. `src/app/io/mod.spl` - SFFI wrapper module
