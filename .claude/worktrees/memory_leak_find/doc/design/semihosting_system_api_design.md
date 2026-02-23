# Semihosting System API Design for Simple Language

**Date**: 2026-02-05
**Status**: Design
**Author**: Claude (AI Research Assistant)

---

## Executive Summary

This document designs a minimal semihosting-based system API for bare-metal targets. The key innovation is **compile-time string interning** where print statements are converted to handle IDs, reducing binary size and I/O bandwidth significantly.

**Key Features:**
- Minimal API: Limited file I/O + byte-saved system print
- Compile-time print string to handle_id conversion
- Host-side `semi_host_reader` reconstructs strings from SMF
- Support for ARM, RISC-V, and x86 semihosting methods
- 10-100x reduction in print-related code size (similar to defmt)

---

## Table of Contents

1. [Semihosting Methods Research](#1-semihosting-methods-research)
2. [Minimal System API Design](#2-minimal-system-api-design)
3. [String Interning at Compile Time](#3-string-interning-at-compile-time)
4. [SMF Format Updates](#4-smf-format-updates)
5. [Semi Host Reader Design](#5-semi-host-reader-design)
6. [Architecture-Specific Implementation](#6-architecture-specific-implementation)
7. [Size Optimization Analysis](#7-size-optimization-analysis)
8. [Implementation Plan](#8-implementation-plan)

---

## 1. Semihosting Methods Research

### 1.1 ARM Semihosting

**Mechanism**: SVC (Supervisor Call) instruction triggers exception handler that communicates via Debug Communication Channel (DCC) over JTAG.

**Official Specification**: [ARM Semihosting ABI](https://github.com/ARM-software/abi-aa/blob/main/semihosting/semihosting.rst)

**Operation Types:**
| Operation | Code | Description |
|-----------|------|-------------|
| SYS_OPEN | 0x01 | Open file |
| SYS_CLOSE | 0x02 | Close file |
| SYS_WRITEC | 0x03 | Write character |
| SYS_WRITE0 | 0x04 | Write null-terminated string |
| SYS_WRITE | 0x05 | Write bytes to file |
| SYS_READ | 0x06 | Read bytes from file |
| SYS_READC | 0x07 | Read character |
| SYS_CLOCK | 0x10 | Get centiseconds |
| SYS_TIME | 0x11 | Get seconds since epoch |
| SYS_EXIT | 0x18 | Exit with status |

**Instruction Sequence (ARM/Thumb):**
```asm
# ARM mode
mov r0, #operation
ldr r1, =params
svc #0x123456     ; Angel semihosting

# Thumb mode
mov r0, #operation
ldr r1, =params
bkpt #0xAB        ; Thumb semihosting
```

**JTAG/Trace32 Support:**
- Lauterbach TRACE32: Full semihosting support via `SYStem.Option SemiHost ON`
- OpenOCD: `arm semihosting enable`
- J-Link: Built-in semihosting support

### 1.2 RISC-V Semihosting

**Mechanism**: EBREAK instruction followed by magic sequence detected by debugger.

**Official Specification**: [RISC-V Semihosting Spec](https://github.com/riscv/riscv-semihosting-spec)

**Magic Sequence:**
```asm
# RISC-V semihosting trigger
.option push
.option norvc
slli zero, zero, 0x1f   # Magic: Entry NOP
ebreak                   # Breakpoint triggers debugger
srai zero, zero, 0x7    # Magic: Exit NOP
.option pop

# a0 = operation number
# a1 = parameter block pointer
# Return value in a0
```

**Operation Codes**: Same as ARM (SYS_OPEN, SYS_WRITE, etc.)

**Debugger Support:**
- OpenOCD: `riscv semihosting enable`
- SEGGER Ozone: Native RISC-V semihosting support (Oct 2024+)
- Trace32: `SYStem.Option SemiHost ON`

### 1.3 x86 Semihosting (QEMU)

**Mechanism**: Port I/O to ISA debug exit device or special CPUID calls.

**QEMU ISA Debug Exit:**
```asm
# Exit with status code
mov dx, 0xF4        ; ISA debug exit port
mov al, exit_code
out dx, al          ; Triggers QEMU exit

# Exit code mapping: (exit_code << 1) | 1
# So 0 becomes 1, 1 becomes 3
```

**QEMU Serial Output:**
```asm
# COM1 serial output (for test harness)
mov dx, 0x3F8       ; COM1 data port
mov al, character
out dx, al
```

### 1.4 Comparison Summary

| Feature | ARM | RISC-V | x86 (QEMU) |
|---------|-----|--------|------------|
| Trigger | SVC/BKPT | EBREAK + magic | Port I/O |
| Detection | DCC/JTAG | Debug Module | Emulator trap |
| Ops | 20+ standard | Same as ARM | Limited |
| Overhead | ~100 cycles | ~50-100 cycles | Varies |
| Real HW | Yes | Yes | Emulator only |
| Trace32 | Yes | Yes | N/A |

---

## 2. Minimal System API Design

### 2.1 Design Principles

1. **Minimal footprint**: Only essential operations
2. **No formatting on target**: All string work on host
3. **Binary-only I/O**: Send raw bytes/IDs, not strings
4. **Shared core**: Same logic across architectures

### 2.2 System API Interface

```simple
# src/baremetal/system_api.spl

# --- Core Print API (Binary-Only) ---

# Print using interned string handle (compile-time resolved)
@inline
fn semi_print(handle: u32):
    semi_host_call(SYS_WRITE_HANDLE, handle, 0)

# Print handle with single i64 parameter
@inline
fn semi_print1(handle: u32, p0: i64):
    semi_host_call(SYS_WRITE_HANDLE_P1, handle, p0)

# Print handle with two i64 parameters
@inline
fn semi_print2(handle: u32, p0: i64, p1: i64):
    semi_host_call(SYS_WRITE_HANDLE_P2, handle, p0, p1)

# Print handle with three i64 parameters
@inline
fn semi_print3(handle: u32, p0: i64, p1: i64, p2: i64):
    semi_host_call(SYS_WRITE_HANDLE_P3, handle, p0, p1, p2)

# --- Limited File I/O ---

# Open file (host filesystem via semihosting)
fn semi_open(path_handle: u32, mode: u8) -> i32:
    semi_host_call(SYS_OPEN, path_handle, mode as i64) as i32

# Close file
fn semi_close(fd: i32) -> bool:
    semi_host_call(SYS_CLOSE, fd as i64, 0) == 0

# Read bytes into buffer
fn semi_read(fd: i32, buf: rawptr<u8>, len: u32) -> i32:
    semi_host_call(SYS_READ, fd as i64, buf.addr() as i64, len as i64) as i32

# Write bytes from buffer
fn semi_write(fd: i32, buf: rawptr<u8>, len: u32) -> i32:
    semi_host_call(SYS_WRITE, fd as i64, buf.addr() as i64, len as i64) as i32

# --- System Control ---

# Exit with status code
@noreturn
fn semi_exit(code: i32):
    semi_host_call(SYS_EXIT, code as i64, 0)
    unreachable()

# Get time in centiseconds
fn semi_clock() -> i64:
    semi_host_call(SYS_CLOCK, 0, 0)

# --- Architecture-Specific Core ---

# Low-level semihosting call (architecture-specific)
@inline
extern fn semi_host_call(op: u32, arg0: i64, arg1: i64) -> i64
```

### 2.3 Custom Operation Codes

```simple
# Extended operation codes for Simple semihosting
# Standard ARM/RISC-V codes: 0x00-0x1F
# Simple extension codes: 0x100+

const SYS_WRITE_HANDLE: u32 = 0x100    # Print interned string by handle
const SYS_WRITE_HANDLE_P1: u32 = 0x101 # Print with 1 param
const SYS_WRITE_HANDLE_P2: u32 = 0x102 # Print with 2 params
const SYS_WRITE_HANDLE_P3: u32 = 0x103 # Print with 3 params
const SYS_WRITE_HANDLE_PN: u32 = 0x104 # Print with N params (array)

# Param block layout for SYS_WRITE_HANDLE_PN:
# [0]: handle_id (u32)
# [1]: param_count (u32)
# [2..]: param values (i64 each)
```

---

## 3. String Interning at Compile Time

### 3.1 Compile-Time Transformation

**Source Code:**
```simple
fn process_data(count: i64, total: f64):
    print "Processing {count} items, total: {total}"
    if count == 0:
        print "Warning: empty input"
```

**After Compilation (conceptual MIR):**
```simple
fn process_data(count: i64, total: f64):
    # "Processing {count} items, total: {total}" -> handle 0x0042
    semi_print2(0x0042, count, total.to_bits())
    if count == 0:
        # "Warning: empty input" -> handle 0x0043
        semi_print(0x0043)
```

### 3.2 String Table Generation

**Compiler generates string table in SMF:**
```
StringTable Section:
  Handle 0x0042: "Processing {} items, total: {}"
                 format_types: [Int64, Float64]
  Handle 0x0043: "Warning: empty input"
                 format_types: []
  Handle 0x0044: "test/spec.spl:42"  # Source location
                 format_types: []
```

### 3.3 Format Specifier Encoding

```simple
# Format type IDs (encoded in string table metadata)
enum FormatType: u8:
    None = 0        # No formatting (literal)
    Int8 = 1
    Int16 = 2
    Int32 = 3
    Int64 = 4
    UInt8 = 5
    UInt16 = 6
    UInt32 = 7
    UInt64 = 8
    Float32 = 9
    Float64 = 10
    Bool = 11
    Char = 12
    Hex8 = 13       # {:x} format
    Hex16 = 14
    Hex32 = 15
    Hex64 = 16
    Binary = 17     # {:b} format
    Pointer = 18    # {:p} format
```

---

## 4. SMF Format Updates

### 4.1 New Section: StringIntern

Add new section type to SMF specification:

```
Section Type: StringIntern (0x10)
Purpose: Interned strings for semihosting print

Structure:
┌────────────────────────────────────┐
│ Section Header (64 bytes)          │
├────────────────────────────────────┤
│ StringIntern Header (16 bytes)     │
│   - entry_count: u32               │
│   - string_data_size: u32          │
│   - format_data_size: u32          │
│   - reserved: u32                  │
├────────────────────────────────────┤
│ Entry Table (12 bytes × count)     │
│   - handle: u32                    │
│   - string_offset: u32             │
│   - format_offset: u32             │
├────────────────────────────────────┤
│ String Data (variable)             │
│   - null-terminated UTF-8 strings  │
├────────────────────────────────────┤
│ Format Data (variable)             │
│   - format_count: u8               │
│   - format_types: [FormatType]     │
└────────────────────────────────────┘
```

### 4.2 Example SMF StringIntern Section

```
Entry Table:
  [0] handle=0x0042, str_off=0, fmt_off=0
  [1] handle=0x0043, str_off=32, fmt_off=3

String Data:
  0x00: "Processing {} items, total: {}\0"
  0x20: "Warning: empty input\0"

Format Data:
  0x00: 02 04 0A        # 2 params: Int64, Float64
  0x03: 00              # 0 params
```

### 4.3 Source Location Interning (Optional)

For debugging, intern source locations too:

```simple
# Debug print with source location
@debug_print
fn debug_assert(cond: bool, msg_handle: u32):
    if not cond:
        # Compiler adds source location automatically
        semi_print2(SRC_LOC_HANDLE, msg_handle, 0)
        semi_exit(1)
```

---

## 5. Semi Host Reader Design

### 5.1 Overview

`semi_host_reader` runs on the host machine and:
1. Receives binary semihosting calls from target
2. Looks up string handles in SMF file
3. Formats and displays human-readable output

### 5.2 Architecture

```
┌─────────────────┐     JTAG/Serial     ┌─────────────────────┐
│   Target MCU    │ ──────────────────► │  semi_host_reader   │
│                 │  handle + params    │                     │
│ semi_print2(    │                     │ 1. Receive handle   │
│   0x42, 10, 3.5 │                     │ 2. Load SMF string  │
│ )               │                     │ 3. Format output    │
└─────────────────┘                     │ 4. Display:         │
                                        │    "Processing 10   │
                                        │     items, total:   │
                                        │     3.5"            │
                                        └─────────────────────┘
                                                  │
                                                  ▼
                                        ┌─────────────────────┐
                                        │     SMF File        │
                                        │  (StringIntern      │
                                        │   Section)          │
                                        └─────────────────────┘
```

### 5.3 Command Line Interface

```bash
# Start semi_host_reader
simple semi-host-reader \
    --smf-root=/path/to/project/build \
    --transport=openocd \
    --target=arm-cortex-m4 \
    --output=stdout

# Options:
#   --smf-root    : Path to SMF files (for string lookup)
#   --transport   : openocd, jlink, trace32, serial, qemu
#   --target      : Target architecture
#   --output      : stdout, file, json
#   --timestamp   : Add timestamps to output
```

### 5.4 Implementation

```simple
# src/app/semihost/reader.spl

struct SemiHostReader:
    smf_root: text
    string_table: Dict<u32, InternedString>
    transport: Transport

struct InternedString:
    text: text
    format_types: [FormatType]

impl SemiHostReader:
    static fn new(smf_root: text, transport: Transport) -> SemiHostReader:
        val reader = SemiHostReader(
            smf_root: smf_root,
            string_table: {},
            transport: transport
        )
        reader.load_all_smf_files()
        reader

    # Load string tables from all SMF files in root
    me load_all_smf_files():
        val smf_files = glob(self.smf_root + "/**/*.smf")
        for smf_path in smf_files:
            self.load_smf_strings(smf_path)

    # Load strings from single SMF file
    me load_smf_strings(smf_path: text):
        val smf = SmfFile.load(smf_path)
        val section = smf.find_section(SectionType.StringIntern)
        if section.?:
            for entry in section.entries():
                self.string_table[entry.handle] = InternedString(
                    text: entry.string,
                    format_types: entry.format_types
                )

    # Main reader loop
    fn run():
        while true:
            val call = self.transport.receive_call()
            match call.op:
                case SYS_WRITE_HANDLE:
                    self.handle_print(call.handle, [])
                case SYS_WRITE_HANDLE_P1:
                    self.handle_print(call.handle, [call.p0])
                case SYS_WRITE_HANDLE_P2:
                    self.handle_print(call.handle, [call.p0, call.p1])
                case SYS_WRITE_HANDLE_P3:
                    self.handle_print(call.handle, [call.p0, call.p1, call.p2])
                case SYS_EXIT:
                    print "[EXIT] Code: {call.p0}"
                    break
                case _:
                    # Pass through to standard semihosting
                    self.transport.handle_standard(call)

    # Format and print interned string
    fn handle_print(handle: u32, params: [i64]):
        val entry = self.string_table.get(handle)
        if not entry.?:
            print "[UNKNOWN HANDLE: 0x{handle:08x}] params={params}"
            return

        val interned = entry.unwrap()
        val formatted = self.format_string(interned.text, interned.format_types, params)
        print formatted

    # Format string with parameters
    fn format_string(template: text, types: [FormatType], params: [i64]) -> text:
        var result = template
        var param_idx = 0

        while result.contains("{}") and param_idx < params.len():
            val param = params[param_idx]
            val fmt_type = if param_idx < types.len(): types[param_idx] else: FormatType.Int64

            val formatted = match fmt_type:
                case FormatType.Int64: param.to_string()
                case FormatType.Float64: f64.from_bits(param as u64).to_string()
                case FormatType.Bool: if param != 0: "true" else: "false"
                case FormatType.Hex32: "0x{param as u32:08x}"
                case FormatType.Hex64: "0x{param:016x}"
                case _: param.to_string()

            result = result.replace_first("{}", formatted)
            param_idx = param_idx + 1

        result
```

---

## 6. Architecture-Specific Implementation

### 6.1 ARM Cortex-M Implementation

```simple
# src/baremetal/arm/semihost.spl

@cfg("target_arch", "arm")
@inline
fn semi_host_call(op: u32, arg0: i64, arg1: i64) -> i64:
    var result: i64
    # Thumb-2 semihosting via BKPT
    asm(
        "mov r0, {op}",
        "ldr r1, ={params}",
        "bkpt #0xAB",
        "mov {result}, r0",
        op = in(r0) op,
        params = in(r1) [arg0, arg1].as_ptr(),
        result = out(r0) result
    )
    result
```

### 6.2 RISC-V Implementation

```simple
# src/baremetal/riscv/semihost.spl

@cfg("target_arch", "riscv32")
@inline
fn semi_host_call(op: u32, arg0: i64, arg1: i64) -> i64:
    var result: i64
    asm(
        ".option push",
        ".option norvc",
        "mv a0, {op}",
        "mv a1, {params}",
        "slli zero, zero, 0x1f",  # Entry magic
        "ebreak",
        "srai zero, zero, 0x7",   # Exit magic
        "mv {result}, a0",
        ".option pop",
        op = in(a0) op,
        params = in(a1) [arg0, arg1].as_ptr(),
        result = out(a0) result
    )
    result
```

### 6.3 x86 QEMU Implementation

```simple
# src/baremetal/x86/semihost.spl

@cfg("target_arch", "x86")
@inline
fn semi_host_call(op: u32, arg0: i64, arg1: i64) -> i64:
    match op:
        case SYS_EXIT:
            # QEMU ISA debug exit
            asm("outb %al, %dx", in(dx) 0xF4u16, in(al) (arg0 as u8))
            0
        case SYS_WRITE_HANDLE | SYS_WRITE_HANDLE_P1 | SYS_WRITE_HANDLE_P2 | SYS_WRITE_HANDLE_P3:
            # Serial output: encode as binary protocol
            serial_write_u32(op)
            serial_write_u32(arg0 as u32)  # handle
            if op >= SYS_WRITE_HANDLE_P1:
                serial_write_i64(arg1)
            0
        case _:
            # Unsupported
            -1

fn serial_write_u32(val: u32):
    for i in 0..4:
        val byte = ((val >> (i * 8)) & 0xFF) as u8
        asm("outb %al, %dx", in(dx) 0x3F8u16, in(al) byte)
```

---

## 7. Size Optimization Analysis

### 7.1 Traditional Printf vs Interned Print

**Traditional Printf:**
```c
// Each printf adds ~50-200 bytes for format parsing
printf("Processing %lld items, total: %f\n", count, total);
// Code size: ~80 bytes (call + format string + args setup)
// String size: 32 bytes
// Total: ~112 bytes per print statement
```

**Interned Print:**
```simple
semi_print2(0x0042, count, total.to_bits())
// Code size: ~12 bytes (load handle + 2 args + call)
// String stored in SMF: 0 bytes in binary
// Total: ~12 bytes per print statement
```

**Size Reduction: 89% per print statement**

### 7.2 Overall Binary Size Impact

| Component | Traditional | Interned | Reduction |
|-----------|-------------|----------|-----------|
| Printf implementation | 5-20 KB | 0 KB | 100% |
| Format strings | Varies | 0 KB* | 100% |
| Per-print overhead | ~100 bytes | ~12 bytes | 88% |
| Semihost stub | 0 KB | ~200 bytes | -200 bytes |

*Strings moved to SMF StringIntern section on host

**Example: 50 print statements**
- Traditional: 50 × 100 + 10,000 (printf) = 15,000 bytes
- Interned: 50 × 12 + 200 (stub) = 800 bytes
- **Reduction: 94.7%**

### 7.3 Comparison with defmt (Rust)

| Feature | defmt | Simple Interned |
|---------|-------|-----------------|
| String interning | Yes | Yes |
| Compile-time | Yes | Yes |
| Host decoder | Yes | Yes |
| Custom format | Limited | Full |
| SMF integration | No | Yes |
| Multi-arch | ARM/RISC-V | ARM/RISC-V/x86 |

---

## 8. Implementation Plan

### 8.1 Phase 1: Core Infrastructure (16h)

1. **StringIntern section in SMF** (8h)
   - Update SMF specification
   - Add section type 0x10
   - Implement writer/reader

2. **Compiler string collection** (8h)
   - Extract print format strings
   - Assign handles
   - Generate StringIntern section

### 8.2 Phase 2: Architecture Support (24h)

1. **ARM semihosting** (8h)
   - BKPT instruction sequence
   - OpenOCD integration testing

2. **RISC-V semihosting** (8h)
   - EBREAK + magic sequence
   - OpenOCD integration testing

3. **x86/QEMU semihosting** (8h)
   - Serial protocol for QEMU
   - ISA debug exit

### 8.3 Phase 3: Host Tools (16h)

1. **semi_host_reader** (12h)
   - SMF loading
   - Transport abstraction
   - String formatting

2. **Integration with test runner** (4h)
   - Connect to QEMU test harness
   - Parse semihosting output

### 8.4 Phase 4: Testing & Documentation (8h)

1. **SSpec tests** (4h)
   - Compile-time interning tests
   - Host reader tests

2. **Documentation** (4h)
   - Update SMF spec
   - Usage guide

**Total: 64 hours**

---

## Sources

### ARM Semihosting
- [ARM Semihosting ABI Specification](https://github.com/ARM-software/abi-aa/blob/main/semihosting/semihosting.rst)
- [Lauterbach TRACE32 ARM Debugger Manual](https://www2.lauterbach.com/pdf/debugger_arm.pdf)
- [Semihosting on ARM with GCC and OpenOCD](https://bgamari.github.io/posts/2014-10-31-semihosting.html)

### RISC-V Semihosting
- [RISC-V Semihosting Specification](https://github.com/riscv/riscv-semihosting-spec)
- [Understanding RISC-V Semihosting](https://embeddedinn.com/articles/tutorial/understanding-riscv-semihosting/)
- [SEGGER Ozone RISC-V Semihosting Support](https://www.segger.com/news/pr-241015-ozone-riscv-semihosting/)
- [Lauterbach TRACE32 RISC-V Debugger Manual](https://repo.lauterbach.com/pdfnew/debugger_riscv.pdf)

### Printf Optimization
- [defmt: Efficient Logging for Embedded Rust](https://github.com/knurling-rs/defmt)
- [defmt Documentation](https://defmt.ferrous-systems.com/)
- [Pigweed Size Optimizations](https://pigweed.dev/size_optimizations.html)
- [Embedded Artistry Printf Implementation](https://embeddedartistry.com/blog/2019/11/06/an-embedded-friendly-printf-implementation/)

---

## Appendix A: Full Operation Code Table

```simple
# Standard ARM/RISC-V Semihosting Operations
const SYS_OPEN: u32 = 0x01
const SYS_CLOSE: u32 = 0x02
const SYS_WRITEC: u32 = 0x03
const SYS_WRITE0: u32 = 0x04
const SYS_WRITE: u32 = 0x05
const SYS_READ: u32 = 0x06
const SYS_READC: u32 = 0x07
const SYS_ISERROR: u32 = 0x08
const SYS_ISTTY: u32 = 0x09
const SYS_SEEK: u32 = 0x0A
const SYS_FLEN: u32 = 0x0C
const SYS_TMPNAM: u32 = 0x0D
const SYS_REMOVE: u32 = 0x0E
const SYS_RENAME: u32 = 0x0F
const SYS_CLOCK: u32 = 0x10
const SYS_TIME: u32 = 0x11
const SYS_SYSTEM: u32 = 0x12
const SYS_ERRNO: u32 = 0x13
const SYS_GET_CMDLINE: u32 = 0x15
const SYS_HEAPINFO: u32 = 0x16
const SYS_EXIT: u32 = 0x18
const SYS_EXIT_EXTENDED: u32 = 0x20
const SYS_ELAPSED: u32 = 0x30
const SYS_TICKFREQ: u32 = 0x31

# Simple Extensions (0x100+)
const SYS_WRITE_HANDLE: u32 = 0x100
const SYS_WRITE_HANDLE_P1: u32 = 0x101
const SYS_WRITE_HANDLE_P2: u32 = 0x102
const SYS_WRITE_HANDLE_P3: u32 = 0x103
const SYS_WRITE_HANDLE_PN: u32 = 0x104
```

---

## Appendix B: SMF StringIntern Binary Format

```
Offset  Size  Field
------  ----  -----
0x00    4     entry_count
0x04    4     string_data_size
0x08    4     format_data_size
0x0C    4     reserved (0)
0x10    12*N  Entry Table
              [0..4] handle (u32)
              [4..8] string_offset (u32)
              [8..12] format_offset (u32)
+       var   String Data (null-terminated UTF-8)
+       var   Format Data (count + types)
```
