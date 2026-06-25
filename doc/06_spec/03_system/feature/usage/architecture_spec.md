# Multi-Architecture Support

> Tests multi-architecture support across 8-bit, 16-bit, 32-bit, and 64-bit targets including AVR, MCS51, MSP430, x86, ARM, RISC-V, x86_64, and AArch64. Validates architecture properties (pointer size, stack alignment, FPU, endianness), target triple generation for bare-metal and hosted environments, and TargetConfig generation for each bit-width class.

<!-- sdn-diagram:id=architecture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=architecture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

architecture_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=architecture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-Architecture Support

Tests multi-architecture support across 8-bit, 16-bit, 32-bit, and 64-bit targets including AVR, MCS51, MSP430, x86, ARM, RISC-V, x86_64, and AArch64. Validates architecture properties (pointer size, stack alignment, FPU, endianness), target triple generation for bare-metal and hosted environments, and TargetConfig generation for each bit-width class.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ARCH-002 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/usage/architecture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests multi-architecture support across 8-bit, 16-bit, 32-bit, and 64-bit targets
including AVR, MCS51, MSP430, x86, ARM, RISC-V, x86_64, and AArch64. Validates
architecture properties (pointer size, stack alignment, FPU, endianness),
target triple generation for bare-metal and hosted environments, and
TargetConfig generation for each bit-width class.

## Syntax

```simple
val avr = TargetArch.AVR
expect(avr.bits()).to_equal(8)
val config = TargetConfig.for_arch(TargetArch.X86_64)
```
Architecture Support Specification

Tests multi-architecture support (8/16/32/64-bit) including:
- Target architecture properties
- Pointer-sized types (usize/isize)
- Calling conventions
- Type layout per architecture

Feature IDs: #BM-ARCH-001
Category: Bare-Metal
Status: In Progress

NOTE: parse tests use parse_target_arch() free function wrapper
instead of TargetArch.parse() static method (not supported in interpreter)

## Scenarios

### Target Architecture

### 8-bit Architectures

#### AVR has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avr = TargetArch.AVR
expect(avr.bits()).to_equal(8)
expect(avr.pointer_bytes()).to_equal(2)
expect(avr.stack_align()).to_equal(1)
expect(avr.max_atomic_width()).to_equal(8)
expect(avr.has_fpu()).to_equal(false)
expect(avr.is_harvard()).to_equal(true)
expect(avr.endianness()).to_equal(Endian.Little)
```

</details>

#### MCS51 has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcs51 = TargetArch.MCS51
expect(mcs51.bits()).to_equal(8)
expect(mcs51.pointer_bytes()).to_equal(2)
expect(mcs51.stack_align()).to_equal(1)
expect(mcs51.has_fpu()).to_equal(false)
expect(mcs51.is_harvard()).to_equal(true)
expect(mcs51.endianness()).to_equal(Endian.Big)
```

</details>

#### AVR parses from string

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_target_arch("avr")
expect(parsed.?).to_equal(true)
expect(parsed.unwrap()).to_equal(TargetArch.AVR)

val parsed2 = parse_target_arch("atmega")
expect(parsed2.?).to_equal(true)
expect(parsed2.unwrap()).to_equal(TargetArch.AVR)
```

</details>

### 16-bit Architectures

#### MSP430 has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msp = TargetArch.MSP430
expect(msp.bits()).to_equal(16)
expect(msp.pointer_bytes()).to_equal(2)
expect(msp.stack_align()).to_equal(2)
expect(msp.max_atomic_width()).to_equal(16)
expect(msp.has_fpu()).to_equal(false)
expect(msp.is_harvard()).to_equal(false)
expect(msp.endianness()).to_equal(Endian.Little)
```

</details>

#### MSP430 parses from string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_target_arch("msp430")
expect(parsed.?).to_equal(true)
expect(parsed.unwrap()).to_equal(TargetArch.MSP430)
```

</details>

### 32-bit Architectures

#### x86 has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = TargetArch.X86
expect(x86.bits()).to_equal(32)
expect(x86.pointer_bytes()).to_equal(4)
expect(x86.stack_align()).to_equal(4)
expect(x86.max_atomic_width()).to_equal(64)
expect(x86.has_fpu()).to_equal(true)
expect(x86.is_harvard()).to_equal(false)
```

</details>

#### ARM has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm = TargetArch.Arm
expect(arm.bits()).to_equal(32)
expect(arm.pointer_bytes()).to_equal(4)
expect(arm.stack_align()).to_equal(4)
expect(arm.has_fpu()).to_equal(false)  # Cortex-M0/M3
```

</details>

#### RISC-V 32 has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv32 = TargetArch.Riscv32
expect(rv32.bits()).to_equal(32)
expect(rv32.pointer_bytes()).to_equal(4)
```

</details>

### 64-bit Architectures

#### x86_64 has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x64 = TargetArch.X86_64
expect(x64.bits()).to_equal(64)
expect(x64.pointer_bytes()).to_equal(8)
expect(x64.stack_align()).to_equal(16)
expect(x64.max_atomic_width()).to_equal(128)
expect(x64.has_fpu()).to_equal(true)
```

</details>

#### AArch64 has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64 = TargetArch.Aarch64
expect(arm64.bits()).to_equal(64)
expect(arm64.pointer_bytes()).to_equal(8)
expect(arm64.stack_align()).to_equal(16)
```

</details>

#### RISC-V 64 has correct properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = TargetArch.Riscv64
expect(rv64.bits()).to_equal(64)
expect(rv64.pointer_bytes()).to_equal(8)
```

</details>

### Pointer Size

#### 8-bit and 16-bit use 16-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avr = TargetArch.AVR
val mcs51 = TargetArch.MCS51
val msp430 = TargetArch.MSP430
expect(avr.pointer_size()).to_equal(PointerSize.Bits16)
expect(mcs51.pointer_size()).to_equal(PointerSize.Bits16)
expect(msp430.pointer_size()).to_equal(PointerSize.Bits16)
```

</details>

#### 32-bit uses 32-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = TargetArch.X86
val arm = TargetArch.Arm
val rv32 = TargetArch.Riscv32
expect(x86.pointer_size()).to_equal(PointerSize.Bits32)
expect(arm.pointer_size()).to_equal(PointerSize.Bits32)
expect(rv32.pointer_size()).to_equal(PointerSize.Bits32)
```

</details>

#### 64-bit uses 64-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x64 = TargetArch.X86_64
val arm64 = TargetArch.Aarch64
val rv64 = TargetArch.Riscv64
expect(x64.pointer_size()).to_equal(PointerSize.Bits64)
expect(arm64.pointer_size()).to_equal(PointerSize.Bits64)
expect(rv64.pointer_size()).to_equal(PointerSize.Bits64)
```

</details>

#### PointerSize returns correct byte count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p16 = PointerSize.Bits16
val p32 = PointerSize.Bits32
val p64 = PointerSize.Bits64
expect(p16.bytes()).to_equal(2)
expect(p32.bytes()).to_equal(4)
expect(p64.bytes()).to_equal(8)
```

</details>

### Target Triple

#### generates correct bare-metal triples

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avr = TargetArch.AVR
val msp430 = TargetArch.MSP430
val x86 = TargetArch.X86
val arm = TargetArch.Arm
val x64 = TargetArch.X86_64
expect(avr.triple_str_baremetal()).to_equal("avr-unknown-unknown")
expect(msp430.triple_str_baremetal()).to_equal("msp430-none-elf")
expect(x86.triple_str_baremetal()).to_equal("i686-unknown-none")
expect(arm.triple_str_baremetal()).to_equal("thumbv7m-none-eabi")
expect(x64.triple_str_baremetal()).to_equal("x86_64-unknown-none")
```

</details>

#### generates correct hosted triples

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = TargetArch.X86
val x64 = TargetArch.X86_64
val arm = TargetArch.Arm
expect(x86.triple_str()).to_equal("i686-unknown-linux-gnu")
expect(x64.triple_str()).to_equal("x86_64-unknown-linux-gnu")
expect(arm.triple_str()).to_equal("armv7-unknown-linux-gnueabihf")
```

</details>

### Target Config

#### configures 8-bit correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TargetConfig.for_arch(TargetArch.AVR)
expect(config.pointer_bytes).to_equal(2)
expect(config.value_bytes).to_equal(2)
expect(config.tag_bits).to_equal(0)
expect(config.heap_align).to_equal(1)
expect(config.default_stack_size).to_equal(256)
```

</details>

#### configures 16-bit correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TargetConfig.for_arch(TargetArch.MSP430)
expect(config.pointer_bytes).to_equal(2)
expect(config.value_bytes).to_equal(2)
expect(config.tag_bits).to_equal(1)
expect(config.heap_align).to_equal(2)
expect(config.default_stack_size).to_equal(512)
```

</details>

#### configures 32-bit correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TargetConfig.for_arch(TargetArch.X86)
expect(config.pointer_bytes).to_equal(4)
expect(config.value_bytes).to_equal(8)
expect(config.tag_bits).to_equal(2)
expect(config.heap_align).to_equal(4)
```

</details>

#### configures 64-bit correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TargetConfig.for_arch(TargetArch.X86_64)
expect(config.pointer_bytes).to_equal(8)
expect(config.value_bytes).to_equal(8)
expect(config.tag_bits).to_equal(3)
expect(config.heap_align).to_equal(8)
```

</details>

### Architecture Bit Width Helpers

#### is_8bit returns true for 8-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avr = TargetArch.AVR
val mcs51 = TargetArch.MCS51
val x86 = TargetArch.X86
expect(avr.is_8bit()).to_equal(true)
expect(mcs51.is_8bit()).to_equal(true)
expect(x86.is_8bit()).to_equal(false)
```

</details>

#### is_16bit returns true for 16-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msp430 = TargetArch.MSP430
val avr = TargetArch.AVR
expect(msp430.is_16bit()).to_equal(true)
expect(avr.is_16bit()).to_equal(false)
```

</details>

#### is_32bit returns true for 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = TargetArch.X86
val arm = TargetArch.Arm
val x64 = TargetArch.X86_64
expect(x86.is_32bit()).to_equal(true)
expect(arm.is_32bit()).to_equal(true)
expect(x64.is_32bit()).to_equal(false)
```

</details>

#### is_64bit returns true for 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x64 = TargetArch.X86_64
val arm64 = TargetArch.Aarch64
val x86 = TargetArch.X86
expect(x64.is_64bit()).to_equal(true)
expect(arm64.is_64bit()).to_equal(true)
expect(x86.is_64bit()).to_equal(false)
```

</details>

### Endianness

#### most architectures are little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avr = TargetArch.AVR
val msp430 = TargetArch.MSP430
val x86 = TargetArch.X86
val x64 = TargetArch.X86_64
expect(avr.endianness()).to_equal(Endian.Little)
expect(msp430.endianness()).to_equal(Endian.Little)
expect(x86.endianness()).to_equal(Endian.Little)
expect(x64.endianness()).to_equal(Endian.Little)
```

</details>

#### MCS51 is big-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcs51 = TargetArch.MCS51
expect(mcs51.endianness()).to_equal(Endian.Big)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
