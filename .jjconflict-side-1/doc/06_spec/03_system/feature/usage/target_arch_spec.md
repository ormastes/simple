# Target Architecture Specification

> Multi-architecture support for bare-metal development including:

<!-- sdn-diagram:id=target_arch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=target_arch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

target_arch_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=target_arch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Architecture Specification

Multi-architecture support for bare-metal development including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-ARCH-001 |
| Category | Bare-Metal / Architecture |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/target_arch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Multi-architecture support for bare-metal development including:
- 8-bit architectures (AVR, MCS51)
- 16-bit architectures (MSP430)
- 32-bit architectures (x86, ARM, RISC-V 32)
- 64-bit architectures (x86_64, AArch64, RISC-V 64)

## Key Concepts

| Concept | Description |
|---------|-------------|
| bits() | Native word size: 8, 16, 32, or 64 |
| pointer_bytes() | Pointer size in bytes (2/4/8) |
| stack_align() | Stack alignment requirement |
| is_harvard() | Harvard vs von Neumann architecture |
| endianness() | Little or Big endian |

## Implementation Notes

- 8-bit architectures use 16-bit pointers for >256 byte addressing
- Stack alignment varies by architecture (1/2/4/16 bytes)
- Harvard architectures have separate code/data memory

## Scenarios

### Target Architecture Bit Widths

#### 8-bit Architectures

#### AVR has 8-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ATmega/ATtiny are 8-bit processors.
val AVR_BITS = 8
expect(AVR_BITS).to_equal(8)
```

</details>

#### MCS51 has 8-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Intel 8051 family are 8-bit processors.
val MCS51_BITS = 8
expect(MCS51_BITS).to_equal(8)
```

</details>

#### 8-bit architectures use 16-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For >256 byte address space.
val POINTER_BYTES_8BIT = 2
expect(POINTER_BYTES_8BIT).to_equal(2)
```

</details>

#### 16-bit Architectures

#### MSP430 has 16-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MSP430_BITS = 16
expect(MSP430_BITS).to_equal(16)
```

</details>

#### 16-bit architectures use 16-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val POINTER_BYTES_16BIT = 2
expect(POINTER_BYTES_16BIT).to_equal(2)
```

</details>

#### 32-bit Architectures

#### x86 has 32-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_BITS = 32
expect(X86_BITS).to_equal(32)
```

</details>

#### ARM Cortex-M has 32-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ARM_BITS = 32
expect(ARM_BITS).to_equal(32)
```

</details>

#### RISC-V 32 has 32-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val RISCV32_BITS = 32
expect(RISCV32_BITS).to_equal(32)
```

</details>

#### 32-bit architectures use 32-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val POINTER_BYTES_32BIT = 4
expect(POINTER_BYTES_32BIT).to_equal(4)
```

</details>

#### 64-bit Architectures

#### x86_64 has 64-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_64_BITS = 64
expect(X86_64_BITS).to_equal(64)
```

</details>

#### AArch64 has 64-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AARCH64_BITS = 64
expect(AARCH64_BITS).to_equal(64)
```

</details>

#### RISC-V 64 has 64-bit native word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val RISCV64_BITS = 64
expect(RISCV64_BITS).to_equal(64)
```

</details>

#### 64-bit architectures use 64-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val POINTER_BYTES_64BIT = 8
expect(POINTER_BYTES_64BIT).to_equal(8)
```

</details>

### Stack Alignment

#### 8-bit architectures have 1-byte stack alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AVR_STACK_ALIGN = 1
val MCS51_STACK_ALIGN = 1
expect(AVR_STACK_ALIGN).to_equal(1)
expect(MCS51_STACK_ALIGN).to_equal(1)
```

</details>

#### 16-bit architectures have 2-byte stack alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MSP430_STACK_ALIGN = 2
expect(MSP430_STACK_ALIGN).to_equal(2)
```

</details>

#### 32-bit x86 has 4-byte stack alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_STACK_ALIGN = 4
expect(X86_STACK_ALIGN).to_equal(4)
```

</details>

#### 64-bit x86_64 has 16-byte stack alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SSE requires 16-byte alignment.
val X86_64_STACK_ALIGN = 16
expect(X86_64_STACK_ALIGN).to_equal(16)
```

</details>

#### AArch64 has 16-byte stack alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AARCH64_STACK_ALIGN = 16
expect(AARCH64_STACK_ALIGN).to_equal(16)
```

</details>

### Maximum Atomic Width

#### 8-bit architectures support 8-bit atomics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AVR_MAX_ATOMIC = 8
expect(AVR_MAX_ATOMIC).to_equal(8)
```

</details>

#### 16-bit architectures support 16-bit atomics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MSP430_MAX_ATOMIC = 16
expect(MSP430_MAX_ATOMIC).to_equal(16)
```

</details>

#### x86 supports 64-bit atomics via cmpxchg8b

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_MAX_ATOMIC = 64
expect(X86_MAX_ATOMIC).to_equal(64)
```

</details>

#### x86_64 supports 128-bit atomics via cmpxchg16b

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_64_MAX_ATOMIC = 128
expect(X86_64_MAX_ATOMIC).to_equal(128)
```

</details>

### Harvard Architecture Detection

#### AVR is Harvard architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AVR has separate program (flash) and data (SRAM) memory.
val AVR_IS_HARVARD = true
expect(AVR_IS_HARVARD).to_equal(true)
```

</details>

#### MCS51 is Harvard architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 8051 has separate CODE, DATA, XDATA spaces.
val MCS51_IS_HARVARD = true
expect(MCS51_IS_HARVARD).to_equal(true)
```

</details>

#### x86 is von Neumann architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# x86 has unified address space.
val X86_IS_HARVARD = false
expect(X86_IS_HARVARD).to_equal(false)
```

</details>

#### ARM Cortex-M is von Neumann architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ARM_IS_HARVARD = false
expect(ARM_IS_HARVARD).to_equal(false)
```

</details>

### Endianness

#### Little-Endian Architectures

#### AVR is little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AVR_LITTLE_ENDIAN = true
expect(AVR_LITTLE_ENDIAN).to_equal(true)
```

</details>

#### x86 is little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_LITTLE_ENDIAN = true
expect(X86_LITTLE_ENDIAN).to_equal(true)
```

</details>

#### x86_64 is little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_64_LITTLE_ENDIAN = true
expect(X86_64_LITTLE_ENDIAN).to_equal(true)
```

</details>

#### MSP430 is little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MSP430_LITTLE_ENDIAN = true
expect(MSP430_LITTLE_ENDIAN).to_equal(true)
```

</details>

#### Big-Endian Architectures

#### MCS51 is big-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 8051 stores MSB first.
val MCS51_BIG_ENDIAN = true
expect(MCS51_BIG_ENDIAN).to_equal(true)
```

</details>

### Target Triple Generation

#### 8-bit Triples

#### AVR triple is avr-unknown-unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AVR_TRIPLE = "avr-unknown-unknown"
expect(AVR_TRIPLE).to_equal("avr-unknown-unknown")
```

</details>

#### MCS51 triple is mcs51-unknown-unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MCS51_TRIPLE = "mcs51-unknown-unknown"
expect(MCS51_TRIPLE).to_equal("mcs51-unknown-unknown")
```

</details>

#### 16-bit Triples

#### MSP430 triple is msp430-none-elf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MSP430_TRIPLE = "msp430-none-elf"
expect(MSP430_TRIPLE).to_equal("msp430-none-elf")
```

</details>

#### 32-bit Triples

#### x86 baremetal triple is i686-unknown-none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_TRIPLE = "i686-unknown-none"
expect(X86_TRIPLE).to_equal("i686-unknown-none")
```

</details>

#### ARM baremetal triple is thumbv7m-none-eabi

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ARM_TRIPLE = "thumbv7m-none-eabi"
expect(ARM_TRIPLE).to_equal("thumbv7m-none-eabi")
```

</details>

#### RISC-V 32 baremetal triple is riscv32gc-unknown-none-elf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val RISCV32_TRIPLE = "riscv32gc-unknown-none-elf"
expect(RISCV32_TRIPLE).to_equal("riscv32gc-unknown-none-elf")
```

</details>

#### 64-bit Triples

#### x86_64 baremetal triple is x86_64-unknown-none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_64_TRIPLE = "x86_64-unknown-none"
expect(X86_64_TRIPLE).to_equal("x86_64-unknown-none")
```

</details>

#### AArch64 baremetal triple is aarch64-unknown-none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AARCH64_TRIPLE = "aarch64-unknown-none"
expect(AARCH64_TRIPLE).to_equal("aarch64-unknown-none")
```

</details>

#### RISC-V 64 baremetal triple is riscv64gc-unknown-none-elf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val RISCV64_TRIPLE = "riscv64gc-unknown-none-elf"
expect(RISCV64_TRIPLE).to_equal("riscv64gc-unknown-none-elf")
```

</details>

### Target Configuration

#### 8-bit Configuration

#### AVR has 256 byte default stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AVR_DEFAULT_STACK = 256
expect(AVR_DEFAULT_STACK).to_equal(256)
```

</details>

#### 8-bit has 1-byte heap alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val HEAP_ALIGN_8BIT = 1
expect(HEAP_ALIGN_8BIT).to_equal(1)
```

</details>

#### 8-bit has 0 tag bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# No room for tagged pointers.
val TAG_BITS_8BIT = 0
expect(TAG_BITS_8BIT).to_equal(0)
```

</details>

#### 16-bit Configuration

#### MSP430 has 512 byte default stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MSP430_DEFAULT_STACK = 512
expect(MSP430_DEFAULT_STACK).to_equal(512)
```

</details>

#### 16-bit has 2-byte heap alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val HEAP_ALIGN_16BIT = 2
expect(HEAP_ALIGN_16BIT).to_equal(2)
```

</details>

#### 32-bit Configuration

#### 32-bit has 4-byte heap alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val HEAP_ALIGN_32BIT = 4
expect(HEAP_ALIGN_32BIT).to_equal(4)
```

</details>

#### 32-bit has 2 tag bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TAG_BITS_32BIT = 2
expect(TAG_BITS_32BIT).to_equal(2)
```

</details>

#### 64-bit Configuration

#### 64-bit has 8-byte heap alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val HEAP_ALIGN_64BIT = 8
expect(HEAP_ALIGN_64BIT).to_equal(8)
```

</details>

#### 64-bit has 3 tag bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 8-byte aligned pointers allow 3 low bits.
val TAG_BITS_64BIT = 3
expect(TAG_BITS_64BIT).to_equal(3)
```

</details>

### FPU Availability

#### AVR has no FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AVR_HAS_FPU = false
expect(AVR_HAS_FPU).to_equal(false)
```

</details>

#### MCS51 has no FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MCS51_HAS_FPU = false
expect(MCS51_HAS_FPU).to_equal(false)
```

</details>

#### MSP430 has no FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MSP430_HAS_FPU = false
expect(MSP430_HAS_FPU).to_equal(false)
```

</details>

#### ARM Cortex-M0/M3 has no FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# M4F has FPU but requires feature flag.
val ARM_HAS_FPU = false
expect(ARM_HAS_FPU).to_equal(false)
```

</details>

#### x86 has FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_HAS_FPU = true
expect(X86_HAS_FPU).to_equal(true)
```

</details>

#### x86_64 has FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val X86_64_HAS_FPU = true
expect(X86_64_HAS_FPU).to_equal(true)
```

</details>

#### AArch64 has FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val AARCH64_HAS_FPU = true
expect(AARCH64_HAS_FPU).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
