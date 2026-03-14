# Target Architecture Specification
*Source:* `test/feature/usage/target_arch_spec.spl`
**Feature IDs:** #BM-ARCH-001  |  **Category:** Bare-Metal / Architecture  |  **Status:** In Progress

## Overview



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

## Feature: Target Architecture Bit Widths

### Scenario: 8-bit Architectures

| # | Example | Status |
|---|---------|--------|
| 1 | AVR has 8-bit native word | pass |
| 2 | MCS51 has 8-bit native word | pass |
| 3 | 8-bit architectures use 16-bit pointers | pass |

**Example:** AVR has 8-bit native word
    Given val AVR_BITS = 8
    Then  expect(AVR_BITS).to_equal(8)

**Example:** MCS51 has 8-bit native word
    Given val MCS51_BITS = 8
    Then  expect(MCS51_BITS).to_equal(8)

**Example:** 8-bit architectures use 16-bit pointers
    Given val POINTER_BYTES_8BIT = 2
    Then  expect(POINTER_BYTES_8BIT).to_equal(2)

### Scenario: 16-bit Architectures

| # | Example | Status |
|---|---------|--------|
| 1 | MSP430 has 16-bit native word | pass |
| 2 | 16-bit architectures use 16-bit pointers | pass |

**Example:** MSP430 has 16-bit native word
    Given val MSP430_BITS = 16
    Then  expect(MSP430_BITS).to_equal(16)

**Example:** 16-bit architectures use 16-bit pointers
    Given val POINTER_BYTES_16BIT = 2
    Then  expect(POINTER_BYTES_16BIT).to_equal(2)

### Scenario: 32-bit Architectures

| # | Example | Status |
|---|---------|--------|
| 1 | x86 has 32-bit native word | pass |
| 2 | ARM Cortex-M has 32-bit native word | pass |
| 3 | RISC-V 32 has 32-bit native word | pass |
| 4 | 32-bit architectures use 32-bit pointers | pass |

**Example:** x86 has 32-bit native word
    Given val X86_BITS = 32
    Then  expect(X86_BITS).to_equal(32)

**Example:** ARM Cortex-M has 32-bit native word
    Given val ARM_BITS = 32
    Then  expect(ARM_BITS).to_equal(32)

**Example:** RISC-V 32 has 32-bit native word
    Given val RISCV32_BITS = 32
    Then  expect(RISCV32_BITS).to_equal(32)

**Example:** 32-bit architectures use 32-bit pointers
    Given val POINTER_BYTES_32BIT = 4
    Then  expect(POINTER_BYTES_32BIT).to_equal(4)

### Scenario: 64-bit Architectures

| # | Example | Status |
|---|---------|--------|
| 1 | x86_64 has 64-bit native word | pass |
| 2 | AArch64 has 64-bit native word | pass |
| 3 | RISC-V 64 has 64-bit native word | pass |
| 4 | 64-bit architectures use 64-bit pointers | pass |

**Example:** x86_64 has 64-bit native word
    Given val X86_64_BITS = 64
    Then  expect(X86_64_BITS).to_equal(64)

**Example:** AArch64 has 64-bit native word
    Given val AARCH64_BITS = 64
    Then  expect(AARCH64_BITS).to_equal(64)

**Example:** RISC-V 64 has 64-bit native word
    Given val RISCV64_BITS = 64
    Then  expect(RISCV64_BITS).to_equal(64)

**Example:** 64-bit architectures use 64-bit pointers
    Given val POINTER_BYTES_64BIT = 8
    Then  expect(POINTER_BYTES_64BIT).to_equal(8)

## Feature: Stack Alignment

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | 8-bit architectures have 1-byte stack alignment | pass |
| 2 | 16-bit architectures have 2-byte stack alignment | pass |
| 3 | 32-bit x86 has 4-byte stack alignment | pass |
| 4 | 64-bit x86_64 has 16-byte stack alignment | pass |
| 5 | AArch64 has 16-byte stack alignment | pass |

**Example:** 8-bit architectures have 1-byte stack alignment
    Given val AVR_STACK_ALIGN = 1
    Given val MCS51_STACK_ALIGN = 1
    Then  expect(AVR_STACK_ALIGN).to_equal(1)
    Then  expect(MCS51_STACK_ALIGN).to_equal(1)

**Example:** 16-bit architectures have 2-byte stack alignment
    Given val MSP430_STACK_ALIGN = 2
    Then  expect(MSP430_STACK_ALIGN).to_equal(2)

**Example:** 32-bit x86 has 4-byte stack alignment
    Given val X86_STACK_ALIGN = 4
    Then  expect(X86_STACK_ALIGN).to_equal(4)

**Example:** 64-bit x86_64 has 16-byte stack alignment
    Given val X86_64_STACK_ALIGN = 16
    Then  expect(X86_64_STACK_ALIGN).to_equal(16)

**Example:** AArch64 has 16-byte stack alignment
    Given val AARCH64_STACK_ALIGN = 16
    Then  expect(AARCH64_STACK_ALIGN).to_equal(16)

## Feature: Maximum Atomic Width

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | 8-bit architectures support 8-bit atomics | pass |
| 2 | 16-bit architectures support 16-bit atomics | pass |
| 3 | x86 supports 64-bit atomics via cmpxchg8b | pass |
| 4 | x86_64 supports 128-bit atomics via cmpxchg16b | pass |

**Example:** 8-bit architectures support 8-bit atomics
    Given val AVR_MAX_ATOMIC = 8
    Then  expect(AVR_MAX_ATOMIC).to_equal(8)

**Example:** 16-bit architectures support 16-bit atomics
    Given val MSP430_MAX_ATOMIC = 16
    Then  expect(MSP430_MAX_ATOMIC).to_equal(16)

**Example:** x86 supports 64-bit atomics via cmpxchg8b
    Given val X86_MAX_ATOMIC = 64
    Then  expect(X86_MAX_ATOMIC).to_equal(64)

**Example:** x86_64 supports 128-bit atomics via cmpxchg16b
    Given val X86_64_MAX_ATOMIC = 128
    Then  expect(X86_64_MAX_ATOMIC).to_equal(128)

## Feature: Harvard Architecture Detection

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | AVR is Harvard architecture | pass |
| 2 | MCS51 is Harvard architecture | pass |
| 3 | x86 is von Neumann architecture | pass |
| 4 | ARM Cortex-M is von Neumann architecture | pass |

**Example:** AVR is Harvard architecture
    Given val AVR_IS_HARVARD = true
    Then  expect(AVR_IS_HARVARD).to_equal(true)

**Example:** MCS51 is Harvard architecture
    Given val MCS51_IS_HARVARD = true
    Then  expect(MCS51_IS_HARVARD).to_equal(true)

**Example:** x86 is von Neumann architecture
    Given val X86_IS_HARVARD = false
    Then  expect(X86_IS_HARVARD).to_equal(false)

**Example:** ARM Cortex-M is von Neumann architecture
    Given val ARM_IS_HARVARD = false
    Then  expect(ARM_IS_HARVARD).to_equal(false)

## Feature: Endianness

### Scenario: Little-Endian Architectures

| # | Example | Status |
|---|---------|--------|
| 1 | AVR is little-endian | pass |
| 2 | x86 is little-endian | pass |
| 3 | x86_64 is little-endian | pass |
| 4 | MSP430 is little-endian | pass |

**Example:** AVR is little-endian
    Given val AVR_LITTLE_ENDIAN = true
    Then  expect(AVR_LITTLE_ENDIAN).to_equal(true)

**Example:** x86 is little-endian
    Given val X86_LITTLE_ENDIAN = true
    Then  expect(X86_LITTLE_ENDIAN).to_equal(true)

**Example:** x86_64 is little-endian
    Given val X86_64_LITTLE_ENDIAN = true
    Then  expect(X86_64_LITTLE_ENDIAN).to_equal(true)

**Example:** MSP430 is little-endian
    Given val MSP430_LITTLE_ENDIAN = true
    Then  expect(MSP430_LITTLE_ENDIAN).to_equal(true)

### Scenario: Big-Endian Architectures

| # | Example | Status |
|---|---------|--------|
| 1 | MCS51 is big-endian | pass |

**Example:** MCS51 is big-endian
    Given val MCS51_BIG_ENDIAN = true
    Then  expect(MCS51_BIG_ENDIAN).to_equal(true)

## Feature: Target Triple Generation

### Scenario: 8-bit Triples

| # | Example | Status |
|---|---------|--------|
| 1 | AVR triple is avr-unknown-unknown | pass |
| 2 | MCS51 triple is mcs51-unknown-unknown | pass |

**Example:** AVR triple is avr-unknown-unknown
    Given val AVR_TRIPLE = "avr-unknown-unknown"
    Then  expect(AVR_TRIPLE).to_equal("avr-unknown-unknown")

**Example:** MCS51 triple is mcs51-unknown-unknown
    Given val MCS51_TRIPLE = "mcs51-unknown-unknown"
    Then  expect(MCS51_TRIPLE).to_equal("mcs51-unknown-unknown")

### Scenario: 16-bit Triples

| # | Example | Status |
|---|---------|--------|
| 1 | MSP430 triple is msp430-none-elf | pass |

**Example:** MSP430 triple is msp430-none-elf
    Given val MSP430_TRIPLE = "msp430-none-elf"
    Then  expect(MSP430_TRIPLE).to_equal("msp430-none-elf")

### Scenario: 32-bit Triples

| # | Example | Status |
|---|---------|--------|
| 1 | x86 baremetal triple is i686-unknown-none | pass |
| 2 | ARM baremetal triple is thumbv7m-none-eabi | pass |
| 3 | RISC-V 32 baremetal triple is riscv32gc-unknown-none-elf | pass |

**Example:** x86 baremetal triple is i686-unknown-none
    Given val X86_TRIPLE = "i686-unknown-none"
    Then  expect(X86_TRIPLE).to_equal("i686-unknown-none")

**Example:** ARM baremetal triple is thumbv7m-none-eabi
    Given val ARM_TRIPLE = "thumbv7m-none-eabi"
    Then  expect(ARM_TRIPLE).to_equal("thumbv7m-none-eabi")

**Example:** RISC-V 32 baremetal triple is riscv32gc-unknown-none-elf
    Given val RISCV32_TRIPLE = "riscv32gc-unknown-none-elf"
    Then  expect(RISCV32_TRIPLE).to_equal("riscv32gc-unknown-none-elf")

### Scenario: 64-bit Triples

| # | Example | Status |
|---|---------|--------|
| 1 | x86_64 baremetal triple is x86_64-unknown-none | pass |
| 2 | AArch64 baremetal triple is aarch64-unknown-none | pass |
| 3 | RISC-V 64 baremetal triple is riscv64gc-unknown-none-elf | pass |

**Example:** x86_64 baremetal triple is x86_64-unknown-none
    Given val X86_64_TRIPLE = "x86_64-unknown-none"
    Then  expect(X86_64_TRIPLE).to_equal("x86_64-unknown-none")

**Example:** AArch64 baremetal triple is aarch64-unknown-none
    Given val AARCH64_TRIPLE = "aarch64-unknown-none"
    Then  expect(AARCH64_TRIPLE).to_equal("aarch64-unknown-none")

**Example:** RISC-V 64 baremetal triple is riscv64gc-unknown-none-elf
    Given val RISCV64_TRIPLE = "riscv64gc-unknown-none-elf"
    Then  expect(RISCV64_TRIPLE).to_equal("riscv64gc-unknown-none-elf")

## Feature: Target Configuration

### Scenario: 8-bit Configuration

| # | Example | Status |
|---|---------|--------|
| 1 | AVR has 256 byte default stack | pass |
| 2 | 8-bit has 1-byte heap alignment | pass |
| 3 | 8-bit has 0 tag bits | pass |

**Example:** AVR has 256 byte default stack
    Given val AVR_DEFAULT_STACK = 256
    Then  expect(AVR_DEFAULT_STACK).to_equal(256)

**Example:** 8-bit has 1-byte heap alignment
    Given val HEAP_ALIGN_8BIT = 1
    Then  expect(HEAP_ALIGN_8BIT).to_equal(1)

**Example:** 8-bit has 0 tag bits
    Given val TAG_BITS_8BIT = 0
    Then  expect(TAG_BITS_8BIT).to_equal(0)

### Scenario: 16-bit Configuration

| # | Example | Status |
|---|---------|--------|
| 1 | MSP430 has 512 byte default stack | pass |
| 2 | 16-bit has 2-byte heap alignment | pass |

**Example:** MSP430 has 512 byte default stack
    Given val MSP430_DEFAULT_STACK = 512
    Then  expect(MSP430_DEFAULT_STACK).to_equal(512)

**Example:** 16-bit has 2-byte heap alignment
    Given val HEAP_ALIGN_16BIT = 2
    Then  expect(HEAP_ALIGN_16BIT).to_equal(2)

### Scenario: 32-bit Configuration

| # | Example | Status |
|---|---------|--------|
| 1 | 32-bit has 4-byte heap alignment | pass |
| 2 | 32-bit has 2 tag bits | pass |

**Example:** 32-bit has 4-byte heap alignment
    Given val HEAP_ALIGN_32BIT = 4
    Then  expect(HEAP_ALIGN_32BIT).to_equal(4)

**Example:** 32-bit has 2 tag bits
    Given val TAG_BITS_32BIT = 2
    Then  expect(TAG_BITS_32BIT).to_equal(2)

### Scenario: 64-bit Configuration

| # | Example | Status |
|---|---------|--------|
| 1 | 64-bit has 8-byte heap alignment | pass |
| 2 | 64-bit has 3 tag bits | pass |

**Example:** 64-bit has 8-byte heap alignment
    Given val HEAP_ALIGN_64BIT = 8
    Then  expect(HEAP_ALIGN_64BIT).to_equal(8)

**Example:** 64-bit has 3 tag bits
    Given val TAG_BITS_64BIT = 3
    Then  expect(TAG_BITS_64BIT).to_equal(3)

## Feature: FPU Availability

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | AVR has no FPU | pass |
| 2 | MCS51 has no FPU | pass |
| 3 | MSP430 has no FPU | pass |
| 4 | ARM Cortex-M0/M3 has no FPU | pass |
| 5 | x86 has FPU | pass |
| 6 | x86_64 has FPU | pass |
| 7 | AArch64 has FPU | pass |

**Example:** AVR has no FPU
    Given val AVR_HAS_FPU = false
    Then  expect(AVR_HAS_FPU).to_equal(false)

**Example:** MCS51 has no FPU
    Given val MCS51_HAS_FPU = false
    Then  expect(MCS51_HAS_FPU).to_equal(false)

**Example:** MSP430 has no FPU
    Given val MSP430_HAS_FPU = false
    Then  expect(MSP430_HAS_FPU).to_equal(false)

**Example:** ARM Cortex-M0/M3 has no FPU
    Given val ARM_HAS_FPU = false
    Then  expect(ARM_HAS_FPU).to_equal(false)

**Example:** x86 has FPU
    Given val X86_HAS_FPU = true
    Then  expect(X86_HAS_FPU).to_equal(true)

**Example:** x86_64 has FPU
    Given val X86_64_HAS_FPU = true
    Then  expect(X86_64_HAS_FPU).to_equal(true)

**Example:** AArch64 has FPU
    Given val AARCH64_HAS_FPU = true
    Then  expect(AARCH64_HAS_FPU).to_equal(true)


