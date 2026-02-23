# Target Architecture Specification

**Feature ID:** #BM-ARCH-001 | **Category:** Bare-Metal / Architecture | **Difficulty:** 2/5 | **Status:** In Progress

_Source: `test/feature/usage/target_arch_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 56 |

## Test Structure

### Target Architecture Bit Widths
_Verify correct bit width for each architecture class._

#### 8-bit Architectures
_AVR and MCS51 are 8-bit microcontrollers._

- ✅ AVR has 8-bit native word
- ✅ MCS51 has 8-bit native word
- ✅ 8-bit architectures use 16-bit pointers
#### 16-bit Architectures
_MSP430 is a 16-bit ultra-low-power microcontroller._

- ✅ MSP430 has 16-bit native word
- ✅ 16-bit architectures use 16-bit pointers
#### 32-bit Architectures
_x86, ARM Cortex-M, RISC-V 32._

- ✅ x86 has 32-bit native word
- ✅ ARM Cortex-M has 32-bit native word
- ✅ RISC-V 32 has 32-bit native word
- ✅ 32-bit architectures use 32-bit pointers
#### 64-bit Architectures
_x86_64, AArch64, RISC-V 64._

- ✅ x86_64 has 64-bit native word
- ✅ AArch64 has 64-bit native word
- ✅ RISC-V 64 has 64-bit native word
- ✅ 64-bit architectures use 64-bit pointers
### Stack Alignment
_Verify correct stack alignment for each architecture._

- ✅ 8-bit architectures have 1-byte stack alignment
- ✅ 16-bit architectures have 2-byte stack alignment
- ✅ 32-bit x86 has 4-byte stack alignment
- ✅ 64-bit x86_64 has 16-byte stack alignment
- ✅ AArch64 has 16-byte stack alignment
### Maximum Atomic Width
_Verify maximum atomic operation width for each architecture._

- ✅ 8-bit architectures support 8-bit atomics
- ✅ 16-bit architectures support 16-bit atomics
- ✅ x86 supports 64-bit atomics via cmpxchg8b
- ✅ x86_64 supports 128-bit atomics via cmpxchg16b
### Harvard Architecture Detection
_Verify Harvard vs von Neumann architecture detection._

- ✅ AVR is Harvard architecture
- ✅ MCS51 is Harvard architecture
- ✅ x86 is von Neumann architecture
- ✅ ARM Cortex-M is von Neumann architecture
### Endianness
_Verify byte order for each architecture._

#### Little-Endian Architectures

- ✅ AVR is little-endian
- ✅ x86 is little-endian
- ✅ x86_64 is little-endian
- ✅ MSP430 is little-endian
#### Big-Endian Architectures

- ✅ MCS51 is big-endian
### Target Triple Generation
_Verify target triple string format for bare-metal._

#### 8-bit Triples

- ✅ AVR triple is avr-unknown-unknown
- ✅ MCS51 triple is mcs51-unknown-unknown
#### 16-bit Triples

- ✅ MSP430 triple is msp430-none-elf
#### 32-bit Triples

- ✅ x86 baremetal triple is i686-unknown-none
- ✅ ARM baremetal triple is thumbv7m-none-eabi
- ✅ RISC-V 32 baremetal triple is riscv32gc-unknown-none-elf
#### 64-bit Triples

- ✅ x86_64 baremetal triple is x86_64-unknown-none
- ✅ AArch64 baremetal triple is aarch64-unknown-none
- ✅ RISC-V 64 baremetal triple is riscv64gc-unknown-none-elf
### Target Configuration
_Verify target configuration for resource-limited devices._

#### 8-bit Configuration

- ✅ AVR has 256 byte default stack
- ✅ 8-bit has 1-byte heap alignment
- ✅ 8-bit has 0 tag bits
#### 16-bit Configuration

- ✅ MSP430 has 512 byte default stack
- ✅ 16-bit has 2-byte heap alignment
#### 32-bit Configuration

- ✅ 32-bit has 4-byte heap alignment
- ✅ 32-bit has 2 tag bits
#### 64-bit Configuration

- ✅ 64-bit has 8-byte heap alignment
- ✅ 64-bit has 3 tag bits
### FPU Availability
_Verify hardware FPU detection._

- ✅ AVR has no FPU
- ✅ MCS51 has no FPU
- ✅ MSP430 has no FPU
- ✅ ARM Cortex-M0/M3 has no FPU
- ✅ x86 has FPU
- ✅ x86_64 has FPU
- ✅ AArch64 has FPU

