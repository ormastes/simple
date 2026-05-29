# Multi-Architecture Support

**Feature ID:** #ARCH-002 | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/usage/architecture_spec.spl`_

---

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
val config = TargetConfig__for_arch(TargetArch.X86_64)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 27 |

## Test Structure

### Target Architecture

### 8-bit Architectures

- ✅ AVR has correct properties
- ✅ MCS51 has correct properties
- ✅ AVR parses from string
### 16-bit Architectures

- ✅ MSP430 has correct properties
- ✅ MSP430 parses from string
### 32-bit Architectures

- ✅ x86 has correct properties
- ✅ ARM has correct properties
- ✅ RISC-V 32 has correct properties
### 64-bit Architectures

- ✅ x86_64 has correct properties
- ✅ AArch64 has correct properties
- ✅ RISC-V 64 has correct properties
### Pointer Size

- ✅ 8-bit and 16-bit use 16-bit pointers
- ✅ 32-bit uses 32-bit pointers
- ✅ 64-bit uses 64-bit pointers
- ✅ PointerSize returns correct byte count
### Target Triple

- ✅ generates correct bare-metal triples
- ✅ generates correct hosted triples
### Target Config

- ✅ configures 8-bit correctly
- ✅ configures 16-bit correctly
- ✅ configures 32-bit correctly
- ✅ configures 64-bit correctly
### Architecture Bit Width Helpers

- ✅ is_8bit returns true for 8-bit
- ✅ is_16bit returns true for 16-bit
- ✅ is_32bit returns true for 32-bit
- ✅ is_64bit returns true for 64-bit
### Endianness

- ✅ most architectures are little-endian
- ✅ MCS51 is big-endian

