# Multi-Architecture Support

Tests multi-architecture support across 8-bit, 16-bit, 32-bit, and 64-bit targets including AVR, MCS51, MSP430, x86, ARM, RISC-V, x86_64, and AArch64. Validates architecture properties (pointer size, stack alignment, FPU, endianness), target triple generation for bare-metal and hosted environments, and TargetConfig generation for each bit-width class.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ARCH-002 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/architecture_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/architecture/result.json` |

## Scenarios

- AVR has correct properties
- MCS51 has correct properties
- AVR parses from string
- MSP430 has correct properties
- MSP430 parses from string
- x86 has correct properties
- ARM has correct properties
- RISC-V 32 has correct properties
- x86_64 has correct properties
- AArch64 has correct properties
- RISC-V 64 has correct properties
- 8-bit and 16-bit use 16-bit pointers
- 32-bit uses 32-bit pointers
- 64-bit uses 64-bit pointers
- PointerSize returns correct byte count
- generates correct bare-metal triples
- generates correct hosted triples
- configures 8-bit correctly
- configures 16-bit correctly
- configures 32-bit correctly
- configures 64-bit correctly
- is_8bit returns true for 8-bit
- is_16bit returns true for 16-bit
- is_32bit returns true for 32-bit
- is_64bit returns true for 64-bit
- most architectures are little-endian
- MCS51 is big-endian
