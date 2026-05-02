# Target Architecture Specification

Multi-architecture support for bare-metal development including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-ARCH-001 |
| Category | Bare-Metal / Architecture |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/feature/usage/target_arch_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/target_arch/result.json` |

## Scenarios

- AVR has 8-bit native word
- MCS51 has 8-bit native word
- 8-bit architectures use 16-bit pointers
- MSP430 has 16-bit native word
- 16-bit architectures use 16-bit pointers
- x86 has 32-bit native word
- ARM Cortex-M has 32-bit native word
- RISC-V 32 has 32-bit native word
- 32-bit architectures use 32-bit pointers
- x86_64 has 64-bit native word
- AArch64 has 64-bit native word
- RISC-V 64 has 64-bit native word
- 64-bit architectures use 64-bit pointers
- 8-bit architectures have 1-byte stack alignment
- 16-bit architectures have 2-byte stack alignment
- 32-bit x86 has 4-byte stack alignment
- 64-bit x86_64 has 16-byte stack alignment
- AArch64 has 16-byte stack alignment
- 8-bit architectures support 8-bit atomics
- 16-bit architectures support 16-bit atomics
- x86 supports 64-bit atomics via cmpxchg8b
- x86_64 supports 128-bit atomics via cmpxchg16b
- AVR is Harvard architecture
- MCS51 is Harvard architecture
- x86 is von Neumann architecture
- ARM Cortex-M is von Neumann architecture
- AVR is little-endian
- x86 is little-endian
- x86_64 is little-endian
- MSP430 is little-endian
- MCS51 is big-endian
- AVR triple is avr-unknown-unknown
- MCS51 triple is mcs51-unknown-unknown
- MSP430 triple is msp430-none-elf
- x86 baremetal triple is i686-unknown-none
- ARM baremetal triple is thumbv7m-none-eabi
- RISC-V 32 baremetal triple is riscv32gc-unknown-none-elf
- x86_64 baremetal triple is x86_64-unknown-none
- AArch64 baremetal triple is aarch64-unknown-none
- RISC-V 64 baremetal triple is riscv64gc-unknown-none-elf
- AVR has 256 byte default stack
- 8-bit has 1-byte heap alignment
- 8-bit has 0 tag bits
- MSP430 has 512 byte default stack
- 16-bit has 2-byte heap alignment
- 32-bit has 4-byte heap alignment
- 32-bit has 2 tag bits
- 64-bit has 8-byte heap alignment
- 64-bit has 3 tag bits
- AVR has no FPU
- MCS51 has no FPU
- MSP430 has no FPU
- ARM Cortex-M0/M3 has no FPU
- x86 has FPU
- x86_64 has FPU
- AArch64 has FPU
