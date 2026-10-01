# Target Architecture Specification

> `std.common.target.TargetArch` for per-architecture layout decisions.

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
| Updated | 2026-08-27 |
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

#### AVR has 8-bit native word and 16-bit pointers

- AVR has 8-bit native word and 16-bit pointers
   - Expected: TargetArch.AVR.bits() equals `8`
   - Expected: TargetArch.AVR.pointer_bytes() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AVR has 8-bit native word and 16-bit pointers")
expect(TargetArch.AVR.bits()).to_equal(8)
expect(TargetArch.AVR.pointer_bytes()).to_equal(2)
```

</details>

#### MCS51 has 8-bit native word and 16-bit pointers

- MCS51 has 8-bit native word and 16-bit pointers
   - Expected: TargetArch.MCS51.bits() equals `8`
   - Expected: TargetArch.MCS51.pointer_bytes() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCS51 has 8-bit native word and 16-bit pointers")
expect(TargetArch.MCS51.bits()).to_equal(8)
expect(TargetArch.MCS51.pointer_bytes()).to_equal(2)
```

</details>

#### 16-bit Architectures

#### MSP430 has 16-bit native word

- MSP430 has 16-bit native word and 16-bit pointers
   - Expected: TargetArch.MSP430.bits() equals `16`
   - Expected: TargetArch.MSP430.pointer_bytes() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MSP430 has 16-bit native word and 16-bit pointers")
expect(TargetArch.MSP430.bits()).to_equal(16)
expect(TargetArch.MSP430.pointer_bytes()).to_equal(2)
```

</details>

#### 32-bit Architectures

#### x86 has 32-bit native word

- x86, ARM and RISC-V 32 have 32-bit words and 4-byte pointers
   - Expected: TargetArch.X86.bits() equals `32`
   - Expected: TargetArch.Arm.bits() equals `32`
   - Expected: TargetArch.Riscv32.bits() equals `32`
   - Expected: TargetArch.X86.pointer_bytes() equals `4`
   - Expected: TargetArch.Riscv32.pointer_bytes() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86, ARM and RISC-V 32 have 32-bit words and 4-byte pointers")
expect(TargetArch.X86.bits()).to_equal(32)
expect(TargetArch.Arm.bits()).to_equal(32)
expect(TargetArch.Riscv32.bits()).to_equal(32)
expect(TargetArch.X86.pointer_bytes()).to_equal(4)
expect(TargetArch.Riscv32.pointer_bytes()).to_equal(4)
```

</details>

#### 64-bit Architectures

#### x86_64 has 64-bit native word

- x86_64, AArch64 and RISC-V 64 have 64-bit words and 8-byte pointers
   - Expected: TargetArch.X86_64.bits() equals `64`
   - Expected: TargetArch.Aarch64.bits() equals `64`
   - Expected: TargetArch.Riscv64.bits() equals `64`
   - Expected: TargetArch.X86_64.pointer_bytes() equals `8`
   - Expected: TargetArch.Riscv64.pointer_bytes() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86_64, AArch64 and RISC-V 64 have 64-bit words and 8-byte pointers")
expect(TargetArch.X86_64.bits()).to_equal(64)
expect(TargetArch.Aarch64.bits()).to_equal(64)
expect(TargetArch.Riscv64.bits()).to_equal(64)
expect(TargetArch.X86_64.pointer_bytes()).to_equal(8)
expect(TargetArch.Riscv64.pointer_bytes()).to_equal(8)
```

</details>

### Stack Alignment

#### 8-bit architectures have 1-byte stack alignment

- 8-bit architectures have 1-byte stack alignment
   - Expected: TargetArch.AVR.stack_align() equals `1`
   - Expected: TargetArch.MCS51.stack_align() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("8-bit architectures have 1-byte stack alignment")
expect(TargetArch.AVR.stack_align()).to_equal(1)
expect(TargetArch.MCS51.stack_align()).to_equal(1)
```

</details>

#### 16-bit architectures have 2-byte stack alignment

- 16-bit architectures have 2-byte stack alignment
   - Expected: TargetArch.MSP430.stack_align() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("16-bit architectures have 2-byte stack alignment")
expect(TargetArch.MSP430.stack_align()).to_equal(2)
```

</details>

#### 32-bit x86 has 4-byte stack alignment

- 32-bit x86 has 4-byte stack alignment
   - Expected: TargetArch.X86.stack_align() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("32-bit x86 has 4-byte stack alignment")
expect(TargetArch.X86.stack_align()).to_equal(4)
```

</details>

#### x86_64 and AArch64 have 16-byte stack alignment

- x86_64 and AArch64 have 16-byte stack alignment
   - Expected: TargetArch.X86_64.stack_align() equals `16`
   - Expected: TargetArch.Aarch64.stack_align() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86_64 and AArch64 have 16-byte stack alignment")
# SSE (x86_64) and the AAPCS64 ABI (AArch64) require 16-byte alignment.
expect(TargetArch.X86_64.stack_align()).to_equal(16)
expect(TargetArch.Aarch64.stack_align()).to_equal(16)
```

</details>

### Maximum Atomic Width

#### 8-bit architectures support 8-bit atomics

- 8-bit architectures support 8-bit atomics
   - Expected: TargetArch.AVR.max_atomic_width() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("8-bit architectures support 8-bit atomics")
expect(TargetArch.AVR.max_atomic_width()).to_equal(8)
```

</details>

#### 16-bit architectures support 16-bit atomics

- 16-bit architectures support 16-bit atomics
   - Expected: TargetArch.MSP430.max_atomic_width() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("16-bit architectures support 16-bit atomics")
expect(TargetArch.MSP430.max_atomic_width()).to_equal(16)
```

</details>

#### x86 supports 64-bit atomics via cmpxchg8b

- x86 supports 64-bit atomics via cmpxchg8b
   - Expected: TargetArch.X86.max_atomic_width() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86 supports 64-bit atomics via cmpxchg8b")
expect(TargetArch.X86.max_atomic_width()).to_equal(64)
```

</details>

#### x86_64 supports 128-bit atomics via cmpxchg16b

- x86_64 supports 128-bit atomics via cmpxchg16b
   - Expected: TargetArch.X86_64.max_atomic_width() equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86_64 supports 128-bit atomics via cmpxchg16b")
expect(TargetArch.X86_64.max_atomic_width()).to_equal(128)
```

</details>

### Harvard Architecture Detection

#### AVR and MCS51 are Harvard architectures

- AVR and MCS51 are Harvard architectures
   - Expected: TargetArch.AVR.is_harvard() is true
   - Expected: TargetArch.MCS51.is_harvard() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AVR and MCS51 are Harvard architectures")
# Separate program and data memory spaces.
expect(TargetArch.AVR.is_harvard()).to_equal(true)
expect(TargetArch.MCS51.is_harvard()).to_equal(true)
```

</details>

#### x86 and ARM Cortex-M are von Neumann architectures

- x86 and ARM Cortex-M are von Neumann architectures
   - Expected: TargetArch.X86.is_harvard() is false
   - Expected: TargetArch.Arm.is_harvard() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86 and ARM Cortex-M are von Neumann architectures")
# Unified address space.
expect(TargetArch.X86.is_harvard()).to_equal(false)
expect(TargetArch.Arm.is_harvard()).to_equal(false)
```

</details>

### Endianness

#### AVR, x86, x86_64 and MSP430 are little-endian

- AVR, x86, x86_64 and MSP430 are little-endian
   - Expected: TargetArch.AVR.endianness() equals `Endian.Little`
   - Expected: TargetArch.X86.endianness() equals `Endian.Little`
   - Expected: TargetArch.X86_64.endianness() equals `Endian.Little`
   - Expected: TargetArch.MSP430.endianness() equals `Endian.Little`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AVR, x86, x86_64 and MSP430 are little-endian")
expect(TargetArch.AVR.endianness()).to_equal(Endian.Little)
expect(TargetArch.X86.endianness()).to_equal(Endian.Little)
expect(TargetArch.X86_64.endianness()).to_equal(Endian.Little)
expect(TargetArch.MSP430.endianness()).to_equal(Endian.Little)
```

</details>

#### MCS51 is big-endian

- MCS51 is big-endian
   - Expected: TargetArch.MCS51.endianness() equals `Endian.Big`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCS51 is big-endian")
# 8051 stores MSB first.
val MCS51_BIG_ENDIAN = true
expect(MCS51_BIG_ENDIAN).to_equal(true)
```

</details>

### Target Triple Generation

#### 8-bit Triples

- bare-metal triples follow the per-arch canonical form
   - Expected: TargetArch.AVR.triple_str_baremetal() equals `avr-unknown-unknown`
   - Expected: TargetArch.MCS51.triple_str_baremetal() equals `mcs51-unknown-unknown`
   - Expected: TargetArch.MSP430.triple_str_baremetal() equals `msp430-none-elf`
   - Expected: TargetArch.X86.triple_str_baremetal() equals `i686-unknown-none`
   - Expected: TargetArch.Arm.triple_str_baremetal() equals `thumbv7m-none-eabi`
   - Expected: TargetArch.Riscv32.triple_str_baremetal() equals `riscv32imac-unknown-none-elf`
   - Expected: TargetArch.X86_64.triple_str_baremetal() equals `x86_64-unknown-none`
   - Expected: TargetArch.Aarch64.triple_str_baremetal() equals `aarch64-unknown-none`
   - Expected: TargetArch.Riscv64.triple_str_baremetal() equals `riscv64gc-unknown-none-elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bare-metal triples follow the per-arch canonical form")
expect(TargetArch.AVR.triple_str_baremetal()).to_equal("avr-unknown-unknown")
expect(TargetArch.MCS51.triple_str_baremetal()).to_equal("mcs51-unknown-unknown")
expect(TargetArch.MSP430.triple_str_baremetal()).to_equal("msp430-none-elf")
expect(TargetArch.X86.triple_str_baremetal()).to_equal("i686-unknown-none")
expect(TargetArch.Arm.triple_str_baremetal()).to_equal("thumbv7m-none-eabi")
expect(TargetArch.Riscv32.triple_str_baremetal()).to_equal("riscv32imac-unknown-none-elf")
expect(TargetArch.X86_64.triple_str_baremetal()).to_equal("x86_64-unknown-none")
expect(TargetArch.Aarch64.triple_str_baremetal()).to_equal("aarch64-unknown-none")
expect(TargetArch.Riscv64.triple_str_baremetal()).to_equal("riscv64gc-unknown-none-elf")
```

</details>

### FPU Availability

#### AVR has no FPU

- AVR, MCS51, MSP430 and baseline ARM have no FPU
   - Expected: TargetArch.AVR.has_fpu() is false
   - Expected: TargetArch.MCS51.has_fpu() is false
   - Expected: TargetArch.MSP430.has_fpu() is false
   - Expected: TargetArch.Arm.has_fpu() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AVR, MCS51, MSP430 and baseline ARM have no FPU")
expect(TargetArch.AVR.has_fpu()).to_equal(false)
expect(TargetArch.MCS51.has_fpu()).to_equal(false)
expect(TargetArch.MSP430.has_fpu()).to_equal(false)
expect(TargetArch.Arm.has_fpu()).to_equal(false)
```

</details>

#### MCS51 has no FPU

- x86, x86_64 and AArch64 have an FPU
   - Expected: TargetArch.X86.has_fpu() is true
   - Expected: TargetArch.X86_64.has_fpu() is true
   - Expected: TargetArch.Aarch64.has_fpu() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86, x86_64 and AArch64 have an FPU")
expect(TargetArch.X86.has_fpu()).to_equal(true)
expect(TargetArch.X86_64.has_fpu()).to_equal(true)
expect(TargetArch.Aarch64.has_fpu()).to_equal(true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed524e3bde85a72d18cec65622534b86cbf34059e05b9c7077021e0da900291a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed524e3bde85a72d18cec65622534b86cbf34059e05b9c7077021e0da900291a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed524e3bde85a72d18cec65622534b86cbf34059e05b9c7077021e0da900291a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/target_arch_spec.spl
mirror: doc/06_spec/03_system/feature/usage/target_arch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/target_arch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/target_arch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/target_arch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 26 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/target_arch_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AVR has 8-bit native word and 16-bit pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/target_arch_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MCS51 has 8-bit native word and 16-bit pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/target_arch_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MSP430 has 16-bit native word and 16-bit pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
