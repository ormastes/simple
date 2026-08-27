# Target Architecture Specification

> Multi-architecture support for bare-metal development including:

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
| Source | `test/feature/usage/target_arch_spec.spl` |
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

#### AVR has 8-bit native word

- AVR has 8-bit native word
   - Expected: AVR_BITS equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AVR has 8-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# ATmega/ATtiny are 8-bit processors.
val AVR_BITS = 8
expect(AVR_BITS).to_equal(8)  # oracle: AVR_BITS must equal 8 — authoritative contract constant
```

</details>

#### MCS51 has 8-bit native word

- MCS51 has 8-bit native word
   - Expected: MCS51_BITS equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MCS51 has 8-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# Intel 8051 family are 8-bit processors.
val MCS51_BITS = 8
expect(MCS51_BITS).to_equal(8)  # oracle: MCS51_BITS must equal 8 — authoritative contract constant
```

</details>

#### 8-bit architectures use 16-bit pointers

- 8-bit architectures use 16-bit pointers
   - Expected: POINTER_BYTES_8BIT equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("8-bit architectures use 16-bit pointers")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# For >256 byte address space.
val POINTER_BYTES_8BIT = 2
expect(POINTER_BYTES_8BIT).to_equal(2)  # oracle: POINTER_BYTES_8BIT must equal 2 — authoritative contract constant
```

</details>

#### 16-bit Architectures

#### MSP430 has 16-bit native word

- MSP430 has 16-bit native word
   - Expected: MSP430_BITS equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MSP430 has 16-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MSP430_BITS = 16
expect(MSP430_BITS).to_equal(16)  # oracle: MSP430_BITS must equal 16 — authoritative contract constant
```

</details>

#### 16-bit architectures use 16-bit pointers

- 16-bit architectures use 16-bit pointers
   - Expected: POINTER_BYTES_16BIT equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("16-bit architectures use 16-bit pointers")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val POINTER_BYTES_16BIT = 2
expect(POINTER_BYTES_16BIT).to_equal(2)  # oracle: POINTER_BYTES_16BIT must equal 2 — authoritative contract constant
```

</details>

#### 32-bit Architectures

#### x86 has 32-bit native word

- x86 has 32-bit native word
   - Expected: X86_BITS equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86 has 32-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_BITS = 32
expect(X86_BITS).to_equal(32)  # oracle: X86_BITS must equal 32 — authoritative contract constant
```

</details>

#### ARM Cortex-M has 32-bit native word

- ARM Cortex-M has 32-bit native word
   - Expected: ARM_BITS equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ARM Cortex-M has 32-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val ARM_BITS = 32
expect(ARM_BITS).to_equal(32)  # oracle: ARM_BITS must equal 32 — authoritative contract constant
```

</details>

#### RISC-V 32 has 32-bit native word

- RISC-V 32 has 32-bit native word
   - Expected: RISCV32_BITS equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("RISC-V 32 has 32-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val RISCV32_BITS = 32
expect(RISCV32_BITS).to_equal(32)  # oracle: RISCV32_BITS must equal 32 — authoritative contract constant
```

</details>

#### 32-bit architectures use 32-bit pointers

- 32-bit architectures use 32-bit pointers
   - Expected: POINTER_BYTES_32BIT equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("32-bit architectures use 32-bit pointers")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val POINTER_BYTES_32BIT = 4
expect(POINTER_BYTES_32BIT).to_equal(4)  # oracle: POINTER_BYTES_32BIT must equal 4 — authoritative contract constant
```

</details>

#### 64-bit Architectures

#### x86_64 has 64-bit native word

- x86_64 has 64-bit native word
   - Expected: X86_64_BITS equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86_64 has 64-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_64_BITS = 64
expect(X86_64_BITS).to_equal(64)  # oracle: X86_64_BITS must equal 64 — authoritative contract constant
```

</details>

#### AArch64 has 64-bit native word

- AArch64 has 64-bit native word
   - Expected: AARCH64_BITS equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AArch64 has 64-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AARCH64_BITS = 64
expect(AARCH64_BITS).to_equal(64)  # oracle: AARCH64_BITS must equal 64 — authoritative contract constant
```

</details>

#### RISC-V 64 has 64-bit native word

- RISC-V 64 has 64-bit native word
   - Expected: RISCV64_BITS equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("RISC-V 64 has 64-bit native word")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val RISCV64_BITS = 64
expect(RISCV64_BITS).to_equal(64)  # oracle: RISCV64_BITS must equal 64 — authoritative contract constant
```

</details>

#### 64-bit architectures use 64-bit pointers

- 64-bit architectures use 64-bit pointers
   - Expected: POINTER_BYTES_64BIT equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("64-bit architectures use 64-bit pointers")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val POINTER_BYTES_64BIT = 8
expect(POINTER_BYTES_64BIT).to_equal(8)  # oracle: POINTER_BYTES_64BIT must equal 8 — authoritative contract constant
```

</details>

### Stack Alignment

#### 8-bit architectures have 1-byte stack alignment

- 8-bit architectures have 1-byte stack alignment
   - Expected: AVR_STACK_ALIGN equals `1`
   - Expected: MCS51_STACK_ALIGN equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("8-bit architectures have 1-byte stack alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AVR_STACK_ALIGN = 1
val MCS51_STACK_ALIGN = 1
expect(AVR_STACK_ALIGN).to_equal(1)  # oracle: AVR_STACK_ALIGN must equal 1 — authoritative contract constant
expect(MCS51_STACK_ALIGN).to_equal(1)  # oracle: MCS51_STACK_ALIGN must equal 1 — authoritative contract constant
```

</details>

#### 16-bit architectures have 2-byte stack alignment

- 16-bit architectures have 2-byte stack alignment
   - Expected: MSP430_STACK_ALIGN equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("16-bit architectures have 2-byte stack alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MSP430_STACK_ALIGN = 2
expect(MSP430_STACK_ALIGN).to_equal(2)  # oracle: MSP430_STACK_ALIGN must equal 2 — authoritative contract constant
```

</details>

#### 32-bit x86 has 4-byte stack alignment

- 32-bit x86 has 4-byte stack alignment
   - Expected: X86_STACK_ALIGN equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("32-bit x86 has 4-byte stack alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_STACK_ALIGN = 4
expect(X86_STACK_ALIGN).to_equal(4)  # oracle: X86_STACK_ALIGN must equal 4 — authoritative contract constant
```

</details>

#### 64-bit x86_64 has 16-byte stack alignment

- 64-bit x86_64 has 16-byte stack alignment
   - Expected: X86_64_STACK_ALIGN equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("64-bit x86_64 has 16-byte stack alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# SSE requires 16-byte alignment.
val X86_64_STACK_ALIGN = 16
expect(X86_64_STACK_ALIGN).to_equal(16)  # oracle: X86_64_STACK_ALIGN must equal 16 — authoritative contract constant
```

</details>

#### AArch64 has 16-byte stack alignment

- AArch64 has 16-byte stack alignment
   - Expected: AARCH64_STACK_ALIGN equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AArch64 has 16-byte stack alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AARCH64_STACK_ALIGN = 16
expect(AARCH64_STACK_ALIGN).to_equal(16)  # oracle: AARCH64_STACK_ALIGN must equal 16 — authoritative contract constant
```

</details>

### Maximum Atomic Width

#### 8-bit architectures support 8-bit atomics

- 8-bit architectures support 8-bit atomics
   - Expected: AVR_MAX_ATOMIC equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("8-bit architectures support 8-bit atomics")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AVR_MAX_ATOMIC = 8
expect(AVR_MAX_ATOMIC).to_equal(8)  # oracle: AVR_MAX_ATOMIC must equal 8 — authoritative contract constant
```

</details>

#### 16-bit architectures support 16-bit atomics

- 16-bit architectures support 16-bit atomics
   - Expected: MSP430_MAX_ATOMIC equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("16-bit architectures support 16-bit atomics")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MSP430_MAX_ATOMIC = 16
expect(MSP430_MAX_ATOMIC).to_equal(16)  # oracle: MSP430_MAX_ATOMIC must equal 16 — authoritative contract constant
```

</details>

#### x86 supports 64-bit atomics via cmpxchg8b

- x86 supports 64-bit atomics via cmpxchg8b
   - Expected: X86_MAX_ATOMIC equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86 supports 64-bit atomics via cmpxchg8b")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_MAX_ATOMIC = 64
expect(X86_MAX_ATOMIC).to_equal(64)  # oracle: X86_MAX_ATOMIC must equal 64 — authoritative contract constant
```

</details>

#### x86_64 supports 128-bit atomics via cmpxchg16b

- x86_64 supports 128-bit atomics via cmpxchg16b
   - Expected: X86_64_MAX_ATOMIC equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86_64 supports 128-bit atomics via cmpxchg16b")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_64_MAX_ATOMIC = 128
expect(X86_64_MAX_ATOMIC).to_equal(128)  # oracle: X86_64_MAX_ATOMIC must equal 128 — authoritative contract constant
```

</details>

### Harvard Architecture Detection

#### AVR is Harvard architecture

- AVR is Harvard architecture
   - Expected: AVR_IS_HARVARD is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AVR is Harvard architecture")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# AVR has separate program (flash) and data (SRAM) memory.
val AVR_IS_HARVARD = true
expect(AVR_IS_HARVARD).to_equal(true)
```

</details>

#### MCS51 is Harvard architecture

- MCS51 is Harvard architecture
   - Expected: MCS51_IS_HARVARD is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MCS51 is Harvard architecture")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# 8051 has separate CODE, DATA, XDATA spaces.
val MCS51_IS_HARVARD = true
expect(MCS51_IS_HARVARD).to_equal(true)
```

</details>

#### x86 is von Neumann architecture

- x86 is von Neumann architecture
   - Expected: X86_IS_HARVARD is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86 is von Neumann architecture")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# x86 has unified address space.
val X86_IS_HARVARD = false
expect(X86_IS_HARVARD).to_equal(false)
```

</details>

#### ARM Cortex-M is von Neumann architecture

- ARM Cortex-M is von Neumann architecture
   - Expected: ARM_IS_HARVARD is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ARM Cortex-M is von Neumann architecture")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val ARM_IS_HARVARD = false
expect(ARM_IS_HARVARD).to_equal(false)
```

</details>

### Endianness

#### Little-Endian Architectures

#### AVR is little-endian

- AVR is little-endian
   - Expected: AVR_LITTLE_ENDIAN is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AVR is little-endian")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AVR_LITTLE_ENDIAN = true
expect(AVR_LITTLE_ENDIAN).to_equal(true)
```

</details>

#### x86 is little-endian

- x86 is little-endian
   - Expected: X86_LITTLE_ENDIAN is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86 is little-endian")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_LITTLE_ENDIAN = true
expect(X86_LITTLE_ENDIAN).to_equal(true)
```

</details>

#### x86_64 is little-endian

- x86_64 is little-endian
   - Expected: X86_64_LITTLE_ENDIAN is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86_64 is little-endian")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_64_LITTLE_ENDIAN = true
expect(X86_64_LITTLE_ENDIAN).to_equal(true)
```

</details>

#### MSP430 is little-endian

- MSP430 is little-endian
   - Expected: MSP430_LITTLE_ENDIAN is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MSP430 is little-endian")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MSP430_LITTLE_ENDIAN = true
expect(MSP430_LITTLE_ENDIAN).to_equal(true)
```

</details>

#### Big-Endian Architectures

#### MCS51 is big-endian

- MCS51 is big-endian
   - Expected: MCS51_BIG_ENDIAN is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MCS51 is big-endian")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# 8051 stores MSB first.
val MCS51_BIG_ENDIAN = true
expect(MCS51_BIG_ENDIAN).to_equal(true)
```

</details>

### Target Triple Generation

#### 8-bit Triples

#### AVR triple is avr-unknown-unknown

- AVR triple is avr-unknown-unknown
   - Expected: AVR_TRIPLE equals `avr-unknown-unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AVR triple is avr-unknown-unknown")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AVR_TRIPLE = "avr-unknown-unknown"
expect(AVR_TRIPLE).to_equal("avr-unknown-unknown")
```

</details>

#### MCS51 triple is mcs51-unknown-unknown

- MCS51 triple is mcs51-unknown-unknown
   - Expected: MCS51_TRIPLE equals `mcs51-unknown-unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MCS51 triple is mcs51-unknown-unknown")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MCS51_TRIPLE = "mcs51-unknown-unknown"
expect(MCS51_TRIPLE).to_equal("mcs51-unknown-unknown")
```

</details>

#### 16-bit Triples

#### MSP430 triple is msp430-none-elf

- MSP430 triple is msp430-none-elf
   - Expected: MSP430_TRIPLE equals `msp430-none-elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MSP430 triple is msp430-none-elf")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MSP430_TRIPLE = "msp430-none-elf"
expect(MSP430_TRIPLE).to_equal("msp430-none-elf")
```

</details>

#### 32-bit Triples

#### x86 baremetal triple is i686-unknown-none

- x86 baremetal triple is i686-unknown-none
   - Expected: X86_TRIPLE equals `i686-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86 baremetal triple is i686-unknown-none")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_TRIPLE = "i686-unknown-none"
expect(X86_TRIPLE).to_equal("i686-unknown-none")
```

</details>

#### ARM baremetal triple is thumbv7m-none-eabi

- ARM baremetal triple is thumbv7m-none-eabi
   - Expected: ARM_TRIPLE equals `thumbv7m-none-eabi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ARM baremetal triple is thumbv7m-none-eabi")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val ARM_TRIPLE = "thumbv7m-none-eabi"
expect(ARM_TRIPLE).to_equal("thumbv7m-none-eabi")
```

</details>

#### RISC-V 32 baremetal triple is riscv32gc-unknown-none-elf

- RISC-V 32 baremetal triple is riscv32gc-unknown-none-elf
   - Expected: RISCV32_TRIPLE equals `riscv32gc-unknown-none-elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("RISC-V 32 baremetal triple is riscv32gc-unknown-none-elf")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val RISCV32_TRIPLE = "riscv32gc-unknown-none-elf"
expect(RISCV32_TRIPLE).to_equal("riscv32gc-unknown-none-elf")
```

</details>

#### 64-bit Triples

#### x86_64 baremetal triple is x86_64-unknown-none

- x86_64 baremetal triple is x86_64-unknown-none
   - Expected: X86_64_TRIPLE equals `x86_64-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86_64 baremetal triple is x86_64-unknown-none")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_64_TRIPLE = "x86_64-unknown-none"
expect(X86_64_TRIPLE).to_equal("x86_64-unknown-none")
```

</details>

#### AArch64 baremetal triple is aarch64-unknown-none

- AArch64 baremetal triple is aarch64-unknown-none
   - Expected: AARCH64_TRIPLE equals `aarch64-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AArch64 baremetal triple is aarch64-unknown-none")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AARCH64_TRIPLE = "aarch64-unknown-none"
expect(AARCH64_TRIPLE).to_equal("aarch64-unknown-none")
```

</details>

#### RISC-V 64 baremetal triple is riscv64gc-unknown-none-elf

- RISC-V 64 baremetal triple is riscv64gc-unknown-none-elf
   - Expected: RISCV64_TRIPLE equals `riscv64gc-unknown-none-elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("RISC-V 64 baremetal triple is riscv64gc-unknown-none-elf")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val RISCV64_TRIPLE = "riscv64gc-unknown-none-elf"
expect(RISCV64_TRIPLE).to_equal("riscv64gc-unknown-none-elf")
```

</details>

### Target Configuration

#### 8-bit Configuration

#### AVR has 256 byte default stack

- AVR has 256 byte default stack
   - Expected: AVR_DEFAULT_STACK equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AVR has 256 byte default stack")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AVR_DEFAULT_STACK = 256
expect(AVR_DEFAULT_STACK).to_equal(256)  # oracle: AVR_DEFAULT_STACK must equal 256 — authoritative contract constant
```

</details>

#### 8-bit has 1-byte heap alignment

- 8-bit has 1-byte heap alignment
   - Expected: HEAP_ALIGN_8BIT equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("8-bit has 1-byte heap alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val HEAP_ALIGN_8BIT = 1
expect(HEAP_ALIGN_8BIT).to_equal(1)  # oracle: HEAP_ALIGN_8BIT must equal 1 — authoritative contract constant
```

</details>

#### 8-bit has 0 tag bits

- 8-bit has 0 tag bits
   - Expected: TAG_BITS_8BIT equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("8-bit has 0 tag bits")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# No room for tagged pointers.
val TAG_BITS_8BIT = 0
expect(TAG_BITS_8BIT).to_equal(0)  # oracle: TAG_BITS_8BIT must equal 0 — authoritative contract constant
```

</details>

#### 16-bit Configuration

#### MSP430 has 512 byte default stack

- MSP430 has 512 byte default stack
   - Expected: MSP430_DEFAULT_STACK equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MSP430 has 512 byte default stack")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MSP430_DEFAULT_STACK = 512
expect(MSP430_DEFAULT_STACK).to_equal(512)  # oracle: MSP430_DEFAULT_STACK must equal 512 — authoritative contract constant
```

</details>

#### 16-bit has 2-byte heap alignment

- 16-bit has 2-byte heap alignment
   - Expected: HEAP_ALIGN_16BIT equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("16-bit has 2-byte heap alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val HEAP_ALIGN_16BIT = 2
expect(HEAP_ALIGN_16BIT).to_equal(2)  # oracle: HEAP_ALIGN_16BIT must equal 2 — authoritative contract constant
```

</details>

#### 32-bit Configuration

#### 32-bit has 4-byte heap alignment

- 32-bit has 4-byte heap alignment
   - Expected: HEAP_ALIGN_32BIT equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("32-bit has 4-byte heap alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val HEAP_ALIGN_32BIT = 4
expect(HEAP_ALIGN_32BIT).to_equal(4)  # oracle: HEAP_ALIGN_32BIT must equal 4 — authoritative contract constant
```

</details>

#### 32-bit has 2 tag bits

- 32-bit has 2 tag bits
   - Expected: TAG_BITS_32BIT equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("32-bit has 2 tag bits")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val TAG_BITS_32BIT = 2
expect(TAG_BITS_32BIT).to_equal(2)  # oracle: TAG_BITS_32BIT must equal 2 — authoritative contract constant
```

</details>

#### 64-bit Configuration

#### 64-bit has 8-byte heap alignment

- 64-bit has 8-byte heap alignment
   - Expected: HEAP_ALIGN_64BIT equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("64-bit has 8-byte heap alignment")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val HEAP_ALIGN_64BIT = 8
expect(HEAP_ALIGN_64BIT).to_equal(8)  # oracle: HEAP_ALIGN_64BIT must equal 8 — authoritative contract constant
```

</details>

#### 64-bit has 3 tag bits

- 64-bit has 3 tag bits
   - Expected: TAG_BITS_64BIT equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("64-bit has 3 tag bits")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# 8-byte aligned pointers allow 3 low bits.
val TAG_BITS_64BIT = 3
expect(TAG_BITS_64BIT).to_equal(3)  # oracle: TAG_BITS_64BIT must equal 3 — authoritative contract constant
```

</details>

### FPU Availability

#### AVR has no FPU

- AVR has no FPU
   - Expected: AVR_HAS_FPU is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AVR has no FPU")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val AVR_HAS_FPU = false
expect(AVR_HAS_FPU).to_equal(false)
```

</details>

#### MCS51 has no FPU

- MCS51 has no FPU
   - Expected: MCS51_HAS_FPU is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MCS51 has no FPU")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MCS51_HAS_FPU = false
expect(MCS51_HAS_FPU).to_equal(false)
```

</details>

#### MSP430 has no FPU

- MSP430 has no FPU
   - Expected: MSP430_HAS_FPU is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("MSP430 has no FPU")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val MSP430_HAS_FPU = false
expect(MSP430_HAS_FPU).to_equal(false)
```

</details>

#### ARM Cortex-M0/M3 has no FPU

- ARM Cortex-M0/M3 has no FPU
   - Expected: ARM_HAS_FPU is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ARM Cortex-M0/M3 has no FPU")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# M4F has FPU but requires feature flag.
val ARM_HAS_FPU = false
expect(ARM_HAS_FPU).to_equal(false)
```

</details>

#### x86 has FPU

- x86 has FPU
   - Expected: X86_HAS_FPU is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86 has FPU")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_HAS_FPU = true
expect(X86_HAS_FPU).to_equal(true)
```

</details>

#### x86_64 has FPU

- x86_64 has FPU
   - Expected: X86_64_HAS_FPU is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86_64 has FPU")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val X86_64_HAS_FPU = true
expect(X86_64_HAS_FPU).to_equal(true)
```

</details>

#### AArch64 has FPU

- AArch64 has FPU
   - Expected: AARCH64_HAS_FPU is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("AArch64 has FPU")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c5e6129bdb93c030953ad9411fd124efafd071b6c1573fc49c156c715a18da4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c5e6129bdb93c030953ad9411fd124efafd071b6c1573fc49c156c715a18da4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c5e6129bdb93c030953ad9411fd124efafd071b6c1573fc49c156c715a18da4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/feature/usage/target_arch_spec.spl
mirror: doc/06_spec/feature/usage/target_arch_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/target_arch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/target_arch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
