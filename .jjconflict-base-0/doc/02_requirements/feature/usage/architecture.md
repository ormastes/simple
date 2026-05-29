# architecture
*Source:* `test/feature/usage/architecture_spec.spl`

## Feature: Target Architecture

## Feature: 8-bit Architectures

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | AVR has correct properties | pass |
| 2 | MCS51 has correct properties | pass |

**Example:** AVR has correct properties
    Given val avr = TargetArch.AVR
    Then  expect(avr.bits()).to_equal(8)
    Then  expect(avr.pointer_bytes()).to_equal(2)
    Then  expect(avr.stack_align()).to_equal(1)
    Then  expect(avr.max_atomic_width()).to_equal(8)
    Then  expect(avr.has_fpu()).to_equal(false)
    Then  expect(avr.is_harvard()).to_equal(true)
    Then  expect(avr.endianness()).to_equal(Endian.Little)

**Example:** MCS51 has correct properties
    Given val mcs51 = TargetArch.MCS51
    Then  expect(mcs51.bits()).to_equal(8)
    Then  expect(mcs51.pointer_bytes()).to_equal(2)
    Then  expect(mcs51.stack_align()).to_equal(1)
    Then  expect(mcs51.has_fpu()).to_equal(false)
    Then  expect(mcs51.is_harvard()).to_equal(true)
    Then  expect(mcs51.endianness()).to_equal(Endian.Big)
    Given val parsed = TargetArch__parse("avr")
    Then  expect(parsed.?).to_equal(true)
    Then  expect(parsed.unwrap()).to_equal(TargetArch.AVR)
    Given val parsed2 = TargetArch__parse("atmega")
    Then  expect(parsed2.?).to_equal(true)
    Then  expect(parsed2.unwrap()).to_equal(TargetArch.AVR)

## Feature: 16-bit Architectures

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | MSP430 has correct properties | pass |

**Example:** MSP430 has correct properties
    Given val msp = TargetArch.MSP430
    Then  expect(msp.bits()).to_equal(16)
    Then  expect(msp.pointer_bytes()).to_equal(2)
    Then  expect(msp.stack_align()).to_equal(2)
    Then  expect(msp.max_atomic_width()).to_equal(16)
    Then  expect(msp.has_fpu()).to_equal(false)
    Then  expect(msp.is_harvard()).to_equal(false)
    Then  expect(msp.endianness()).to_equal(Endian.Little)
    Given val parsed = TargetArch__parse("msp430")
    Then  expect(parsed.?).to_equal(true)
    Then  expect(parsed.unwrap()).to_equal(TargetArch.MSP430)

## Feature: 32-bit Architectures

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | x86 has correct properties | pass |
| 2 | ARM has correct properties | pass |
| 3 | RISC-V 32 has correct properties | pass |

**Example:** x86 has correct properties
    Given val x86 = TargetArch.X86
    Then  expect(x86.bits()).to_equal(32)
    Then  expect(x86.pointer_bytes()).to_equal(4)
    Then  expect(x86.stack_align()).to_equal(4)
    Then  expect(x86.max_atomic_width()).to_equal(64)
    Then  expect(x86.has_fpu()).to_equal(true)
    Then  expect(x86.is_harvard()).to_equal(false)

**Example:** ARM has correct properties
    Given val arm = TargetArch.Arm
    Then  expect(arm.bits()).to_equal(32)
    Then  expect(arm.pointer_bytes()).to_equal(4)
    Then  expect(arm.stack_align()).to_equal(4)
    Then  expect(arm.has_fpu()).to_equal(false)  # Cortex-M0/M3

**Example:** RISC-V 32 has correct properties
    Given val rv32 = TargetArch.Riscv32
    Then  expect(rv32.bits()).to_equal(32)
    Then  expect(rv32.pointer_bytes()).to_equal(4)

## Feature: 64-bit Architectures

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | x86_64 has correct properties | pass |
| 2 | AArch64 has correct properties | pass |
| 3 | RISC-V 64 has correct properties | pass |

**Example:** x86_64 has correct properties
    Given val x64 = TargetArch.X86_64
    Then  expect(x64.bits()).to_equal(64)
    Then  expect(x64.pointer_bytes()).to_equal(8)
    Then  expect(x64.stack_align()).to_equal(16)
    Then  expect(x64.max_atomic_width()).to_equal(128)
    Then  expect(x64.has_fpu()).to_equal(true)

**Example:** AArch64 has correct properties
    Given val arm64 = TargetArch.Aarch64
    Then  expect(arm64.bits()).to_equal(64)
    Then  expect(arm64.pointer_bytes()).to_equal(8)
    Then  expect(arm64.stack_align()).to_equal(16)

**Example:** RISC-V 64 has correct properties
    Given val rv64 = TargetArch.Riscv64
    Then  expect(rv64.bits()).to_equal(64)
    Then  expect(rv64.pointer_bytes()).to_equal(8)

## Feature: Pointer Size

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | 8-bit and 16-bit use 16-bit pointers | pass |
| 2 | 32-bit uses 32-bit pointers | pass |
| 3 | 64-bit uses 64-bit pointers | pass |
| 4 | PointerSize returns correct byte count | pass |

**Example:** 8-bit and 16-bit use 16-bit pointers
    Then  expect(TargetArch.AVR__pointer_size()).to_equal(PointerSize.Bits16)
    Then  expect(TargetArch.MCS51__pointer_size()).to_equal(PointerSize.Bits16)
    Then  expect(TargetArch.MSP430__pointer_size()).to_equal(PointerSize.Bits16)

**Example:** 32-bit uses 32-bit pointers
    Then  expect(TargetArch.X86__pointer_size()).to_equal(PointerSize.Bits32)
    Then  expect(TargetArch.Arm__pointer_size()).to_equal(PointerSize.Bits32)
    Then  expect(TargetArch.Riscv32__pointer_size()).to_equal(PointerSize.Bits32)

**Example:** 64-bit uses 64-bit pointers
    Then  expect(TargetArch.X86_64__pointer_size()).to_equal(PointerSize.Bits64)
    Then  expect(TargetArch.Aarch64__pointer_size()).to_equal(PointerSize.Bits64)
    Then  expect(TargetArch.Riscv64__pointer_size()).to_equal(PointerSize.Bits64)

**Example:** PointerSize returns correct byte count
    Then  expect(PointerSize.Bits16__bytes()).to_equal(2)
    Then  expect(PointerSize.Bits32__bytes()).to_equal(4)
    Then  expect(PointerSize.Bits64__bytes()).to_equal(8)

## Feature: Target Triple

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates correct bare-metal triples | pass |
| 2 | generates correct hosted triples | pass |

**Example:** generates correct bare-metal triples
    Then  expect(TargetArch.AVR__triple_str_baremetal()).to_equal("avr-unknown-unknown")
    Then  expect(TargetArch.MSP430__triple_str_baremetal()).to_equal("msp430-none-elf")
    Then  expect(TargetArch.X86__triple_str_baremetal()).to_equal("i686-unknown-none")
    Then  expect(TargetArch.Arm__triple_str_baremetal()).to_equal("thumbv7m-none-eabi")
    Then  expect(TargetArch.X86_64__triple_str_baremetal()).to_equal("x86_64-unknown-none")

**Example:** generates correct hosted triples
    Then  expect(TargetArch.X86__triple_str()).to_equal("i686-unknown-linux-gnu")
    Then  expect(TargetArch.X86_64__triple_str()).to_equal("x86_64-unknown-linux-gnu")
    Then  expect(TargetArch.Arm__triple_str()).to_equal("armv7-unknown-linux-gnueabihf")

## Feature: Target Config

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | configures 8-bit correctly | pass |
| 2 | configures 16-bit correctly | pass |
| 3 | configures 32-bit correctly | pass |
| 4 | configures 64-bit correctly | pass |

**Example:** configures 8-bit correctly
    Given val config = TargetConfig__for_arch(TargetArch.AVR)
    Then  expect(config.pointer_bytes).to_equal(2)
    Then  expect(config.value_bytes).to_equal(2)
    Then  expect(config.tag_bits).to_equal(0)
    Then  expect(config.heap_align).to_equal(1)
    Then  expect(config.default_stack_size).to_equal(256)

**Example:** configures 16-bit correctly
    Given val config = TargetConfig__for_arch(TargetArch.MSP430)
    Then  expect(config.pointer_bytes).to_equal(2)
    Then  expect(config.value_bytes).to_equal(2)
    Then  expect(config.tag_bits).to_equal(1)
    Then  expect(config.heap_align).to_equal(2)
    Then  expect(config.default_stack_size).to_equal(512)

**Example:** configures 32-bit correctly
    Given val config = TargetConfig__for_arch(TargetArch.X86)
    Then  expect(config.pointer_bytes).to_equal(4)
    Then  expect(config.value_bytes).to_equal(8)
    Then  expect(config.tag_bits).to_equal(2)
    Then  expect(config.heap_align).to_equal(4)

**Example:** configures 64-bit correctly
    Given val config = TargetConfig__for_arch(TargetArch.X86_64)
    Then  expect(config.pointer_bytes).to_equal(8)
    Then  expect(config.value_bytes).to_equal(8)
    Then  expect(config.tag_bits).to_equal(3)
    Then  expect(config.heap_align).to_equal(8)

## Feature: Architecture Bit Width Helpers

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | is_8bit returns true for 8-bit | pass |
| 2 | is_16bit returns true for 16-bit | pass |
| 3 | is_32bit returns true for 32-bit | pass |
| 4 | is_64bit returns true for 64-bit | pass |

**Example:** is_8bit returns true for 8-bit
    Then  expect(TargetArch.AVR__is_8bit()).to_equal(true)
    Then  expect(TargetArch.MCS51__is_8bit()).to_equal(true)
    Then  expect(TargetArch.X86__is_8bit()).to_equal(false)

**Example:** is_16bit returns true for 16-bit
    Then  expect(TargetArch.MSP430__is_16bit()).to_equal(true)
    Then  expect(TargetArch.AVR__is_16bit()).to_equal(false)

**Example:** is_32bit returns true for 32-bit
    Then  expect(TargetArch.X86__is_32bit()).to_equal(true)
    Then  expect(TargetArch.Arm__is_32bit()).to_equal(true)
    Then  expect(TargetArch.X86_64__is_32bit()).to_equal(false)

**Example:** is_64bit returns true for 64-bit
    Then  expect(TargetArch.X86_64__is_64bit()).to_equal(true)
    Then  expect(TargetArch.Aarch64__is_64bit()).to_equal(true)
    Then  expect(TargetArch.X86__is_64bit()).to_equal(false)

## Feature: Endianness

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | most architectures are little-endian | pass |
| 2 | MCS51 is big-endian | pass |

**Example:** most architectures are little-endian
    Then  expect(TargetArch.AVR__endianness()).to_equal(Endian.Little)
    Then  expect(TargetArch.MSP430__endianness()).to_equal(Endian.Little)
    Then  expect(TargetArch.X86__endianness()).to_equal(Endian.Little)
    Then  expect(TargetArch.X86_64__endianness()).to_equal(Endian.Little)

**Example:** MCS51 is big-endian
    Then  expect(TargetArch.MCS51__endianness()).to_equal(Endian.Big)


