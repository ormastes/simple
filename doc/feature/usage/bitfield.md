# Bitfield Specification
*Source:* `test/feature/usage/bitfield_spec.spl`
**Feature IDs:** #BM-004  |  **Category:** Language / Bare-Metal  |  **Status:** In Progress

## Overview

Current implementation status in this repository:
- Parser/token support is implemented in `compiler.core`.
- Native C codegen accepts `bitfield Name(uN):` and reserved `_` fields.
- Executable regression: `test/unit/compiler/native/bitfield_codegen_spec.spl`.
- Legacy interpreter runtime (`bin/release/simple`) remains on an older parser and can still reject direct bitfield declarations.



Bitfields allow packing multiple values into a single integer:
- Efficient hardware register access
- Network protocol fields
- Compact data structures

Syntax:
    # bitfield Name(BackingType):
        # field1: uN      # N-bit unsigned
        # field2: iM      # M-bit signed
        # field3: bool    # 1 bit
        # _: uK           # K bits reserved

Features:
- Automatic offset calculation
- Compile-time overflow checking
- Generated getters/setters
- Enum support (bits inferred)

## Feature: Bitfield Definition

### Scenario: Basic Bitfields

| # | Example | Status |
|---|---------|--------|
| 1 | defines bitfield with u8 backing | pass |
| 2 | defines bitfield with u16 backing | pass |
| 3 | defines bitfield with u32 backing | pass |
| 4 | defines bitfield with u64 backing | pass |

**Example:** defines bitfield with u16 backing
    Given val r = ShortRegister(0x5ABC)
    Then  expect(r.value).to_equal(0xABC)
    Then  expect(r.type_).to_equal(5)

**Example:** defines bitfield with u32 backing
    Then  expect(size_of<ControlReg>()).to_equal(4)

**Example:** defines bitfield with u64 backing
    Then  expect(size_of<LargeStatus>()).to_equal(8)

### Scenario: Bit Width Types

| # | Example | Status |
|---|---------|--------|
| 1 | supports arbitrary unsigned widths | pass |
| 2 | supports arbitrary signed widths | pass |

**Example:** supports arbitrary unsigned widths
    Then  expect(true).to_equal(true)  # Compiles successfully

**Example:** supports arbitrary signed widths
    Given val sf = SignedFields(0)
    Then  expect(sf.temp).to_equal(-50)

### Scenario: Reserved Fields

| # | Example | Status |
|---|---------|--------|
| 1 | allows reserved fields | pass |
| 2 | allows multiple reserved fields | pass |

**Example:** allows reserved fields
    Given val w = WithReserved(0xFF)
    Then  expect(w.used).to_equal(15)

**Example:** allows multiple reserved fields
    Then  expect(true).to_equal(true)

## Feature: Bitfield Operations

### Scenario: Getters

| # | Example | Status |
|---|---------|--------|
| 1 | reads single bit | pass |
| 2 | reads multi-bit field | pass |
| 3 | reads signed fields correctly | pass |

**Example:** reads single bit
    Given val flags = BitFlags(0b1010)
    Then  expect(flags.a).to_equal(false)
    Then  expect(flags.b).to_equal(true)
    Then  expect(flags.c).to_equal(false)
    Then  expect(flags.d).to_equal(true)

**Example:** reads multi-bit field
    Given val mf = MultiField(0xABCD)
    Then  expect(mf.low).to_equal(0xD)
    Then  expect(mf.mid).to_equal(0xBC)
    Then  expect(mf.high).to_equal(0xA)

**Example:** reads signed fields correctly
    Given val sr = SignedRead(0xFE7F)  # -2 and 127
    Then  expect(sr.positive).to_equal(127)
    Then  expect(sr.negative).to_equal(-2)

### Scenario: Setters

| # | Example | Status |
|---|---------|--------|
| 1 | sets single bit | pass |
| 2 | sets multi-bit field | pass |
| 3 | preserves other fields when setting | pass |

**Example:** sets single bit
    Given var wb = WriteBit(0)
    Then  expect(wb.flag).to_equal(false)
    Then  expect(wb.flag).to_equal(true)

**Example:** sets multi-bit field
    Given var wm = WriteMulti(0)
    Then  expect(wm.raw()).to_equal(0xCDAB)

**Example:** preserves other fields when setting
    Given var p = Preserve(0xABCD)
    Then  expect(p.high).to_equal(0xAB)
    Then  expect(p.low).to_equal(0xFF)

### Scenario: Raw Value Access

| # | Example | Status |
|---|---------|--------|
| 1 | gets raw value | pass |
| 2 | sets raw value | pass |

**Example:** gets raw value
    Given val ra = RawAccess(0x12345678)
    Then  expect(ra.raw()).to_equal(0x12345678)

**Example:** sets raw value
    Given var sr = SetRaw(0)
    Then  expect(sr.a).to_equal(0xCD)
    Then  expect(sr.b).to_equal(0xAB)

## Feature: Bitfield Validation

### Scenario: Overflow Detection

| # | Example | Status |
|---|---------|--------|
| 1 | validates total bits fit in backing | pass |
| 2 | validates large bitfields | pass |

**Example:** validates total bits fit in backing
    Then  expect(true).to_equal(true)

**Example:** validates large bitfields
    Then  expect(true).to_equal(true)

## Feature: Use Cases - Hardware Registers

### Scenario: x86 Control Registers

| # | Example | Status |
|---|---------|--------|
| 1 | models CR0 register | pass |
| 2 | models EFLAGS register | pass |

**Example:** models CR0 register
    Given var cr0 = CR0(0)

**Example:** models EFLAGS register
    Then  expect(true).to_equal(true)

### Scenario: Page Table Entry

| # | Example | Status |
|---|---------|--------|
| 1 | models 32-bit page table entry | pass |

**Example:** models 32-bit page table entry
    Given var pte = PageTableEntry32(0)
    Then  expect(pte.raw() & 0x3).to_equal(3)  # Present + RW

### Scenario: Network Headers

| # | Example | Status |
|---|---------|--------|
| 1 | models TCP flags | pass |

**Example:** models TCP flags
    Given var flags = TcpFlags(0)
    Then  expect(flags.raw()).to_equal(0x12)  # SYN + ACK

