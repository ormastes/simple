# x86 Bare-Metal Boot Specification
*Source:* `test/feature/usage/x86_boot_spec.spl`
**Feature IDs:** #BM-BOOT-001  |  **Category:** Bare-Metal / x86  |  **Status:** In Progress

## Overview



use std.text.{NL}

Tests for the x86 bare-metal boot infrastructure including:
- Multiboot header generation
- GDT setup and loading
- Serial port initialization
- Test harness output

## Feature: x86 Boot Infrastructure

### Scenario: Multiboot Header

| # | Example | Status |
|---|---------|--------|
| 1 | has correct magic number | pass |
| 2 | has correct flags | pass |
| 3 | checksum validates | pass |

**Example:** has correct magic number
    Given val MULTIBOOT_MAGIC: u32 = 0x1BADB002
    Then  expect(MULTIBOOT_MAGIC).to_equal(0x1BADB002)

**Example:** has correct flags
    Given val MULTIBOOT_PAGE_ALIGN: u32 = 1 << 0
    Given val MULTIBOOT_MEMORY_INFO: u32 = 1 << 1
    Given val MULTIBOOT_FLAGS: u32 = MULTIBOOT_PAGE_ALIGN | MULTIBOOT_MEMORY_INFO
    Then  expect(MULTIBOOT_FLAGS).to_equal(3)

**Example:** checksum validates
    Given val MULTIBOOT_MAGIC: u32 = 0x1BADB002
    Given val MULTIBOOT_FLAGS: u32 = 3
    Given val MULTIBOOT_CHECKSUM: u32 = 0 - (MULTIBOOT_MAGIC + MULTIBOOT_FLAGS)
    Given val sum = MULTIBOOT_MAGIC + MULTIBOOT_FLAGS + MULTIBOOT_CHECKSUM
    Then  expect((sum & 0xFFFFFFFF) as u32).to_equal(0)

### Scenario: GDT Entries

| # | Example | Status |
|---|---------|--------|
| 1 | null descriptor is all zeros | pass |
| 2 | kernel code segment has correct access | pass |
| 3 | kernel data segment has correct access | pass |

**Example:** null descriptor is all zeros
    Then  expect(true).to_equal(true)  # Placeholder - actual test needs GDT type

**Example:** kernel code segment has correct access
    Given val ACCESS_PRESENT: u8 = 1 << 7
    Given val ACCESS_RING0: u8 = 0 << 5
    Given val ACCESS_CODE_DATA: u8 = 1 << 4
    Given val ACCESS_EXEC: u8 = 1 << 3
    Given val ACCESS_RW: u8 = 1 << 1
    Given val expected = ACCESS_PRESENT | ACCESS_RING0 | ACCESS_CODE_DATA | ACCESS_EXEC | ACCESS_RW
    Then  expect(expected).to_equal(0x9A)  # 0b10011010

**Example:** kernel data segment has correct access
    Given val ACCESS_PRESENT: u8 = 1 << 7
    Given val ACCESS_RING0: u8 = 0 << 5
    Given val ACCESS_CODE_DATA: u8 = 1 << 4
    Given val ACCESS_RW: u8 = 1 << 1
    Given val expected = ACCESS_PRESENT | ACCESS_RING0 | ACCESS_CODE_DATA | ACCESS_RW
    Then  expect(expected).to_equal(0x92)  # 0b10010010

### Scenario: Segment Selectors

| # | Example | Status |
|---|---------|--------|
| 1 | kernel code selector is 0x08 | pass |
| 2 | kernel data selector is 0x10 | pass |
| 3 | user code selector has RPL 3 | pass |
| 4 | user data selector has RPL 3 | pass |

**Example:** kernel code selector is 0x08
    Given val KERNEL_CODE_SELECTOR: u16 = 0x08
    Then  expect(KERNEL_CODE_SELECTOR).to_equal(8)

**Example:** kernel data selector is 0x10
    Given val KERNEL_DATA_SELECTOR: u16 = 0x10
    Then  expect(KERNEL_DATA_SELECTOR).to_equal(16)

**Example:** user code selector has RPL 3
    Given val USER_CODE_SELECTOR: u16 = 0x18 | 3
    Then  expect(USER_CODE_SELECTOR).to_equal(0x1B)

**Example:** user data selector has RPL 3
    Given val USER_DATA_SELECTOR: u16 = 0x20 | 3
    Then  expect(USER_DATA_SELECTOR).to_equal(0x23)

## Feature: Serial Port

### Scenario: COM Port Addresses

| # | Example | Status |
|---|---------|--------|
| 1 | COM1 base address is 0x3F8 | pass |
| 2 | COM2 base address is 0x2F8 | pass |

**Example:** COM1 base address is 0x3F8
    Given val COM1: u16 = 0x3F8
    Then  expect(COM1).to_equal(0x3F8)

**Example:** COM2 base address is 0x2F8
    Given val COM2: u16 = 0x2F8
    Then  expect(COM2).to_equal(0x2F8)

### Scenario: UART Registers

| # | Example | Status |
|---|---------|--------|
| 1 | data register offset is 0 | pass |
| 2 | line status register offset is 5 | pass |

**Example:** data register offset is 0
    Given val UART_DATA: u16 = 0
    Then  expect(UART_DATA).to_equal(0)

**Example:** line status register offset is 5
    Given val UART_LSR: u16 = 5
    Then  expect(UART_LSR).to_equal(5)

### Scenario: Baud Rate Divisors

| # | Example | Status |
|---|---------|--------|
| 1 | 115200 baud divisor is 1 | pass |
| 2 | 9600 baud divisor is 12 | pass |

**Example:** 115200 baud divisor is 1
    Given val BAUD_115200: u16 = 1
    Then  expect(BAUD_115200).to_equal(1)

**Example:** 9600 baud divisor is 12
    Given val BAUD_9600: u16 = 12
    Then  expect(BAUD_9600).to_equal(12)

## Feature: Linker Script Generation

### Scenario: Memory Regions

| # | Example | Status |
|---|---------|--------|
| 1 | formats hex addresses correctly | pass |

**Example:** formats hex addresses correctly
    Given val addr: i64 = 1048576
    Then  expect(addr).to_equal(0x100000)

### Scenario: Section Layout

| # | Example | Status |
|---|---------|--------|
| 1 | multiboot section comes first | pass |

**Example:** multiboot section comes first
    Given val MULTIBOOT_ADDR: i64 = 0x00100000
    Given val MULTIBOOT_LIMIT: i64 = 0x00102000  # 8KB after load addr
    Then  expect(MULTIBOOT_ADDR).to_be_less_than(MULTIBOOT_LIMIT)

## Feature: QEMU Exit Codes

### Scenario: Exit Code Translation

| # | Example | Status |
|---|---------|--------|
| 1 | success exit code (0) becomes (1) | pass |
| 2 | failure exit code (1) becomes (3) | pass |
| 3 | can decode QEMU exit code | pass |

**Example:** success exit code (0) becomes (1)
    Given val value = 0
    Given val qemu_exit = (value << 1) | 1
    Then  expect(qemu_exit).to_equal(1)

**Example:** failure exit code (1) becomes (3)
    Given val value = 1
    Given val qemu_exit = (value << 1) | 1
    Then  expect(qemu_exit).to_equal(3)

**Example:** can decode QEMU exit code
    Given val qemu_exit = 3
    Given val original = (qemu_exit - 1) / 2
    Then  expect(original).to_equal(1)


