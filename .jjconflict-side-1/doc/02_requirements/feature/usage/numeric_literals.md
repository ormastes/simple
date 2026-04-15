# Numeric Literals Specification
*Source:* `test/feature/usage/numeric_literals_spec.spl`
**Feature IDs:** #NUM-001  |  **Category:** Language | Literals  |  **Status:** Implemented

## Overview



## Overview

Tests for various numeric literal formats including hexadecimal, binary,
octal, and numeric separators with underscores.

## Syntax

```simple
val hex = 0xFF         # Hexadecimal (255)
val bin = 0b1010       # Binary (10)
val oct = 0o755        # Octal (493)
val sep = 1_000_000    # Underscores for readability
```

## Feature: Hexadecimal Literals

## Hex Numeric Literals

    Tests for hexadecimal numeric literals using 0x prefix.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses basic hex literal | pass |
| 2 | parses lowercase hex | pass |
| 3 | parses mixed case hex | pass |
| 4 | performs hex arithmetic | pass |
| 5 | compares hex and decimal | pass |

**Example:** parses basic hex literal
    Given val x = 0xFF
    Then  expect x == 255

**Example:** parses lowercase hex
    Given val x = 0xff
    Then  expect x == 255

**Example:** parses mixed case hex
    Given val x = 0xAb
    Then  expect x == 171

**Example:** performs hex arithmetic
    Given val x = 0x10 + 0x20
    Then  expect x == 48  # 16 + 32

**Example:** compares hex and decimal
    Then  expect 0x10 == 16
    Then  expect 0x100 == 256

## Feature: Binary Literals

## Binary Numeric Literals

    Tests for binary numeric literals using 0b prefix.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses basic binary literal | pass |
| 2 | parses binary with underscores | pass |
| 3 | performs binary arithmetic | pass |
| 4 | uses binary for bit patterns | pass |

**Example:** parses basic binary literal
    Given val x = 0b1010
    Then  expect x == 10

**Example:** parses binary with underscores
    Given val x = 0b1111_0000
    Then  expect x == 240

**Example:** performs binary arithmetic
    Given val x = 0b1000 + 0b0100
    Then  expect x == 12  # 8 + 4

**Example:** uses binary for bit patterns
    Given val flags = 0b0101
    Then  expect flags == 5

## Feature: Octal Literals

## Octal Numeric Literals

    Tests for octal numeric literals using 0o prefix.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses basic octal literal | pass |
| 2 | parses small octal | pass |
| 3 | performs octal arithmetic | pass |

**Example:** parses basic octal literal
    Given val x = 0o755
    Then  expect x == 493  # 7*64 + 5*8 + 5

**Example:** parses small octal
    Given val x = 0o10
    Then  expect x == 8

**Example:** performs octal arithmetic
    Given val x = 0o10 + 0o10
    Then  expect x == 16  # 8 + 8

## Feature: Numeric Separators

## Underscore Separators

    Tests for using underscores as separators in numeric literals.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses decimal with separators | pass |
| 2 | parses hex with separators | pass |
| 3 | parses binary with separators | pass |
| 4 | allows multiple underscores | pass |

**Example:** parses decimal with separators
    Given val x = 1_000_000
    Then  expect x == 1000000

**Example:** parses hex with separators
    Given val x = 0xFF_FF
    Then  expect x == 65535

**Example:** parses binary with separators
    Given val x = 0b1010_1010
    Then  expect x == 170

**Example:** allows multiple underscores
    Given val x = 100__000
    Then  expect x == 100000


