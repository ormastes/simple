# Integer Literals Specification
*Source:* `test/feature/usage/basic_types_integer_literals_spec.spl`
**Feature IDs:** #200-210  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



## Overview

Integer literals in Simple support multiple base formats (decimal, hexadecimal, binary, octal),
underscore separators for readability, type suffixes for explicit sizing, and user-defined unit
suffixes for semantic meaning. All integers default to 64-bit signed (`i64`) unless explicitly
typed with a suffix.

## Syntax

### Base Formats

```simple
val decimal = 42                # Decimal (base 10)
val hex = 0xFF                  # Hexadecimal (base 16)
val binary = 0b1010             # Binary (base 2)
val octal = 0o77                # Octal (base 8)
```

### Underscore Separators

```simple
val million = 1_000_000         # Decimal with underscores
val hex_color = 0xFF_00_FF      # Hex with underscores
val binary_byte = 0b1111_0000   # Binary with underscores
```

### Type Suffixes

```simple
val byte = 255u8                # Unsigned 8-bit
val short = 1000i16             # Signed 16-bit
val int = 42i32                 # Signed 32-bit
val long = 1000000i64           # Signed 64-bit (default)
```

### Unit Suffixes

```simple
val port = 8080_port            # Port number
val ip = 0x7F000001_ip          # IP address (127.0.0.1)
val distance = 100_km           # Distance in kilometers
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Base Format | Decimal, hex (0x), binary (0b), octal (0o) |
| Underscore Separator | Visual grouping, stripped during parsing |
| Type Suffix | Explicit integer size (i8, i16, i32, i64, u8, u16, u32, u64) |
| Unit Suffix | User-defined semantic units (_port, _ip, _km) |
| Default Type | i64 (64-bit signed integer) |

## Behavior

- **Decimal**: Standard base-10 notation, supports underscores
- **Hexadecimal**: `0x` or `0X` prefix, case-insensitive digits
- **Binary**: `0b` or `0B` prefix, only 0 and 1 digits
- **Octal**: `0o` or `0O` prefix, digits 0-7
- **Underscores**: Ignored during parsing, cannot be consecutive or at boundaries
- **Type Suffixes**: Parsed as token metadata, affect type inference
- **Unit Suffixes**: Parsed as separate concept, provide semantic meaning

## Related Specifications

- [Type Inference](../type_inference/type_inference_spec.md) - Integer type deduction
- [Arithmetic Operators](../operators_arithmetic/operators_arithmetic_spec.md) - Integer operations
- [Basic Types](../basic_types/basic_types_spec.md) - Type system overview

## Implementation Notes

**Lexer:** `src/parser/src/lexer/numbers.rs`
- `scan_number()` - Main entry point for all numeric literals
- `scan_radix_digits()` - Collects digits with underscore handling
- `parse_radix_integer()` - Parses non-decimal bases
- `scan_numeric_suffix()` - Extracts type/unit suffixes

**Token Types:**
- `TokenKind.Integer(i64)` - Plain integer without suffix
- `TokenKind.TypedInteger(i64, NumericSuffix)` - With type or unit suffix

**Performance:** Direct parsing into `i64` with zero-copy where possible.
Underscores are skipped during scanning (no allocation needed).

## Examples

```simple
# Decimal literals
val x = 42
val large = 1_000_000

# Hexadecimal
val color = 0xFF00FF
val addr = 0x7F000001

# Binary
val flags = 0b1111_0000
val mask = 0b11111111

# Octal
val perms = 0o755
val mode = 0o644

# With type suffixes
val byte = 255u8
val port = 8080u16

# With unit suffixes
val timeout = 5000_ms
val size = 1024_bytes
```

## Feature: Integer Literals - Decimal

## Decimal Integer Literals

    Decimal (base 10) is the default notation for integer literals.
    Supports underscore separators for readability.

### Scenario: basic decimal literals

### Scenario: Basic Decimal Integers

        Standard decimal integer notation.

        ```simple
        val x = 42
        val y = 0
        val z = 1000000
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses single digit | pass |
| 2 | parses zero | pass |
| 3 | parses multi-digit | pass |
| 4 | parses large number | pass |

**Example:** parses single digit
    Given val x = 5
    Then  expect(x).to_equal(5)

**Example:** parses zero
    Given val x = 0
    Then  expect(x == 0).to_equal(true)

**Example:** parses multi-digit
    Given val x = 123456
    Then  expect(x).to_equal(123456)

**Example:** parses large number
    Given val x = 999999999
    Then  expect(x).to_equal(999999999)

### Scenario: with underscore separators

### Scenario: Underscore Separators

        Underscores improve readability for large numbers.

        ```simple
        val million = 1_000_000
        val billion = 1_000_000_000
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses with single underscore | pass |
| 2 | parses with multiple underscores | pass |
| 3 | parses with arbitrary grouping | pass |

**Example:** parses with single underscore
    Given val x = 1_000
    Then  expect(x).to_equal(1000)

**Example:** parses with multiple underscores
    Given val x = 1_000_000
    Then  expect(x).to_equal(1000000)

**Example:** parses with arbitrary grouping
    Given val x = 12_34_56
    Then  expect(x).to_equal(123456)

## Feature: Integer Literals - Hexadecimal

## Hexadecimal Integer Literals

    Hexadecimal (base 16) uses `0x` or `0X` prefix.
    Digits: 0-9, a-f, A-F (case insensitive).

### Scenario: basic hex literals

### Scenario: Basic Hexadecimal

        Hex literals start with 0x prefix.

        ```simple
        val x = 0xFF
        val y = 0x10
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses lowercase hex | pass |
| 2 | parses uppercase hex | pass |
| 3 | parses mixed case | pass |
| 4 | parses single hex digit | pass |
| 5 | parses multi-digit hex | pass |

**Example:** parses lowercase hex
    Given val x = 0xff
    Then  expect(x).to_equal(255)

**Example:** parses uppercase hex
    Given val x = 0xFF
    Then  expect(x).to_equal(255)

**Example:** parses mixed case
    Given val x = 0xAb
    Then  expect(x).to_equal(171)

**Example:** parses single hex digit
    Given val x = 0xF
    Then  expect(x).to_equal(15)

**Example:** parses multi-digit hex
    Given val x = 0x1A2B
    Then  expect(x).to_equal(6699)

### Scenario: with underscore separators

### Scenario: Hex with Underscores

        Underscores can group hex digits.

        ```simple
        val color = 0xFF_00_FF
        val addr = 0x7F00_0001
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses hex with underscores | pass |
| 2 | parses byte grouping | pass |

**Example:** parses hex with underscores
    Given val x = 0xFF_00
    Then  expect(x).to_equal(65280)

**Example:** parses byte grouping
    Given val x = 0xFF_FF_FF_FF
    Then  expect(x).to_equal(4294967295)

## Feature: Integer Literals - Binary

## Binary Integer Literals

    Binary (base 2) uses `0b` or `0B` prefix.
    Digits: 0 and 1 only.

### Scenario: basic binary literals

### Scenario: Basic Binary

        Binary literals start with 0b prefix.

        ```simple
        val x = 0b1010
        val y = 0b1111
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple binary | pass |
| 2 | parses all ones | pass |
| 3 | parses all zeros | pass |
| 4 | parses single bit | pass |
| 5 | parses byte value | pass |

**Example:** parses simple binary
    Given val x = 0b1010
    Then  expect(x).to_equal(10)

**Example:** parses all ones
    Given val x = 0b1111
    Then  expect(x).to_equal(15)

**Example:** parses all zeros
    Given val x = 0b0000
    Then  expect(x == 0).to_equal(true)

**Example:** parses single bit
    Given val x = 0b1
    Then  expect(x).to_equal(1)

**Example:** parses byte value
    Given val x = 0b11111111
    Then  expect(x).to_equal(255)

### Scenario: with underscore separators

### Scenario: Binary with Underscores

        Underscores can group binary digits (nibbles, bytes).

        ```simple
        val byte = 0b1111_0000
        val word = 0b1111_1111_0000_0000
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses nibble grouping | pass |
| 2 | parses byte pairs | pass |

**Example:** parses nibble grouping
    Given val x = 0b1111_0000
    Then  expect(x).to_equal(240)

**Example:** parses byte pairs
    Given val x = 0b1010_1010
    Then  expect(x).to_equal(170)

## Feature: Integer Literals - Octal

## Octal Integer Literals

    Octal (base 8) uses `0o` or `0O` prefix.
    Digits: 0-7 only.

### Scenario: basic octal literals

### Scenario: Basic Octal

        Octal literals start with 0o prefix.

        ```simple
        val perms = 0o755
        val mode = 0o644
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple octal | pass |
| 2 | parses unix permissions | pass |
| 3 | parses all sevens | pass |
| 4 | parses single octal digit | pass |

**Example:** parses simple octal
    Given val x = 0o10
    Then  expect(x).to_equal(8)

**Example:** parses unix permissions
    Given val x = 0o755
    Then  expect(x).to_equal(493)

**Example:** parses all sevens
    Given val x = 0o777
    Then  expect(x).to_equal(511)

**Example:** parses single octal digit
    Given val x = 0o7
    Then  expect(x).to_equal(7)

## Feature: Integer Literals - Type Suffixes

## Type Suffixes

    Explicit type suffixes specify integer size and signedness.
    Signed: i8, i16, i32, i64
    Unsigned: u8, u16, u32, u64

### Scenario: signed type suffixes

### Scenario: Signed Type Suffixes

        Signed integers with explicit size.

        ```simple
        val byte = 127i8
        val short = 1000i16
        val int = 100000i32
        val long = 1000000000i64
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses i32 suffix | pass |
| 2 | parses i64 suffix | pass |

**Example:** parses i32 suffix
    Given val x = 42i32
    Then  expect(x).to_equal(42)

**Example:** parses i64 suffix
    Given val x = 1000i64
    Then  expect(x).to_equal(1000)

### Scenario: unsigned type suffixes

### Scenario: Unsigned Type Suffixes

        Unsigned integers with explicit size.

        ```simple
        val byte = 255u8
        val port = 8080u16
        val count = 4294967295u32
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses u8 suffix | pass |
| 2 | parses u16 suffix | pass |
| 3 | parses u32 suffix | pass |

**Example:** parses u8 suffix
    Given val x = 255u8
    Then  expect(x).to_equal(255)

**Example:** parses u16 suffix
    Given val x = 1000u16
    Then  expect(x).to_equal(1000)

**Example:** parses u32 suffix
    Given val x = 12345u32
    Then  expect(x).to_equal(12345)

## Feature: Integer Literals - Mixed Formats

## Mixed Format Expressions

    Different integer literal formats can be used in the same expression.

### Scenario: combining formats

### Scenario: Multiple Formats

        Mix decimal, hex, binary, octal in calculations.

        ```simple
        val result = 10 + 0xA + 0b1010 + 0o12
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | combines decimal and hex | pass |
| 2 | combines decimal and binary | pass |
| 3 | combines all formats | pass |

**Example:** combines decimal and hex
    Given val result = 10 + 0xA
    Then  expect(result).to_equal(20)

**Example:** combines decimal and binary
    Given val result = 5 + 0b101
    Then  expect(result).to_equal(10)

**Example:** combines all formats
    Given val result = 1 + 0xF + 0b1111 + 0o17
    Then  expect(result).to_equal(46)

## Feature: Integer Literals - Edge Cases

## Edge Case Handling

    Special cases and boundary conditions.

### Scenario: with zero

### Scenario: Zero in Different Bases

        Zero can be represented in any base.

        ```simple
        val dec_zero = 0
        val hex_zero = 0x0
        val bin_zero = 0b0
        val oct_zero = 0o0
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | parses decimal zero | pass |
| 2 | parses hex zero | pass |
| 3 | parses binary zero | pass |
| 4 | parses octal zero | pass |

**Example:** parses decimal zero
    Given val x = 0
    Then  expect(x == 0).to_equal(true)

**Example:** parses hex zero
    Given val x = 0x0
    Then  expect(x == 0).to_equal(true)

**Example:** parses binary zero
    Given val x = 0b0
    Then  expect(x == 0).to_equal(true)

**Example:** parses octal zero
    Given val x = 0o0
    Then  expect(x == 0).to_equal(true)

### Scenario: with one

### Scenario: One in Different Bases

        One is represented the same in all bases.

| # | Example | Status |
|---|---------|--------|
| 1 | parses decimal one | pass |
| 2 | parses hex one | pass |
| 3 | parses binary one | pass |
| 4 | parses octal one | pass |

**Example:** parses decimal one
    Given val x = 1
    Then  expect(x).to_equal(1)

**Example:** parses hex one
    Given val x = 0x1
    Then  expect(x).to_equal(1)

**Example:** parses binary one
    Given val x = 0b1
    Then  expect(x).to_equal(1)

**Example:** parses octal one
    Given val x = 0o1
    Then  expect(x).to_equal(1)

### Scenario: with maximum values

### Scenario: Large Integer Values

        Large numbers within i64 range.

| # | Example | Status |
|---|---------|--------|
| 1 | parses large decimal | pass |
| 2 | parses large hex | pass |

**Example:** parses large decimal
    Given val x = 2147483647
    Then  expect(x).to_equal(2147483647)

**Example:** parses large hex
    Given val x = 0x7FFFFFFF
    Then  expect(x).to_equal(2147483647)

## Feature: Integer Literals - Case Insensitivity

## Case Insensitivity

    Hex, binary, and octal prefixes are case-insensitive.

### Scenario: hex prefix case

### Scenario: Hex Prefix Case Variations

        Both 0x and 0X are valid.

| # | Example | Status |
|---|---------|--------|
| 1 | accepts lowercase 0x | pass |
| 2 | accepts uppercase 0X | pass |

**Example:** accepts lowercase 0x
    Given val x = 0xff
    Then  expect(x).to_equal(255)

**Example:** accepts uppercase 0X
    Given val x = 0XFF
    Then  expect(x).to_equal(255)

### Scenario: binary prefix case

### Scenario: Binary Prefix Case Variations

        Both 0b and 0B are valid.

| # | Example | Status |
|---|---------|--------|
| 1 | accepts lowercase 0b | pass |
| 2 | accepts uppercase 0B | pass |

**Example:** accepts lowercase 0b
    Given val x = 0b1010
    Then  expect(x).to_equal(10)

**Example:** accepts uppercase 0B
    Given val x = 0B1010
    Then  expect(x).to_equal(10)

### Scenario: octal prefix case

### Scenario: Octal Prefix Case Variations

        Both 0o and 0O are valid.

| # | Example | Status |
|---|---------|--------|
| 1 | accepts lowercase 0o | pass |
| 2 | accepts uppercase 0O | pass |

**Example:** accepts lowercase 0o
    Given val x = 0o77
    Then  expect(x).to_equal(63)

**Example:** accepts uppercase 0O
    Given val x = 0O77
    Then  expect(x).to_equal(63)


