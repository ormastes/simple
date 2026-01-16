*Source: `simple/test/system/features/basic_types_integer_literals/basic_types_integer_literals_spec.spl`*
*Last Updated: 2026-01-16*

---

# Integer Literals Specification

**Feature IDs:** #200-210
**Category:** Syntax
**Difficulty:** 1/5
**Status:** Implemented

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
- `TokenKind::Integer(i64)` - Plain integer without suffix
- `TokenKind::TypedInteger(i64, NumericSuffix)` - With type or unit suffix

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

## Decimal Integer Literals

    Decimal (base 10) is the default notation for integer literals.
    Supports underscore separators for readability.

### Scenario: Basic Decimal Integers

        Standard decimal integer notation.

        ```simple
        val x = 42
        val y = 0
        val z = 1000000
        ```

### Scenario: Underscore Separators

        Underscores improve readability for large numbers.

        ```simple
        val million = 1_000_000
        val billion = 1_000_000_000
        ```

## Hexadecimal Integer Literals

    Hexadecimal (base 16) uses `0x` or `0X` prefix.
    Digits: 0-9, a-f, A-F (case insensitive).

### Scenario: Basic Hexadecimal

        Hex literals start with 0x prefix.

        ```simple
        val x = 0xFF
        val y = 0x10
        ```

### Scenario: Hex with Underscores

        Underscores can group hex digits.

        ```simple
        val color = 0xFF_00_FF
        val addr = 0x7F00_0001
        ```

## Binary Integer Literals

    Binary (base 2) uses `0b` or `0B` prefix.
    Digits: 0 and 1 only.

### Scenario: Basic Binary

        Binary literals start with 0b prefix.

        ```simple
        val x = 0b1010
        val y = 0b1111
        ```

### Scenario: Binary with Underscores

        Underscores can group binary digits (nibbles, bytes).

        ```simple
        val byte = 0b1111_0000
        val word = 0b1111_1111_0000_0000
        ```

## Octal Integer Literals

    Octal (base 8) uses `0o` or `0O` prefix.
    Digits: 0-7 only.

### Scenario: Basic Octal

        Octal literals start with 0o prefix.

        ```simple
        val perms = 0o755
        val mode = 0o644
        ```

## Type Suffixes

    Explicit type suffixes specify integer size and signedness.
    Signed: i8, i16, i32, i64
    Unsigned: u8, u16, u32, u64

### Scenario: Signed Type Suffixes

        Signed integers with explicit size.

        ```simple
        val byte = 127i8
        val short = 1000i16
        val int = 100000i32
        val long = 1000000000i64
        ```

### Scenario: Unsigned Type Suffixes

        Unsigned integers with explicit size.

        ```simple
        val byte = 255u8
        val port = 8080u16
        val count = 4294967295u32
        ```

## Mixed Format Expressions

    Different integer literal formats can be used in the same expression.

### Scenario: Multiple Formats

        Mix decimal, hex, binary, octal in calculations.

        ```simple
        val result = 10 + 0xA + 0b1010 + 0o12
        ```

## Edge Case Handling

    Special cases and boundary conditions.

### Scenario: Zero in Different Bases

        Zero can be represented in any base.

        ```simple
        val dec_zero = 0
        val hex_zero = 0x0
        val bin_zero = 0b0
        val oct_zero = 0o0
        ```

### Scenario: One in Different Bases

        One is represented the same in all bases.

### Scenario: Large Integer Values

        Large numbers within i64 range.

## Case Insensitivity

    Hex, binary, and octal prefixes are case-insensitive.

### Scenario: Hex Prefix Case Variations

        Both 0x and 0X are valid.

### Scenario: Binary Prefix Case Variations

        Both 0b and 0B are valid.

### Scenario: Octal Prefix Case Variations

        Both 0o and 0O are valid.
