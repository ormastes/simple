# Integer Literals Specification

Integer literals in Simple support multiple base formats (decimal, hexadecimal, binary, octal), underscore separators for readability, type suffixes for explicit sizing, and user-defined unit suffixes for semantic meaning. All integers default to 64-bit signed (`i64`) unless explicitly typed with a suffix.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #200-210 |
| Category | Syntax |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/feature/usage/basic_types_integer_literals_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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
val x = 42
val large = 1_000_000

val color = 0xFF00FF
val addr = 0x7F000001

val flags = 0b1111_0000
val mask = 0b11111111

val perms = 0o755
val mode = 0o644

val byte = 255u8
val port = 8080u16

val timeout = 5000_ms
val size = 1024_bytes
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/basic_types_integer_literals/result.json` |

## Scenarios

- parses single digit
- parses zero
- parses multi-digit
- parses large number
- parses with single underscore
- parses with multiple underscores
- parses with arbitrary grouping
- parses lowercase hex
- parses uppercase hex
- parses mixed case
- parses single hex digit
- parses multi-digit hex
- parses hex with underscores
- parses byte grouping
- parses simple binary
- parses all ones
- parses all zeros
- parses single bit
- parses byte value
- parses nibble grouping
- parses byte pairs
- parses simple octal
- parses unix permissions
- parses all sevens
- parses single octal digit
- parses i32 suffix
- parses i64 suffix
- parses u8 suffix
- parses u16 suffix
- parses u32 suffix
- combines decimal and hex
- combines decimal and binary
- combines all formats
- parses decimal zero
- parses hex zero
- parses binary zero
- parses octal zero
- parses decimal one
- parses hex one
- parses binary one
- parses octal one
- parses large decimal
- parses large hex
- accepts lowercase 0x
- accepts uppercase 0X
- accepts lowercase 0b
- accepts uppercase 0B
- accepts lowercase 0o
- accepts uppercase 0O
