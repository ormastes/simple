# Integer Literals Specification

> Integer literals in Simple support multiple base formats (decimal, hexadecimal, binary, octal), underscore separators for readability, type suffixes for explicit sizing, and user-defined unit suffixes for semantic meaning. All integers default to 64-bit signed (`i64`) unless explicitly typed with a suffix.

<!-- sdn-diagram:id=basic_types_integer_literals_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=basic_types_integer_literals_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

basic_types_integer_literals_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=basic_types_integer_literals_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integer Literals Specification

Integer literals in Simple support multiple base formats (decimal, hexadecimal, binary, octal), underscore separators for readability, type suffixes for explicit sizing, and user-defined unit suffixes for semantic meaning. All integers default to 64-bit signed (`i64`) unless explicitly typed with a suffix.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #200-210 |
| Category | Syntax |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/basic_types_integer_literals_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Integer Literals - Decimal

#### basic decimal literals

#### parses single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
expect(x).to_equal(5)
```

</details>

#### parses zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0
expect(x == 0).to_equal(true)
```

</details>

#### parses multi-digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 123456
expect(x).to_equal(123456)
```

</details>

#### parses large number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 999999999
expect(x).to_equal(999999999)
```

</details>

#### with underscore separators

#### parses with single underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1_000
expect(x).to_equal(1000)
```

</details>

#### parses with multiple underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1_000_000
expect(x).to_equal(1000000)
```

</details>

#### parses with arbitrary grouping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 12_34_56
expect(x).to_equal(123456)
```

</details>

### Integer Literals - Hexadecimal

#### basic hex literals

#### parses lowercase hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xff
expect(x).to_equal(255)
```

</details>

#### parses uppercase hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xFF
expect(x).to_equal(255)
```

</details>

#### parses mixed case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xAb
expect(x).to_equal(171)
```

</details>

#### parses single hex digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xF
expect(x).to_equal(15)
```

</details>

#### parses multi-digit hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0x1A2B
expect(x).to_equal(6699)
```

</details>

#### with underscore separators

#### parses hex with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xFF_00
expect(x).to_equal(65280)
```

</details>

#### parses byte grouping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xFF_FF_FF_FF
expect(x).to_equal(4294967295)
```

</details>

### Integer Literals - Binary

#### basic binary literals

#### parses simple binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1010
expect(x).to_equal(10)
```

</details>

#### parses all ones

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1111
expect(x).to_equal(15)
```

</details>

#### parses all zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b0000
expect(x == 0).to_equal(true)
```

</details>

#### parses single bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1
expect(x).to_equal(1)
```

</details>

#### parses byte value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b11111111
expect(x).to_equal(255)
```

</details>

#### with underscore separators

#### parses nibble grouping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1111_0000
expect(x).to_equal(240)
```

</details>

#### parses byte pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1010_1010
expect(x).to_equal(170)
```

</details>

### Integer Literals - Octal

#### basic octal literals

#### parses simple octal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o10
expect(x).to_equal(8)
```

</details>

#### parses unix permissions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o755
expect(x).to_equal(493)
```

</details>

#### parses all sevens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o777
expect(x).to_equal(511)
```

</details>

#### parses single octal digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o7
expect(x).to_equal(7)
```

</details>

### Integer Literals - Type Suffixes

#### signed type suffixes

#### parses i32 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42i32
expect(x).to_equal(42)
```

</details>

#### parses i64 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1000i64
expect(x).to_equal(1000)
```

</details>

#### unsigned type suffixes

#### parses u8 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 255u8
expect(x).to_equal(255)
```

</details>

#### parses u16 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1000u16
expect(x).to_equal(1000)
```

</details>

#### parses u32 suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 12345u32
expect(x).to_equal(12345)
```

</details>

### Integer Literals - Mixed Formats

#### combining formats

#### combines decimal and hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 + 0xA
expect(result).to_equal(20)
```

</details>

#### combines decimal and binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5 + 0b101
expect(result).to_equal(10)
```

</details>

#### combines all formats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 + 0xF + 0b1111 + 0o17
expect(result).to_equal(46)
```

</details>

### Integer Literals - Edge Cases

#### with zero

#### parses decimal zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0
expect(x == 0).to_equal(true)
```

</details>

#### parses hex zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0x0
expect(x == 0).to_equal(true)
```

</details>

#### parses binary zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b0
expect(x == 0).to_equal(true)
```

</details>

#### parses octal zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o0
expect(x == 0).to_equal(true)
```

</details>

#### with one

#### parses decimal one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
expect(x).to_equal(1)
```

</details>

#### parses hex one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0x1
expect(x).to_equal(1)
```

</details>

#### parses binary one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1
expect(x).to_equal(1)
```

</details>

#### parses octal one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o1
expect(x).to_equal(1)
```

</details>

#### with maximum values

#### parses large decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2147483647
expect(x).to_equal(2147483647)
```

</details>

#### parses large hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0x7FFFFFFF
expect(x).to_equal(2147483647)
```

</details>

### Integer Literals - Case Insensitivity

#### hex prefix case

#### accepts lowercase 0x

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xff
expect(x).to_equal(255)
```

</details>

#### accepts uppercase 0X

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0XFF
expect(x).to_equal(255)
```

</details>

#### binary prefix case

#### accepts lowercase 0b

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1010
expect(x).to_equal(10)
```

</details>

#### accepts uppercase 0B

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0B1010
expect(x).to_equal(10)
```

</details>

#### octal prefix case

#### accepts lowercase 0o

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o77
expect(x).to_equal(63)
```

</details>

#### accepts uppercase 0O

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0O77
expect(x).to_equal(63)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
