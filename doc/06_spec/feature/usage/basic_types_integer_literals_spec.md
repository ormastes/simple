# Integer Literals Specification

> Integer literals in Simple support multiple base formats (decimal, hexadecimal, binary, octal), underscore separators for readability, type suffixes for explicit sizing, and user-defined unit suffixes for semantic meaning. All integers default to 64-bit signed (`i64`) unless explicitly typed with a suffix.

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
| Source | `test/feature/usage/basic_types_integer_literals_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Integer literals in Simple support multiple base formats (decimal, hexadecimal, binary, octal),
underscore separators for readability, type suffixes for explicit sizing, and user-defined unit
suffixes for semantic meaning. All integers default to 64-bit signed (`i64`) unless explicitly
typed with a suffix.

## Syntax

### Base Formats

```simple
use std.spec.step

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

- parses single digit
   - Expected: x equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses single digit")
val x = 5
expect(x).to_equal(5)
```

</details>

#### parses zero

- parses zero
   - Expected: x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses zero")
val x = 0
expect(x).to_equal(0)
```

</details>

#### parses multi-digit

- parses multi-digit
   - Expected: x equals `123456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multi-digit")
val x = 123456
expect(x).to_equal(123456)
```

</details>

#### parses large number

- parses large number
   - Expected: x equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses large number")
val x = 999999999
expect(x).to_equal(999999999)
```

</details>

#### with underscore separators

#### parses with single underscore

- parses with single underscore
   - Expected: x equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses with single underscore")
val x = 1_000
expect(x).to_equal(1000)
```

</details>

#### parses with multiple underscores

- parses with multiple underscores
   - Expected: x equals `1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses with multiple underscores")
val x = 1_000_000
expect(x).to_equal(1000000)
```

</details>

#### parses with arbitrary grouping

- parses with arbitrary grouping
   - Expected: x equals `123456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses with arbitrary grouping")
val x = 12_34_56
expect(x).to_equal(123456)
```

</details>

### Integer Literals - Hexadecimal

#### basic hex literals

#### parses lowercase hex

- parses lowercase hex
   - Expected: x equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses lowercase hex")
val x = 0xff
expect(x).to_equal(255)
```

</details>

#### parses uppercase hex

- parses uppercase hex
   - Expected: x equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses uppercase hex")
val x = 0xFF
expect(x).to_equal(255)
```

</details>

#### parses mixed case

- parses mixed case
   - Expected: x equals `171`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mixed case")
val x = 0xAb
expect(x).to_equal(171)
```

</details>

#### parses single hex digit

- parses single hex digit
   - Expected: x equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses single hex digit")
val x = 0xF
expect(x).to_equal(15)
```

</details>

#### parses multi-digit hex

- parses multi-digit hex
   - Expected: x equals `6699`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multi-digit hex")
val x = 0x1A2B
expect(x).to_equal(6699)
```

</details>

#### with underscore separators

#### parses hex with underscores

- parses hex with underscores
   - Expected: x equals `65280`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses hex with underscores")
val x = 0xFF_00
expect(x).to_equal(65280)
```

</details>

#### parses byte grouping

- parses byte grouping
   - Expected: x equals `4294967295`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses byte grouping")
val x = 0xFF_FF_FF_FF
expect(x).to_equal(4294967295)
```

</details>

### Integer Literals - Binary

#### basic binary literals

#### parses simple binary

- parses simple binary
   - Expected: x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple binary")
val x = 0b1010
expect(x).to_equal(10)
```

</details>

#### parses all ones

- parses all ones
   - Expected: x equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses all ones")
val x = 0b1111
expect(x).to_equal(15)
```

</details>

#### parses all zeros

- parses all zeros
   - Expected: x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses all zeros")
val x = 0b0000
expect(x).to_equal(0)
```

</details>

#### parses single bit

- parses single bit
   - Expected: x equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses single bit")
val x = 0b1
expect(x).to_equal(1)
```

</details>

#### parses byte value

- parses byte value
   - Expected: x equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses byte value")
val x = 0b11111111
expect(x).to_equal(255)
```

</details>

#### with underscore separators

#### parses nibble grouping

- parses nibble grouping
   - Expected: x equals `240`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses nibble grouping")
val x = 0b1111_0000
expect(x).to_equal(240)
```

</details>

#### parses byte pairs

- parses byte pairs
   - Expected: x equals `170`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses byte pairs")
val x = 0b1010_1010
expect(x).to_equal(170)
```

</details>

### Integer Literals - Octal

#### basic octal literals

#### parses simple octal

- parses simple octal
   - Expected: x equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple octal")
val x = 0o10
expect(x).to_equal(8)
```

</details>

#### parses unix permissions

- parses unix permissions
   - Expected: x equals `493`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses unix permissions")
val x = 0o755
expect(x).to_equal(493)
```

</details>

#### parses all sevens

- parses all sevens
   - Expected: x equals `511`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses all sevens")
val x = 0o777
expect(x).to_equal(511)
```

</details>

#### parses single octal digit

- parses single octal digit
   - Expected: x equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses single octal digit")
val x = 0o7
expect(x).to_equal(7)
```

</details>

### Integer Literals - Type Suffixes

#### signed type suffixes

#### parses i32 suffix

- parses i32 suffix
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses i32 suffix")
val x = 42i32
expect(x).to_equal(42)
```

</details>

#### parses i64 suffix

- parses i64 suffix
   - Expected: x equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses i64 suffix")
val x = 1000i64
expect(x).to_equal(1000)
```

</details>

#### unsigned type suffixes

#### parses u8 suffix

- parses u8 suffix
   - Expected: x equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses u8 suffix")
val x = 255u8
expect(x).to_equal(255)
```

</details>

#### parses u16 suffix

- parses u16 suffix
   - Expected: x equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses u16 suffix")
val x = 1000u16
expect(x).to_equal(1000)
```

</details>

#### parses u32 suffix

- parses u32 suffix
   - Expected: x equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses u32 suffix")
val x = 12345u32
expect(x).to_equal(12345)
```

</details>

### Integer Literals - Mixed Formats

#### combining formats

#### combines decimal and hex

- combines decimal and hex
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines decimal and hex")
val result = 10 + 0xA
expect(result).to_equal(20)
```

</details>

#### combines decimal and binary

- combines decimal and binary
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines decimal and binary")
val result = 5 + 0b101
expect(result).to_equal(10)
```

</details>

#### combines all formats

- combines all formats
   - Expected: result equals `46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines all formats")
val result = 1 + 0xF + 0b1111 + 0o17
expect(result).to_equal(46)
```

</details>

### Integer Literals - Edge Cases

#### with zero

#### parses decimal zero

- parses decimal zero
   - Expected: x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses decimal zero")
val x = 0
expect(x).to_equal(0)
```

</details>

#### parses hex zero

- parses hex zero
   - Expected: x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses hex zero")
val x = 0x0
expect(x).to_equal(0)
```

</details>

#### parses binary zero

- parses binary zero
   - Expected: x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses binary zero")
val x = 0b0
expect(x).to_equal(0)
```

</details>

#### parses octal zero

- parses octal zero
   - Expected: x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses octal zero")
val x = 0o0
expect(x).to_equal(0)
```

</details>

#### with one

#### parses decimal one

- parses decimal one
   - Expected: x equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses decimal one")
val x = 1
expect(x).to_equal(1)
```

</details>

#### parses hex one

- parses hex one
   - Expected: x equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses hex one")
val x = 0x1
expect(x).to_equal(1)
```

</details>

#### parses binary one

- parses binary one
   - Expected: x equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses binary one")
val x = 0b1
expect(x).to_equal(1)
```

</details>

#### parses octal one

- parses octal one
   - Expected: x equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses octal one")
val x = 0o1
expect(x).to_equal(1)
```

</details>

#### with maximum values

#### parses large decimal

- parses large decimal
   - Expected: x equals `2147483647`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses large decimal")
val x = 2147483647
expect(x).to_equal(2147483647)
```

</details>

#### parses large hex

- parses large hex
   - Expected: x equals `2147483647`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses large hex")
val x = 0x7FFFFFFF
expect(x).to_equal(2147483647)
```

</details>

### Integer Literals - Case Insensitivity

#### hex prefix case

#### accepts lowercase 0x

- accepts lowercase 0x
   - Expected: x equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts lowercase 0x")
val x = 0xff
expect(x).to_equal(255)
```

</details>

#### accepts uppercase 0X

- accepts uppercase 0X
   - Expected: x equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts uppercase 0X")
val x = 0XFF
expect(x).to_equal(255)
```

</details>

#### binary prefix case

#### accepts lowercase 0b

- accepts lowercase 0b
   - Expected: x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts lowercase 0b")
val x = 0b1010
expect(x).to_equal(10)
```

</details>

#### accepts uppercase 0B

- accepts uppercase 0B
   - Expected: x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts uppercase 0B")
val x = 0B1010
expect(x).to_equal(10)
```

</details>

#### octal prefix case

#### accepts lowercase 0o

- accepts lowercase 0o
   - Expected: x equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts lowercase 0o")
val x = 0o77
expect(x).to_equal(63)
```

</details>

#### accepts uppercase 0O

- accepts uppercase 0O
   - Expected: x equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts uppercase 0O")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d8e7a76c56522f3fe1b8dedfe74a64dd70d814f249cfe1fffc538d83d823813`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d8e7a76c56522f3fe1b8dedfe74a64dd70d814f249cfe1fffc538d83d823813`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d8e7a76c56522f3fe1b8dedfe74a64dd70d814f249cfe1fffc538d83d823813`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/basic_types_integer_literals_spec.spl
mirror: doc/06_spec/feature/usage/basic_types_integer_literals_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/basic_types_integer_literals_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/basic_types_integer_literals_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/basic_types_integer_literals_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 49 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/basic_types_integer_literals_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses single digit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/basic_types_integer_literals_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/basic_types_integer_literals_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multi-digit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
