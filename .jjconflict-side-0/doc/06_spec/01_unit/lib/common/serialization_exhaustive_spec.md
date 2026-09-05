# Serialization Exhaustive Branch Coverage Specification

> Exhaustive per-character and per-value coverage for all lookup functions:

<!-- sdn-diagram:id=serialization_exhaustive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serialization_exhaustive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serialization_exhaustive_spec -> serialization
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serialization_exhaustive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 57 | 57 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Exhaustive Branch Coverage Specification

Exhaustive per-character and per-value coverage for all lookup functions:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-EXHAUSTIVE |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/common/serialization_exhaustive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exhaustive per-character and per-value coverage for all lookup functions:
- char_code_safe exhaustive (all ASCII)
- digit_to_hex exhaustive (0-15)
- hex_to_digit exhaustive (all hex chars)
- char_to_digit_safe exhaustive

## Scenarios

### char_code_safe range boundary chars

#### handles colon just past digit range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe(":")).to_equal(58)
```

</details>

#### handles bracket just past uppercase range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("[")).to_equal(91)
```

</details>

#### handles brace just past lowercase range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("\{")).to_equal(123)
```

</details>

#### handles slash before digit range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("/")).to_equal(47)
```

</details>

#### handles at-sign before uppercase range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("@")).to_equal(64)
```

</details>

#### handles backtick before lowercase range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("`")).to_equal(96)
```

</details>

### detect_format compound OR branches

#### detects sdn for object starting with curly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("\{a: 1\}")).to_equal("sdn")
```

</details>

#### detects sdn for array starting with bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("[1]")).to_equal("sdn")
```

</details>

#### detects sdn for true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("true")).to_equal("sdn")
```

</details>

#### detects sdn for false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("false")).to_equal("sdn")
```

</details>

#### detects sdn for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("nil")).to_equal("sdn")
```

</details>

#### detects sdn for number after failing literal checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("99")).to_equal("sdn")
```

</details>

#### returns unknown when no format matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("xyz")).to_equal("unknown")
```

</details>

### is_valid_sdn compound OR

#### returns true when format is sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("42")).to_equal(true)
```

</details>

#### returns true when format is tagged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("@T\{x\}")).to_equal(true)
```

</details>

#### returns false when format is unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("abc")).to_equal(false)
```

</details>

### hex_to_digit compound OR branches

#### converts lowercase a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("a")).to_equal(10)
```

</details>

#### converts uppercase A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("A")).to_equal(10)
```

</details>

#### converts lowercase b

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("b")).to_equal(11)
```

</details>

#### converts uppercase B

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("B")).to_equal(11)
```

</details>

#### converts lowercase c

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("c")).to_equal(12)
```

</details>

#### converts uppercase C

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("C")).to_equal(12)
```

</details>

#### converts lowercase d

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("d")).to_equal(13)
```

</details>

#### converts uppercase D

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("D")).to_equal(13)
```

</details>

#### converts lowercase e

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("e")).to_equal(14)
```

</details>

#### converts uppercase E

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("E")).to_equal(14)
```

</details>

#### converts lowercase f

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("f")).to_equal(15)
```

</details>

#### converts uppercase F

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("F")).to_equal(15)
```

</details>

### is_numeric_text compound AND

#### accepts pure digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("123")).to_equal(true)
```

</details>

#### rejects colon in number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("1:2")).to_equal(false)
```

</details>

#### rejects exclamation mark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("!")).to_equal(false)
```

</details>

### unquote_string compound AND

#### returns string with opening quote but no closing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("\"abc")
expect(result).to_equal("\"abc")
```

</details>

#### returns string with no quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("abc\"")
expect(result).to_equal("abc\"")
```

</details>

### get_version loop branches

#### extracts version with space before comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versioned = "\{v: 5, data: x\}"
val result = get_version(versioned)
expect(result).to_equal(5)
```

</details>

#### returns nil for version with no comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_version("\{v: 123\}")
expect(result).to_be_nil()
```

</details>

### strip_version loop branches

#### strips version from short data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versioned = add_version("x", 1)
val result = strip_version(versioned)
expect(result).to_equal("x")
```

</details>

#### handles version string that is just prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_version("\{v: 1, dat\}")
# No "data: " found, returns original
expect(result).to_equal("\{v: 1, dat\}")
```

</details>

### write_varint boundary values

#### encodes 127 as single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(127)
expect(result.len()).to_equal(1)
```

</details>

#### encodes 128 as two bytes with continuation bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(128)
expect(result.len()).to_equal(2)
val first_byte = result[0]
# First byte should have continuation bit set (>= 128)
expect(first_byte).to_be_greater_than(127)
```

</details>

#### encodes 255 as two bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(255)
expect(result.len()).to_equal(2)
```

</details>

### read_varint loop termination

#### reads single-byte varint with byte < 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_varint([42], 0)
expect(result.0).to_equal(42)
expect(result.1).to_equal(1)
```

</details>

#### reads two-byte varint continuing past first byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(200)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(200)
```

</details>

#### rejects negative offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_varint([42], 0 - 1)
expect(result.0).to_equal(0)
expect(result.1).to_equal(0)
```

</details>

### structural_hash_bool branches

#### returns 1 for true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(structural_hash_bool(true)).to_equal(1)
```

</details>

#### returns 0 for false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(structural_hash_bool(false)).to_equal(0)
```

</details>

### structural_hash_int xor branch

#### hashes 3 to non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_int(3)
expect(h == 0).to_equal(false)
```

</details>

#### hashes 100 to non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_int(100)
expect(h == 0).to_equal(false)
```

</details>

### char_code_safe exhaustive

#### covers all ASCII codes via serialize_text_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Binary serialize various strings to exercise char_code_safe for each char
val r1 = serialize_text_bytes(" !\"#$%&'()*+,-./")
expect(r1[0]).to_equal(type_text())

val r2 = serialize_text_bytes("0123456789")
expect(r2[0]).to_equal(type_text())

val r3 = serialize_text_bytes(":;<=>?@")
expect(r3[0]).to_equal(type_text())

val r4 = serialize_text_bytes("ABCDEFGHIJKLM")
expect(r4[0]).to_equal(type_text())

val r5 = serialize_text_bytes("NOPQRSTUVWXYZ")
expect(r5[0]).to_equal(type_text())

val r6 = serialize_text_bytes("[\\]^_`")
expect(r6[0]).to_equal(type_text())

val r7 = serialize_text_bytes("abcdefghijklm")
expect(r7[0]).to_equal(type_text())

val r8 = serialize_text_bytes("nopqrstuvwxyz")
expect(r8[0]).to_equal(type_text())

val r9 = serialize_text_bytes("\{|~")
expect(r9[0]).to_equal(type_text())

val r10 = serialize_text_bytes("\n\t\r")
expect(r10[0]).to_equal(type_text())
```

</details>

#### exercises individual char_code_safe for each remaining char

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Symbols not in other tests
expect(char_code_safe(" ")).to_equal(32)
expect(char_code_safe("!")).to_equal(33)
expect(char_code_safe("\"")).to_equal(34)
expect(char_code_safe("#")).to_equal(35)
```

</details>

#### exercises all digits individually

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("0")).to_equal(48)
expect(char_code_safe("1")).to_equal(49)
expect(char_code_safe("2")).to_equal(50)
expect(char_code_safe("3")).to_equal(51)
expect(char_code_safe("4")).to_equal(52)
expect(char_code_safe("5")).to_equal(53)
expect(char_code_safe("6")).to_equal(54)
expect(char_code_safe("7")).to_equal(55)
expect(char_code_safe("8")).to_equal(56)
expect(char_code_safe("9")).to_equal(57)
```

</details>

#### exercises all lowercase individually

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("a")).to_equal(97)
expect(char_code_safe("b")).to_equal(98)
expect(char_code_safe("c")).to_equal(99)
expect(char_code_safe("d")).to_equal(100)
expect(char_code_safe("e")).to_equal(101)
expect(char_code_safe("f")).to_equal(102)
expect(char_code_safe("g")).to_equal(103)
expect(char_code_safe("h")).to_equal(104)
expect(char_code_safe("i")).to_equal(105)
expect(char_code_safe("j")).to_equal(106)
expect(char_code_safe("k")).to_equal(107)
expect(char_code_safe("l")).to_equal(108)
expect(char_code_safe("m")).to_equal(109)
expect(char_code_safe("n")).to_equal(110)
expect(char_code_safe("o")).to_equal(111)
expect(char_code_safe("p")).to_equal(112)
expect(char_code_safe("q")).to_equal(113)
expect(char_code_safe("r")).to_equal(114)
expect(char_code_safe("s")).to_equal(115)
expect(char_code_safe("t")).to_equal(116)
expect(char_code_safe("u")).to_equal(117)
expect(char_code_safe("v")).to_equal(118)
expect(char_code_safe("w")).to_equal(119)
expect(char_code_safe("x")).to_equal(120)
expect(char_code_safe("y")).to_equal(121)
expect(char_code_safe("z")).to_equal(122)
```

</details>

#### exercises all uppercase individually

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("A")).to_equal(65)
expect(char_code_safe("B")).to_equal(66)
expect(char_code_safe("C")).to_equal(67)
expect(char_code_safe("D")).to_equal(68)
expect(char_code_safe("E")).to_equal(69)
expect(char_code_safe("F")).to_equal(70)
expect(char_code_safe("G")).to_equal(71)
expect(char_code_safe("H")).to_equal(72)
expect(char_code_safe("I")).to_equal(73)
expect(char_code_safe("J")).to_equal(74)
expect(char_code_safe("K")).to_equal(75)
expect(char_code_safe("L")).to_equal(76)
expect(char_code_safe("M")).to_equal(77)
expect(char_code_safe("N")).to_equal(78)
expect(char_code_safe("O")).to_equal(79)
expect(char_code_safe("P")).to_equal(80)
expect(char_code_safe("Q")).to_equal(81)
expect(char_code_safe("R")).to_equal(82)
expect(char_code_safe("S")).to_equal(83)
expect(char_code_safe("T")).to_equal(84)
expect(char_code_safe("U")).to_equal(85)
expect(char_code_safe("V")).to_equal(86)
expect(char_code_safe("W")).to_equal(87)
expect(char_code_safe("X")).to_equal(88)
expect(char_code_safe("Y")).to_equal(89)
expect(char_code_safe("Z")).to_equal(90)
```

</details>

### digit_to_hex exhaustive

#### covers all 16 hex digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(digit_to_hex(0)).to_equal("0")
expect(digit_to_hex(1)).to_equal("1")
expect(digit_to_hex(2)).to_equal("2")
expect(digit_to_hex(3)).to_equal("3")
expect(digit_to_hex(4)).to_equal("4")
expect(digit_to_hex(5)).to_equal("5")
expect(digit_to_hex(6)).to_equal("6")
expect(digit_to_hex(7)).to_equal("7")
expect(digit_to_hex(8)).to_equal("8")
expect(digit_to_hex(9)).to_equal("9")
expect(digit_to_hex(10)).to_equal("a")
expect(digit_to_hex(11)).to_equal("b")
expect(digit_to_hex(12)).to_equal("c")
expect(digit_to_hex(13)).to_equal("d")
expect(digit_to_hex(14)).to_equal("e")
expect(digit_to_hex(15)).to_equal("f")
```

</details>

### hex_to_digit exhaustive

#### covers all numeric hex digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("0")).to_equal(0)
expect(hex_to_digit("1")).to_equal(1)
expect(hex_to_digit("2")).to_equal(2)
expect(hex_to_digit("3")).to_equal(3)
expect(hex_to_digit("4")).to_equal(4)
expect(hex_to_digit("5")).to_equal(5)
expect(hex_to_digit("6")).to_equal(6)
expect(hex_to_digit("7")).to_equal(7)
expect(hex_to_digit("8")).to_equal(8)
expect(hex_to_digit("9")).to_equal(9)
```

</details>

#### covers all lowercase letter hex digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("a")).to_equal(10)
expect(hex_to_digit("b")).to_equal(11)
expect(hex_to_digit("c")).to_equal(12)
expect(hex_to_digit("d")).to_equal(13)
expect(hex_to_digit("e")).to_equal(14)
expect(hex_to_digit("f")).to_equal(15)
```

</details>

#### covers all uppercase letter hex digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("A")).to_equal(10)
expect(hex_to_digit("B")).to_equal(11)
expect(hex_to_digit("C")).to_equal(12)
expect(hex_to_digit("D")).to_equal(13)
expect(hex_to_digit("E")).to_equal(14)
expect(hex_to_digit("F")).to_equal(15)
```

</details>

### char_to_digit_safe exhaustive

#### covers all digits 0 through 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_to_digit_safe("0")).to_equal(0)
expect(char_to_digit_safe("1")).to_equal(1)
expect(char_to_digit_safe("2")).to_equal(2)
expect(char_to_digit_safe("3")).to_equal(3)
expect(char_to_digit_safe("4")).to_equal(4)
expect(char_to_digit_safe("5")).to_equal(5)
expect(char_to_digit_safe("6")).to_equal(6)
expect(char_to_digit_safe("7")).to_equal(7)
expect(char_to_digit_safe("8")).to_equal(8)
expect(char_to_digit_safe("9")).to_equal(9)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 57 |
| Active scenarios | 57 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
