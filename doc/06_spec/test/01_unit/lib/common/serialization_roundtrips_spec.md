# Serialization Roundtrips and Extended Branch Coverage Specification

> Roundtrip integration tests and extended branch coverage: detect_format, type tags, versioning, parse_int_safe, deep_equal, structural_hash

<!-- sdn-diagram:id=serialization_roundtrips_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serialization_roundtrips_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serialization_roundtrips_spec -> serialization
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serialization_roundtrips_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 86 | 86 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Roundtrips and Extended Branch Coverage Specification

Roundtrip integration tests and extended branch coverage: detect_format, type tags, versioning, parse_int_safe, deep_equal, structural_hash

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-ROUNDTRIPS |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/common/serialization_roundtrips_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Roundtrip integration tests and extended branch coverage:
- Varint, string, hex, version, type-tag roundtrips
- Extended tests for char_code_safe, write/read_varint, serialize_*, escape/unescape,
  detect_format, type tags, versioning, parse_int_safe, deep_equal, structural_hash

## Scenarios

### Serialization Roundtrips

#### varint roundtrips

#### roundtrips various values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [0, 1, 127, 128, 256, 1000, -1, -128, -1000]
var i = 0
while i < values.len():
    val encoded = write_varint(values[i])
    val decoded = read_varint(encoded, 0)
    expect(decoded.0).to_equal(values[i])
    i = i + 1
```

</details>

#### string escape roundtrips

#### roundtrips strings with all special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inputs = ["", "hello", "say \"hi\"", "a\\b", "line1\nline2", "col1\tcol2", "cr\rhere"]
var i = 0
while i < inputs.len():
    val roundtripped = unescape_string(escape_string(inputs[i]))
    expect(roundtripped).to_equal(inputs[i])
    i = i + 1
```

</details>

#### quote/unquote roundtrips

#### roundtrips text through quote and unquote

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inputs = ["", "simple", "with \"quotes\"", "with\nnewline"]
var i = 0
while i < inputs.len():
    val roundtripped = unquote_string(quote_string(inputs[i]))
    expect(roundtripped).to_equal(inputs[i])
    i = i + 1
```

</details>

#### hex roundtrips

#### roundtrips byte arrays through hex conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inputs = [[], [0], [255], [0, 127, 255], [16, 32, 48]]
var i = 0
while i < inputs.len():
    val roundtripped = hex_to_bytes(bytes_to_hex(inputs[i]))
    expect(deep_equal_list_int(inputs[i], roundtripped)).to_equal(true)
    i = i + 1
```

</details>

#### version roundtrips

#### roundtrips versioned data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = "[1, 2, 3]"
val versioned = add_version(data, 42)
expect(get_version(versioned)).to_equal(42)
expect(strip_version(versioned)).to_equal(data)
```

</details>

#### type tag roundtrips

#### roundtrips tagged data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = "inner content"
val tagged = tag_type(data, "CustomType")
expect(get_type_tag(tagged)).to_equal("CustomType")
expect(strip_type_tag(tagged)).to_equal(data)
```

</details>

### char_code_safe extended

#### returns correct codes for all lowercase letters

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

#### returns correct codes for all uppercase letters

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

#### returns correct codes for all digits

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

#### returns correct codes for remaining symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe(":")).to_equal(58)
expect(char_code_safe(";")).to_equal(59)
expect(char_code_safe("<")).to_equal(60)
expect(char_code_safe("=")).to_equal(61)
expect(char_code_safe(">")).to_equal(62)
expect(char_code_safe("?")).to_equal(63)
expect(char_code_safe("@")).to_equal(64)
expect(char_code_safe("[")).to_equal(91)
expect(char_code_safe("\\")).to_equal(92)
expect(char_code_safe("]")).to_equal(93)
expect(char_code_safe("^")).to_equal(94)
expect(char_code_safe("_")).to_equal(95)
expect(char_code_safe("`")).to_equal(96)
expect(char_code_safe("\{")).to_equal(123)
expect(char_code_safe("|")).to_equal(124)
expect(char_code_safe("\}")).to_equal(125)
expect(char_code_safe("~")).to_equal(126)
```

</details>

#### returns correct codes for whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("\n")).to_equal(10)
expect(char_code_safe("\t")).to_equal(9)
expect(char_code_safe("\r")).to_equal(13)
```

</details>

### char_from_code_safe extended

#### converts code 65 to A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_safe(65)).to_equal("A")
```

</details>

#### converts code 97 to a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_safe(97)).to_equal("a")
```

</details>

#### converts code 48 to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_safe(48)).to_equal("0")
```

</details>

### write_varint extended

#### encodes 128 as two bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(128)
expect(result.len()).to_equal(2)
```

</details>

#### encodes 16384 as three bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(16384)
expect(result.len()).to_equal(3)
```

</details>

#### encodes negative value with sign marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(-42)
expect(result[0]).to_equal(255)
expect(result.len()).to_be_greater_than(1)
```

</details>

#### roundtrips large positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(100000)
val decoded = read_varint(encoded, 0)
expect(decoded.0).to_equal(100000)
```

</details>

#### roundtrips large negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(-100000)
val decoded = read_varint(encoded, 0)
expect(decoded.0).to_equal(-100000)
```

</details>

### read_varint extended

#### reports consumed bytes for multi-byte varint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(1000)
val decoded = read_varint(encoded, 0)
expect(decoded.1).to_equal(encoded.len())
```

</details>

#### reads varint at non-zero offset

- bytes = bytes push
   - Expected: decoded.0 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes = [99]
val encoded = write_varint(42)
var i = 0
while i < encoded.len():
    bytes = bytes.push(encoded[i])
    i = i + 1
val decoded = read_varint(bytes, 1)
expect(decoded.0).to_equal(42)
```

</details>

#### reports consumed bytes for negative varint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(-50)
val decoded = read_varint(encoded, 0)
expect(decoded.1).to_equal(encoded.len())
```

</details>

### serialize_text_bytes extended

#### encodes empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_bytes("")
expect(result[0]).to_equal(type_text())
expect(result.len()).to_equal(2)
```

</details>

#### encodes single character

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_bytes("A")
expect(result[0]).to_equal(type_text())
val last = result[result.len() - 1]
expect(last).to_equal(65)
```

</details>

#### encodes multi-character text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_bytes("AB")
expect(result[0]).to_equal(type_text())
val second_last = result[result.len() - 2]
val last = result[result.len() - 1]
expect(second_last).to_equal(65)
expect(last).to_equal(66)
```

</details>

### escape_string extended

#### escapes double quote alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("\"")
expect(result).to_equal("\\\"")
```

</details>

#### escapes backslash alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("\\")
expect(result).to_equal("\\\\")
```

</details>

#### escapes tab alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("\t")
expect(result).to_equal("\\t")
```

</details>

#### escapes carriage return alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("\r")
expect(result).to_equal("\\r")
```

</details>

#### does not escape normal chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("abc")
expect(result).to_equal("abc")
```

</details>

### unescape_string extended

#### unescapes backslash-quote alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("\\\"")
expect(result).to_equal("\"")
```

</details>

#### unescapes backslash-backslash alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("\\\\")
expect(result).to_equal("\\")
```

</details>

#### handles unknown escape code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("\\x")
expect(result).to_equal("\\x")
```

</details>

#### handles trailing backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("abc\\")
expect(result).to_equal("abc\\")
```

</details>

#### handles multiple escapes in sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("\\n\\t\\r")
expect(result).to_equal("\n\t\r")
```

</details>

### unquote_string extended

#### returns single char unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("x")
expect(result).to_equal("x")
```

</details>

#### returns non-quoted two-char string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("ab")
expect(result).to_equal("ab")
```

</details>

#### unquotes minimal quoted string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("\"\"")
expect(result).to_equal("")
```

</details>

### serialize_int_bytes extended

#### serializes large positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_bytes(100000)
expect(result[0]).to_equal(type_int())
expect(result.len()).to_be_greater_than(2)
```

</details>

#### serializes large negative integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_bytes(-100000)
expect(result[0]).to_equal(type_int())
```

</details>

### serialize_bool_bytes extended

#### has exactly two bytes for true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_bool_bytes(true)
expect(result.len()).to_equal(2)
```

</details>

#### has exactly two bytes for false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_bool_bytes(false)
expect(result.len()).to_equal(2)
```

</details>

### detect_format extended

#### returns unknown for tuple starting with paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("(1, 2)")).to_equal("unknown")
```

</details>

#### detects sdn for negative number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("-42")).to_equal("sdn")
```

</details>

#### returns unknown for single special char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("~")).to_equal("unknown")
```

</details>

### is_valid_sdn extended

#### returns true for numeric string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("42")).to_equal(true)
```

</details>

#### returns true for quoted text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("\"hello\"")).to_equal(true)
```

</details>

#### returns false for single char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("x")).to_equal(false)
```

</details>

### get_type_tag extended

#### extracts single char tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("@X\{v\}")
expect(result).to_equal("X")
```

</details>

#### extracts long tag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("@VeryLongTypeName\{v\}")
expect(result).to_equal("VeryLongTypeName")
```

</details>

#### returns nil for at-sign only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("@ab")
expect(result).to_be_nil()
```

</details>

### strip_type_tag extended

#### strips single char tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("@X\{hello\}")
expect(result).to_equal("hello")
```

</details>

#### strips tag with empty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("@T\{\}")
expect(result).to_equal("")
```

</details>

### get_version extended

#### extracts single digit version

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versioned = add_version("x", 1)
val result = get_version(versioned)
expect(result).to_equal(1)
```

</details>

#### extracts multi-digit version

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versioned = add_version("x", 99)
val result = get_version(versioned)
expect(result).to_equal(99)
```

</details>

### strip_version extended

#### strips version with complex data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versioned = add_version("[1, 2, 3]", 10)
val result = strip_version(versioned)
expect(result).to_equal("[1, 2, 3]")
```

</details>

#### strips version with text data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versioned = add_version("\"hello\"", 2)
val result = strip_version(versioned)
expect(result).to_equal("\"hello\"")
```

</details>

### parse_int_safe extended

#### parses single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("5")).to_equal(5)
```

</details>

#### parses large number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("12345")).to_equal(12345)
```

</details>

#### parses negative with digits after

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("-123")).to_equal(-123)
```

</details>

#### stops at first non-digit in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("5abc3")).to_equal(5)
```

</details>

### digit_to_hex extended

#### covers all low digits via int_to_hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(0)).to_equal("00")
expect(int_to_hex(1)).to_equal("01")
expect(int_to_hex(2)).to_equal("02")
expect(int_to_hex(3)).to_equal("03")
expect(int_to_hex(4)).to_equal("04")
expect(int_to_hex(5)).to_equal("05")
expect(int_to_hex(6)).to_equal("06")
expect(int_to_hex(7)).to_equal("07")
expect(int_to_hex(8)).to_equal("08")
expect(int_to_hex(9)).to_equal("09")
expect(int_to_hex(10)).to_equal("0a")
expect(int_to_hex(11)).to_equal("0b")
expect(int_to_hex(12)).to_equal("0c")
expect(int_to_hex(13)).to_equal("0d")
expect(int_to_hex(14)).to_equal("0e")
expect(int_to_hex(15)).to_equal("0f")
```

</details>

#### covers all high digits via int_to_hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(16)).to_equal("10")
expect(int_to_hex(32)).to_equal("20")
expect(int_to_hex(160)).to_equal("a0")
expect(int_to_hex(176)).to_equal("b0")
expect(int_to_hex(192)).to_equal("c0")
expect(int_to_hex(208)).to_equal("d0")
expect(int_to_hex(224)).to_equal("e0")
expect(int_to_hex(240)).to_equal("f0")
```

</details>

### hex_to_digit extended

#### converts all lowercase hex digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_bytes("0a0b0c0d0e0f")
expect(result[0]).to_equal(10)
expect(result[1]).to_equal(11)
expect(result[2]).to_equal(12)
expect(result[3]).to_equal(13)
expect(result[4]).to_equal(14)
expect(result[5]).to_equal(15)
```

</details>

#### converts all uppercase hex digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_bytes("0A0B0C0D0E0F")
expect(result[0]).to_equal(10)
expect(result[1]).to_equal(11)
expect(result[2]).to_equal(12)
expect(result[3]).to_equal(13)
expect(result[4]).to_equal(14)
expect(result[5]).to_equal(15)
```

</details>

#### converts all numeric digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_bytes("000102030405060708090a")
expect(result[0]).to_equal(0)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(2)
expect(result[3]).to_equal(3)
expect(result[4]).to_equal(4)
expect(result[5]).to_equal(5)
```

</details>

### deep_equal extended

#### detects mismatch at last position in int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([1, 2, 3], [1, 2, 4])).to_equal(false)
```

</details>

#### detects mismatch at first position in int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([9, 2, 3], [1, 2, 3])).to_equal(false)
```

</details>

#### detects mismatch in single element text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_text(["a"], ["b"])).to_equal(false)
```

</details>

#### compares long equal int lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([1, 2, 3, 4, 5], [1, 2, 3, 4, 5])).to_equal(true)
```

</details>

#### compares long equal text lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_text(["a", "b", "c"], ["a", "b", "c"])).to_equal(true)
```

</details>

### structural_hash extended

#### hashes zero integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_int(0)
expect(h).to_equal(0)
```

</details>

#### hashes small positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_int(1)
expect(h == 0).to_equal(false)
```

</details>

#### hashes negative integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_int(-1)
expect(h == 0).to_equal(false)
```

</details>

#### hashes single-element int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_list_int([1])
expect(h == 0).to_equal(false)
```

</details>

#### combines two small hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = combine_hashes(1, 2)
expect(h).to_equal(33)
```

</details>

### is_numeric_text extended

#### returns true for large negative number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("-99999")).to_equal(true)
```

</details>

#### returns false for negative with non-digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("-12a")).to_equal(false)
```

</details>

#### returns false for decimal point

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("3.14")).to_equal(false)
```

</details>

### write_bytes extended

#### writes large byte array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val result = write_bytes(input)
expect(result[0]).to_equal(10)
expect(result.len()).to_equal(11)
```

</details>

### read_bytes extended

#### reads from middle of array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [10, 20, 30, 40, 50]
val result = read_bytes(bytes, 2, 2)
val data = result.0
expect(data.len()).to_equal(2)
expect(data[0]).to_equal(30)
expect(data[1]).to_equal(40)
```

</details>

#### reads single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_bytes([99], 0, 1)
val data = result.0
expect(data.len()).to_equal(1)
expect(data[0]).to_equal(99)
```

</details>

### Compression Markers extended

#### marks and detects long content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marked = mark_compressed("a long piece of content here")
expect(is_compressed(marked)).to_equal(true)
```

</details>

#### returns false for encrypted marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encrypted = mark_encrypted("secret")
expect(is_compressed(encrypted)).to_equal(false)
```

</details>

### Encryption Markers extended

#### marks and detects long content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marked = mark_encrypted("a long piece of content here")
expect(is_encrypted(marked)).to_equal(true)
```

</details>

#### returns false for compressed marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = mark_compressed("stuff")
expect(is_encrypted(compressed)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 86 |
| Active scenarios | 86 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
