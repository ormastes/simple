# Serialization Primitives Coverage Specification

> Branch-coverage tests for serialization primitives:

<!-- sdn-diagram:id=serialization_primitives_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serialization_primitives_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serialization_primitives_spec -> serialization
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serialization_primitives_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Primitives Coverage Specification

Branch-coverage tests for serialization primitives:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-PRIMITIVES |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/common/serialization_primitives_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch-coverage tests for serialization primitives:
- Type constants (types.spl)
- char_code_safe, varint encoding (serialize.spl)
- Binary and text serialization of primitives and collections (serialize.spl)
- String escaping/quoting/unquoting (serialize.spl)

## Scenarios

### Type Constants

#### returns correct values for all type tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(type_nil()).to_equal(0)
expect(type_bool()).to_equal(1)
expect(type_int()).to_equal(2)
expect(type_float()).to_equal(3)
expect(type_text()).to_equal(4)
expect(type_list()).to_equal(5)
expect(type_tuple()).to_equal(6)
expect(type_dict()).to_equal(7)
expect(type_custom()).to_equal(8)
```

</details>

### char_code_safe

#### printable symbols

#### returns correct code for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe(" ")).to_equal(32)
```

</details>

#### returns correct code for exclamation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("!")).to_equal(33)
```

</details>

#### returns correct code for double quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("\"")).to_equal(34)
```

</details>

#### returns correct code for hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("#")).to_equal(35)
```

</details>

#### returns correct code for various symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("$")).to_equal(36)
expect(char_code_safe("%")).to_equal(37)
expect(char_code_safe("&")).to_equal(38)
expect(char_code_safe("'")).to_equal(39)
expect(char_code_safe("(")).to_equal(40)
expect(char_code_safe(")")).to_equal(41)
expect(char_code_safe("*")).to_equal(42)
expect(char_code_safe("+")).to_equal(43)
expect(char_code_safe(",")).to_equal(44)
expect(char_code_safe("-")).to_equal(45)
expect(char_code_safe(".")).to_equal(46)
expect(char_code_safe("/")).to_equal(47)
```

</details>

#### digits

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

#### punctuation after digits

#### returns correct codes for colon through at-sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe(":")).to_equal(58)
expect(char_code_safe(";")).to_equal(59)
expect(char_code_safe("<")).to_equal(60)
expect(char_code_safe("=")).to_equal(61)
expect(char_code_safe(">")).to_equal(62)
expect(char_code_safe("@")).to_equal(64)
```

</details>

#### uppercase letters

#### returns correct codes for A-Z range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("A")).to_equal(65)
expect(char_code_safe("M")).to_equal(77)
expect(char_code_safe("Z")).to_equal(90)
```

</details>

#### lowercase letters

#### returns correct codes for a-z range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("a")).to_equal(97)
expect(char_code_safe("m")).to_equal(109)
expect(char_code_safe("z")).to_equal(122)
```

</details>

#### bracket and brace characters

#### returns correct codes for brackets and braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("[")).to_equal(91)
expect(char_code_safe("\\")).to_equal(92)
expect(char_code_safe("]")).to_equal(93)
expect(char_code_safe("^")).to_equal(94)
expect(char_code_safe("_")).to_equal(95)
expect(char_code_safe("`")).to_equal(96)
expect(char_code_safe("{")).to_equal(123)
expect(char_code_safe("|")).to_equal(124)
expect(char_code_safe("}")).to_equal(125)
expect(char_code_safe("~")).to_equal(126)
```

</details>

#### whitespace characters

#### returns correct codes for newline tab and carriage return

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

#### fallback for unknown characters

#### returns 0 for unrecognized input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Empty string or non-ASCII falls through to default 0
expect(char_code_safe("")).to_equal(0)
```

</details>

### write_varint

#### when value is zero

#### returns single byte zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(0)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(0)
```

</details>

#### when value is positive and small

#### encodes small positive as single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(42)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(42)
```

</details>

#### when value is positive and large

#### encodes values above 127 as multi-byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(300)
expect(result.len()).to_be_greater_than(1)
```

</details>

#### when value is negative

#### prepends 255 sign marker

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

### read_varint

#### roundtrip with zero

#### decodes zero correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(0)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(0)
```

</details>

#### roundtrip with positive

#### decodes positive correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(42)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(42)
```

</details>

#### roundtrip with large positive

#### decodes multi-byte positive correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(300)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(300)
```

</details>

#### roundtrip with negative

#### decodes negative correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(-42)
val result = read_varint(encoded, 0)
expect(result.0).to_equal(-42)
```

</details>

#### consumed bytes count

#### reports correct number of consumed bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = write_varint(42)
val result = read_varint(encoded, 0)
expect(result.1).to_equal(encoded.len())
```

</details>

### serialize_int_bytes

#### starts with int type tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_bytes(0)
expect(result[0]).to_equal(type_int())
```

</details>

#### serializes zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_bytes(0)
expect(result.len()).to_be_greater_than(1)
```

</details>

#### serializes positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_bytes(100)
expect(result[0]).to_equal(type_int())
expect(result.len()).to_be_greater_than(1)
```

</details>

#### serializes negative integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_bytes(-50)
expect(result[0]).to_equal(type_int())
```

</details>

### serialize_bool_bytes

#### serializes true with type tag and 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_bool_bytes(true)
expect(result[0]).to_equal(type_bool())
expect(result[1]).to_equal(1)
```

</details>

#### serializes false with type tag and 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_bool_bytes(false)
expect(result[0]).to_equal(type_bool())
expect(result[1]).to_equal(0)
```

</details>

### serialize_nil_bytes

#### returns single byte with nil type tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_nil_bytes()
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(type_nil())
```

</details>

### serialize_text_bytes

#### serializes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_bytes("")
expect(result[0]).to_equal(type_text())
```

</details>

#### serializes non-empty string with correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_bytes("abc")
expect(result[0]).to_equal(type_text())
expect(result.len()).to_be_greater_than(1)
```

</details>

#### serializes string with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_bytes("a\nb")
expect(result[0]).to_equal(type_text())
```

</details>

### escape_string

#### escapes double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("say \"hi\"")
expect(result).to_contain("\\\"")
```

</details>

#### escapes backslashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("path\\to")
expect(result).to_contain("\\\\")
```

</details>

#### escapes newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("a\nb")
expect(result).to_contain("\\n")
```

</details>

#### escapes tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("a\tb")
expect(result).to_contain("\\t")
```

</details>

#### escapes carriage returns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("a\rb")
expect(result).to_contain("\\r")
```

</details>

#### passes through normal characters unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("hello")
expect(result).to_equal("hello")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_string("")
expect(result).to_equal("")
```

</details>

### unescape_string

#### unescapes backslash-quote to quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("say \\\"hi\\\"")
expect(result).to_contain("\"")
```

</details>

#### unescapes backslash-backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("path\\\\to")
expect(result).to_contain("\\")
```

</details>

#### unescapes backslash-n to newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("a\\nb")
expect(result).to_contain("\n")
```

</details>

#### unescapes backslash-t to tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("a\\tb")
expect(result).to_contain("\t")
```

</details>

#### unescapes backslash-r to carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("a\\rb")
expect(result).to_contain("\r")
```

</details>

#### handles unknown escape sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("a\\xb")
expect(result).to_equal("a\\xb")
```

</details>

#### handles trailing backslash at end of string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("abc\\")
expect(result).to_equal("abc\\")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unescape_string("")
expect(result).to_equal("")
```

</details>

#### roundtrips with escape_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "say \"hi\"\npath\\to\ttab\rreturn"
val roundtripped = unescape_string(escape_string(original))
expect(roundtripped).to_equal(original)
```

</details>

### quote_string

#### wraps string in double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_string("hello")
expect(result).to_start_with("\"")
expect(result).to_end_with("\"")
```

</details>

#### escapes inner content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quote_string("say \"hi\"")
expect(result).to_start_with("\"")
expect(result).to_end_with("\"")
expect(result).to_contain("\\\"")
```

</details>

### unquote_string

#### removes quotes and unescapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("\"hello\"")
expect(result).to_equal("hello")
```

</details>

#### returns input unchanged for short strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("x")
expect(result).to_equal("x")
```

</details>

#### returns input unchanged when not quoted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("hello")
expect(result).to_equal("hello")
```

</details>

#### returns empty input unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unquote_string("")
expect(result).to_equal("")
```

</details>

#### roundtrips with quote_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "hello world"
val roundtripped = unquote_string(quote_string(original))
expect(roundtripped).to_equal(original)
```

</details>

### serialize_int

#### serializes positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_int(42)).to_equal("42")
```

</details>

#### serializes zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_int(0)).to_equal("0")
```

</details>

#### serializes negative integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_int(-7)).to_equal("-7")
```

</details>

### serialize_bool

#### serializes true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_bool(true)).to_equal("true")
```

</details>

#### serializes false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_bool(false)).to_equal("false")
```

</details>

### serialize_nil

#### returns nil string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_nil()).to_equal("nil")
```

</details>

### serialize_text

#### quotes and escapes text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### escapes special characters in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text("a\nb")
expect(result).to_contain("\\n")
```

</details>

### serialize_list

#### serializes empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_list([])
expect(result).to_equal("[]")
```

</details>

#### serializes single-item list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_list(["42"])
expect(result).to_equal("[42]")
```

</details>

#### serializes multi-item list with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_list(["1", "2", "3"])
expect(result).to_equal("[1, 2, 3]")
```

</details>

### serialize_tuple_text

#### serializes empty tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_tuple_text([])
expect(result).to_equal("()")
```

</details>

#### serializes single-value tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_tuple_text(["42"])
expect(result).to_equal("(42)")
```

</details>

#### serializes multi-value tuple with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_tuple_text(["1", "2", "3"])
expect(result).to_equal("(1, 2, 3)")
```

</details>

### serialize_dict

#### serializes empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_dict([])
expect(result).to_equal("{}")
```

</details>

#### serializes single entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_dict([("key", "val")])
expect(result).to_equal("{key: val}")
```

</details>

#### serializes multiple entries with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_dict([("a", "1"), ("b", "2")])
expect(result).to_equal("{a: 1, b: 2}")
```

</details>

### serialize_int_list

#### serializes empty int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_list([])
expect(result).to_equal("[]")
```

</details>

#### serializes non-empty int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_list([1, 2, 3])
expect(result).to_equal("[1, 2, 3]")
```

</details>

### serialize_text_list

#### serializes empty text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_list([])
expect(result).to_equal("[]")
```

</details>

#### serializes non-empty text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_list(["a", "b"])
expect(result).to_equal("[\"a\", \"b\"]")
```

</details>

### serialize_bool_list

#### serializes empty bool list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_bool_list([])
expect(result).to_equal("[]")
```

</details>

#### serializes non-empty bool list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_bool_list([true, false, true])
expect(result).to_equal("[true, false, true]")
```

</details>

### serialize_int_list_bytes

#### starts with list type tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_list_bytes([1, 2])
expect(result[0]).to_equal(type_list())
```

</details>

#### serializes empty int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_list_bytes([])
expect(result[0]).to_equal(type_list())
```

</details>

### serialize_text_list_bytes

#### starts with list type tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_list_bytes(["hello"])
expect(result[0]).to_equal(type_list())
```

</details>

#### serializes empty text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_list_bytes([])
expect(result[0]).to_equal(type_list())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
