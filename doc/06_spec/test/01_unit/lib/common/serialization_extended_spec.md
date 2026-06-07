# Serialization Extended Edge Cases Coverage Specification

> Extended edge-case and additional branch coverage:

<!-- sdn-diagram:id=serialization_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serialization_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serialization_extended_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serialization_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 153 | 153 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Extended Edge Cases Coverage Specification

Extended edge-case and additional branch coverage:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-EXTENDED |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Blocked — std.common.serialization has no .spl source (only empty .smf stubs). |
| Source | `test/01_unit/lib/common/serialization_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Extended edge-case and additional branch coverage:
- Compression/encryption markers extended
- Pretty print, collections, binary list, SDN conversions extended
- Schema and validation edge cases
- is_numeric_text, type tag, version, parse_int_safe, char_to_digit_safe edge cases
- Compound condition branch coverage for detect_format, is_valid_sdn, hex_to_digit

## Scenarios

### pretty_print extended

#### pretty prints nested list at indent 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_list(["inner"], 2)
expect(result).to_start_with("[\n")
expect(result).to_contain("inner")
```

</details>

#### pretty prints nested tuple at indent 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_tuple(["a", "b", "c"], 1)
expect(result).to_start_with("(\n")
expect(result).to_contain(",")
```

</details>

#### pretty prints nested dict at indent 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_dict([("x", "1"), ("y", "2"), ("z", "3")], 1)
expect(result).to_start_with("{\n")
expect(result).to_contain(",")
```

</details>

#### indents at level 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_print_indent("test", 3)
expect(result).to_equal("      test")
```

</details>

### serialize collections extended

#### serializes four-item list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_list(["a", "b", "c", "d"])
expect(result).to_equal("[a, b, c, d]")
```

</details>

#### serializes three-value tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_tuple_text(["x", "y", "z"])
expect(result).to_equal("(x, y, z)")
```

</details>

#### serializes three-entry dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_dict([("a", "1"), ("b", "2"), ("c", "3")])
expect(result).to_equal("\{a: 1, b: 2, c: 3\}")
```

</details>

#### serializes int list with negative values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_list([-1, 0, 1])
expect(result).to_equal("[-1, 0, 1]")
```

</details>

#### serializes text list with special chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_list(["hello world"])
expect(result).to_contain("hello world")
```

</details>

#### serializes bool list with single item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_bool_list([true])
expect(result).to_equal("[true]")
```

</details>

### binary list serialization extended

#### encodes non-empty int list bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_list_bytes([10, 20])
expect(result[0]).to_equal(type_list())
expect(result.len()).to_be_greater_than(3)
```

</details>

#### encodes non-empty text list bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_list_bytes(["hi"])
expect(result[0]).to_equal(type_list())
expect(result.len()).to_be_greater_than(2)
```

</details>

### SDN conversions extended

#### converts large negative integer to SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_int(-999)).to_equal("-999")
```

</details>

#### converts list with three items

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_list(["a", "b", "c"])).to_equal("[a, b, c]")
```

</details>

#### converts tuple with three items

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_tuple(["1", "2", "3"])).to_equal("(1, 2, 3)")
```

</details>

#### converts dict with two entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_dict([("x", "1"), ("y", "2")])).to_equal("\{x: 1, y: 2\}")
```

</details>

### define_schema extended

#### defines single-field schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = define_schema([("id", "int")])
expect(result).to_contain("id: int")
```

</details>

#### defines three-field schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = define_schema([("name", "text"), ("age", "int"), ("active", "bool")])
expect(result).to_contain("name: text")
expect(result).to_contain("active: bool")
```

</details>

### validate_field_type extended

#### validates negative int

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("-5", "int")).to_equal(true)
```

</details>

#### validates text with escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("\"ab\\nc\"", "text")).to_equal(true)
```

</details>

#### validates list with items

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("[1, 2, 3]", "list")).to_equal(true)
```

</details>

#### validates empty tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("()", "tuple")).to_equal(true)
```

</details>

#### validates empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "\{" + "\}"
expect(validate_field_type(input, "dict")).to_equal(true)
```

</details>

### validate_field_type unknown type

#### returns true for unknown type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("anything", "unknown_type")).to_equal(true)
```

</details>

#### returns false for wrong int

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("abc", "int")).to_equal(false)
```

</details>

#### returns false for wrong bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("yes", "bool")).to_equal(false)
```

</details>

#### returns false for wrong nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("none", "nil")).to_equal(false)
```

</details>

#### returns false for wrong text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("abc", "text")).to_equal(false)
```

</details>

#### returns false for wrong list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("abc", "list")).to_equal(false)
```

</details>

#### returns false for wrong tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("abc", "tuple")).to_equal(false)
```

</details>

#### returns false for wrong dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("abc", "dict")).to_equal(false)
```

</details>

### is_numeric_text edge cases

#### returns false for just minus sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("-")).to_equal(false)
```

</details>

#### returns true for single digit zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("0")).to_equal(true)
```

</details>

#### returns false for plus sign prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("+5")).to_equal(false)
```

</details>

#### returns false for letter only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("a")).to_equal(false)
```

</details>

#### returns true for negative single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_numeric_text("-1")).to_equal(true)
```

</details>

### get_type_tag edge cases

#### returns nil for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("")
expect(result).to_be_nil()
```

</details>

#### returns nil for single char

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("a")
expect(result).to_be_nil()
```

</details>

#### returns nil for two chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("ab")
expect(result).to_be_nil()
```

</details>

#### returns nil for non-at prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("hello\{x\}")
expect(result).to_be_nil()
```

</details>

### strip_type_tag edge cases

#### returns original for non-tagged string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("hello")
expect(result).to_equal("hello")
```

</details>

#### returns original for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("")
expect(result).to_equal("")
```

</details>

#### returns original for at-sign without brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("@NoClose")
expect(result).to_equal("@NoClose")
```

</details>

#### handles brace at very end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("@T\{")
expect(result).to_equal("@T\{")
```

</details>

### get_version edge cases

#### returns nil for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_version("")
expect(result).to_be_nil()
```

</details>

#### returns nil for non-versioned input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_version("just text")
expect(result).to_be_nil()
```

</details>

#### returns nil for partial prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_version("\{v:")
expect(result).to_be_nil()
```

</details>

### strip_version edge cases

#### returns original for non-versioned string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_version("hello world")
expect(result).to_equal("hello world")
```

</details>

#### returns original for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_version("")
expect(result).to_equal("")
```

</details>

### parse_int_safe edge cases

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("")).to_equal(0)
```

</details>

#### returns 0 for just minus sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("-")).to_equal(0)
```

</details>

#### parses zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("0")).to_equal(0)
```

</details>

#### stops at non-digit immediately

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("abc")).to_equal(0)
```

</details>

### char_to_digit_safe edge cases

#### returns 0 for non-digit char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_to_digit_safe("x")).to_equal(0)
```

</details>

#### returns correct value for 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_to_digit_safe("5")).to_equal(5)
```

</details>

### read_bytes boundary cases

#### handles zero length read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_bytes([1, 2, 3], 0, 0)
val data = result.0
expect(data.len()).to_equal(0)
```

</details>

#### reads exactly all bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [10, 20, 30]
val result = read_bytes(data, 0, 3)
val bytes = result.0
expect(bytes.len()).to_equal(3)
expect(bytes[0]).to_equal(10)
expect(bytes[2]).to_equal(30)
```

</details>

#### reads partially beyond array end

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [10, 20]
val result = read_bytes(data, 0, 4)
val bytes = result.0
# Only 2 of 4 requested bytes are in bounds
expect(result.1).to_equal(4)
```

</details>

### read_bytes_with_length edge cases

#### reads empty data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [0]
val result = read_bytes_with_length(data, 0)
val bytes = result.0
expect(bytes.len()).to_equal(0)
```

</details>

#### reads single byte data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 42]
val result = read_bytes_with_length(data, 0)
val bytes = result.0
expect(bytes.len()).to_equal(1)
expect(bytes[0]).to_equal(42)
```

</details>

### write_varint edge single byte

#### encodes 1 as single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(1)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(1)
```

</details>

#### encodes 127 as single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(127)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(127)
```

</details>

#### encodes -1 with sign marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_varint(-1)
expect(result[0]).to_equal(255)
```

</details>

### escape_string empty

#### escapes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_string("")).to_equal("")
```

</details>

#### escapes newline alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_string("\n")).to_equal("\\n")
```

</details>

### unescape_string edge

#### unescapes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_string("")).to_equal("")
```

</details>

#### unescapes tab escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_string("\\t")).to_equal("\t")
```

</details>

#### unescapes carriage return escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_string("\\r")).to_equal("\r")
```

</details>

### unquote_string empty

#### returns empty string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unquote_string("")).to_equal("")
```

</details>

### detect_format all branches

#### detects tagged format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("@Type\{data\}")).to_equal("tagged")
```

</details>

#### detects sdn for curly brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("\{key: val\}")).to_equal("sdn")
```

</details>

#### detects sdn for bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("[1, 2]")).to_equal("sdn")
```

</details>

#### detects sdn for quoted string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("\"hello\"")).to_equal("sdn")
```

</details>

#### detects sdn for true literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("true")).to_equal("sdn")
```

</details>

#### detects sdn for false literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("false")).to_equal("sdn")
```

</details>

#### detects sdn for nil literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("nil")).to_equal("sdn")
```

</details>

#### detects sdn for positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("42")).to_equal("sdn")
```

</details>

#### detects sdn for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("0")).to_equal("sdn")
```

</details>

#### returns unknown for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("")).to_equal("unknown")
```

</details>

#### returns unknown for random text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_format("hello")).to_equal("unknown")
```

</details>

### is_valid_sdn all branches

#### accepts tagged format as valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("@T\{x\}")).to_equal(true)
```

</details>

#### accepts list as valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("[1]")).to_equal(true)
```

</details>

#### rejects unknown format

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_sdn("~weird~")).to_equal(false)
```

</details>

### pretty_print empty collections

#### pretty prints empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pretty_list([], 0)).to_equal("[]")
```

</details>

#### pretty prints empty tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pretty_tuple([], 0)).to_equal("()")
```

</details>

#### pretty prints empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pretty_dict([], 0)).to_equal("\{\}")
```

</details>

#### pretty prints single-item list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_list(["x"], 0)
expect(result).to_contain("x")
```

</details>

#### pretty prints single-item tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_tuple(["x"], 0)
expect(result).to_contain("x")
```

</details>

#### pretty prints single-entry dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pretty_dict([("k", "v")], 0)
expect(result).to_contain("k: v")
```

</details>

### pretty_print_indent level zero

#### does not indent at level 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pretty_print_indent("test", 0)).to_equal("test")
```

</details>

#### indents one level

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pretty_print_indent("x", 1)).to_equal("  x")
```

</details>

### serialize empty collections

#### serializes empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_list([])).to_equal("[]")
```

</details>

#### serializes empty tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_tuple_text([])).to_equal("()")
```

</details>

#### serializes empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_dict([])).to_equal("\{\}")
```

</details>

#### serializes single-item list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_list(["a"])).to_equal("[a]")
```

</details>

#### serializes single-value tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_tuple_text(["x"])).to_equal("(x)")
```

</details>

#### serializes single-entry dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_dict([("k", "v")])
expect(result).to_equal("\{k: v\}")
```

</details>

### serialize_int_list empty

#### serializes empty int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_int_list([])).to_equal("[]")
```

</details>

#### serializes empty text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_text_list([])).to_equal("[]")
```

</details>

#### serializes empty bool list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_bool_list([])).to_equal("[]")
```

</details>

### binary list serialization empty

#### serializes empty int list bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_int_list_bytes([])
expect(result[0]).to_equal(type_list())
expect(result.len()).to_equal(2)
```

</details>

#### serializes empty text list bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = serialize_text_list_bytes([])
expect(result[0]).to_equal(type_list())
expect(result.len()).to_equal(2)
```

</details>

### SDN empty collections

#### converts empty list to SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_list([])).to_equal("[]")
```

</details>

#### converts empty tuple to SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_tuple([])).to_equal("()")
```

</details>

#### converts empty dict to SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_dict([])).to_equal("\{\}")
```

</details>

### type tags and compression cross-check

#### tag_type creates proper format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tag_type("content", "MyType")
expect(result).to_equal("@MyType\{content\}")
```

</details>

#### is_compressed returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed("")).to_equal(false)
```

</details>

#### is_encrypted returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_encrypted("")).to_equal(false)
```

</details>

#### is_compressed with non-at-sign prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed("hello world")).to_equal(false)
```

</details>

#### is_encrypted with non-at-sign prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_encrypted("hello world")).to_equal(false)
```

</details>

### deep clone functions

#### deep clones integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_clone_int(42)).to_equal(42)
```

</details>

#### deep clones boolean true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_clone_bool(true)).to_equal(true)
```

</details>

#### deep clones boolean false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_clone_bool(false)).to_equal(false)
```

</details>

#### deep clones text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_clone_text("hello")).to_equal("hello")
```

</details>

#### deep clones empty int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = deep_clone_list_int([])
expect(result.len()).to_equal(0)
```

</details>

#### deep clones empty text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = deep_clone_list_text([])
expect(result.len()).to_equal(0)
```

</details>

#### shallow clones int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shallow_clone_list_int([1, 2])
expect(result.len()).to_equal(2)
```

</details>

#### shallow clones text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shallow_clone_list_text(["a"])
expect(result.len()).to_equal(1)
```

</details>

### deep_equal edge cases

#### compares equal empty int lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([], [])).to_equal(true)
```

</details>

#### compares equal empty text lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_text([], [])).to_equal(true)
```

</details>

#### returns false for different length int lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([1], [1, 2])).to_equal(false)
```

</details>

#### returns false for different length text lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_text(["a"], ["a", "b"])).to_equal(false)
```

</details>

#### deep_equal_int true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_int(5, 5)).to_equal(true)
```

</details>

#### deep_equal_int false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_int(5, 6)).to_equal(false)
```

</details>

#### deep_equal_bool true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_bool(true, true)).to_equal(true)
```

</details>

#### deep_equal_bool false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_bool(true, false)).to_equal(false)
```

</details>

#### deep_equal_text true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_text("a", "a")).to_equal(true)
```

</details>

#### deep_equal_text false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_text("a", "b")).to_equal(false)
```

</details>

### hex digit coverage complete

#### digit_to_hex out of range returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(digit_to_hex(16)).to_equal("0")
```

</details>

#### digit_to_hex negative returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(digit_to_hex(-1)).to_equal("0")
```

</details>

#### hex_to_digit unknown char returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("z")).to_equal(0)
```

</details>

#### hex_to_digit uppercase A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("A")).to_equal(10)
```

</details>

#### hex_to_digit uppercase F

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_digit("F")).to_equal(15)
```

</details>

### serialize_bool text

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

### to_sdn_bool both branches

#### converts true to SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_bool(true)).to_equal("true")
```

</details>

#### converts false to SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_bool(false)).to_equal("false")
```

</details>

### add_version and schema

#### adds version to simple data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_version("data", 1)
expect(result).to_contain("v: 1")
expect(result).to_contain("data")
```

</details>

#### defines empty schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = define_schema([])
expect(result).to_equal("\{\}")
```

</details>

### serialize_nil text

#### returns nil string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(serialize_nil()).to_equal("nil")
```

</details>

### to_sdn_nil

#### returns nil string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_sdn_nil()).to_equal("nil")
```

</details>

### char_code_safe special symbols

#### handles dollar sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("$")).to_equal(36)
```

</details>

#### handles percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("%")).to_equal(37)
```

</details>

#### handles ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("&")).to_equal(38)
```

</details>

#### handles single quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("'")).to_equal(39)
```

</details>

#### handles open paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("(")).to_equal(40)
```

</details>

#### handles close paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe(")")).to_equal(41)
```

</details>

#### handles asterisk

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("*")).to_equal(42)
```

</details>

#### handles plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("+")).to_equal(43)
```

</details>

#### handles comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe(",")).to_equal(44)
```

</details>

#### handles hyphen

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("-")).to_equal(45)
```

</details>

#### handles period

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe(".")).to_equal(46)
```

</details>

#### handles slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_safe("/")).to_equal(47)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 153 |
| Active scenarios | 153 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
