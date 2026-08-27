# Serialization Extended Edge Cases Coverage Specification

> Purpose: Prove that pretty_print extended.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 155 | 155 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Extended Edge Cases Coverage Specification

Purpose: Prove that pretty_print extended.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-EXTENDED |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Blocked — std.common.serialization has no .spl source (only empty .smf stubs). |
| Source | `test/unit/lib/common/serialization_extended_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that pretty_print extended.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### pretty_print extended

#### pretty prints nested list at indent 2

- pretty prints nested list at indent 2
- Verify: pretty prints nested list at indent 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints nested list at indent 2")
step("Verify: pretty prints nested list at indent 2")
# @req: REQ-LIB-COMMON-001
val result = pretty_list(["inner"], 2)
expect(result).to_start_with("[\n")
expect(result).to_contain("inner")
```

</details>

#### pretty prints nested tuple at indent 1

- pretty prints nested tuple at indent 1
- Verify: pretty prints nested tuple at indent 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints nested tuple at indent 1")
step("Verify: pretty prints nested tuple at indent 1")
val result = pretty_tuple(["a", "b", "c"], 1)
expect(result).to_start_with("(\n")
expect(result).to_contain(",")
```

</details>

#### pretty prints nested dict at indent 1

- pretty prints nested dict at indent 1
- Verify: pretty prints nested dict at indent 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints nested dict at indent 1")
step("Verify: pretty prints nested dict at indent 1")
val result = pretty_dict([("x", "1"), ("y", "2"), ("z", "3")], 1)
expect(result).to_start_with("{\n")
expect(result).to_contain(",")
```

</details>

#### indents at level 3

- indents at level 3
- Verify: indents at level 3
   - Expected: result equals `      test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indents at level 3")
step("Verify: indents at level 3")
val result = pretty_print_indent("test", 3)
expect(result).to_equal("      test")
```

</details>

### serialize collections extended

#### serializes four-item list

- serializes four-item list
- Verify: serializes four-item list
   - Expected: result equals `[a, b, c, d]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes four-item list")
step("Verify: serializes four-item list")
val result = serialize_list(["a", "b", "c", "d"])
expect(result).to_equal("[a, b, c, d]")
```

</details>

#### serializes three-value tuple

- serializes three-value tuple
- Verify: serializes three-value tuple
   - Expected: result equals `(x, y, z)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes three-value tuple")
step("Verify: serializes three-value tuple")
val result = serialize_tuple_text(["x", "y", "z"])
expect(result).to_equal("(x, y, z)")
```

</details>

#### serializes three-entry dict

- serializes three-entry dict
- Verify: serializes three-entry dict
   - Expected: result equals `\{a: 1, b: 2, c: 3\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes three-entry dict")
step("Verify: serializes three-entry dict")
val result = serialize_dict([("a", "1"), ("b", "2"), ("c", "3")])
expect(result).to_equal("\{a: 1, b: 2, c: 3\}")
```

</details>

#### serializes int list with negative values

- serializes int list with negative values
- Verify: serializes int list with negative values
   - Expected: result equals `[-1, 0, 1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes int list with negative values")
step("Verify: serializes int list with negative values")
val result = serialize_int_list([-1, 0, 1])
expect(result).to_equal("[-1, 0, 1]")
```

</details>

#### serializes text list with special chars

- serializes text list with special chars
- Verify: serializes text list with special chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes text list with special chars")
step("Verify: serializes text list with special chars")
val result = serialize_text_list(["hello world"])
expect(result).to_contain("hello world")
```

</details>

#### serializes bool list with single item

- serializes bool list with single item
- Verify: serializes bool list with single item
   - Expected: result equals `[true]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes bool list with single item")
step("Verify: serializes bool list with single item")
val result = serialize_bool_list([true])
expect(result).to_equal("[true]")
```

</details>

### binary list serialization extended

#### encodes non-empty int list bytes

- encodes non-empty int list bytes
- Verify: encodes non-empty int list bytes
   - Expected: result[0] equals `type_list()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes non-empty int list bytes")
step("Verify: encodes non-empty int list bytes")
val result = serialize_int_list_bytes([10, 20])
expect(result[0]).to_equal(type_list())
expect(result.len()).to_be_greater_than(3)
```

</details>

#### encodes non-empty text list bytes

- encodes non-empty text list bytes
- Verify: encodes non-empty text list bytes
   - Expected: result[0] equals `type_list()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes non-empty text list bytes")
step("Verify: encodes non-empty text list bytes")
val result = serialize_text_list_bytes(["hi"])
expect(result[0]).to_equal(type_list())
expect(result.len()).to_be_greater_than(2)
```

</details>

### SDN conversions extended

#### converts large negative integer to SDN

- converts large negative integer to SDN
- Verify: converts large negative integer to SDN
   - Expected: to_sdn_int(-999) equals `-999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts large negative integer to SDN")
step("Verify: converts large negative integer to SDN")
expect(to_sdn_int(-999)).to_equal("-999")
```

</details>

#### converts list with three items

- converts list with three items
- Verify: converts list with three items
   - Expected: to_sdn_list(["a", "b", "c"]) equals `[a, b, c]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts list with three items")
step("Verify: converts list with three items")
expect(to_sdn_list(["a", "b", "c"])).to_equal("[a, b, c]")
```

</details>

#### converts tuple with three items

- converts tuple with three items
- Verify: converts tuple with three items
   - Expected: to_sdn_tuple(["1", "2", "3"]) equals `(1, 2, 3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts tuple with three items")
step("Verify: converts tuple with three items")
expect(to_sdn_tuple(["1", "2", "3"])).to_equal("(1, 2, 3)")
```

</details>

#### converts dict with two entries

- converts dict with two entries
- Verify: converts dict with two entries
   - Expected: to_sdn_dict([("x", "1"), ("y", "2")]) equals `\{x: 1, y: 2\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts dict with two entries")
step("Verify: converts dict with two entries")
expect(to_sdn_dict([("x", "1"), ("y", "2")])).to_equal("\{x: 1, y: 2\}")
```

</details>

### define_schema extended

#### defines single-field schema

- defines single-field schema
- Verify: defines single-field schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines single-field schema")
step("Verify: defines single-field schema")
val result = define_schema([("id", "int")])
expect(result).to_contain("id: int")
```

</details>

#### defines three-field schema

- defines three-field schema
- Verify: defines three-field schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines three-field schema")
step("Verify: defines three-field schema")
val result = define_schema([("name", "text"), ("age", "int"), ("active", "bool")])
expect(result).to_contain("name: text")
expect(result).to_contain("active: bool")
```

</details>

### validate_field_type extended

#### validates negative int

- validates negative int
- Verify: validates negative int
   - Expected: validate_field_type("-5", "int") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates negative int")
step("Verify: validates negative int")
expect(validate_field_type("-5", "int")).to_equal(true)
```

</details>

#### validates text with escape

- validates text with escape
- Verify: validates text with escape
   - Expected: validate_field_type("\"ab\\nc\"", "text") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates text with escape")
step("Verify: validates text with escape")
expect(validate_field_type("\"ab\\nc\"", "text")).to_equal(true)
```

</details>

#### validates list with items

- validates list with items
- Verify: validates list with items
   - Expected: validate_field_type("[1, 2, 3]", "list") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates list with items")
step("Verify: validates list with items")
expect(validate_field_type("[1, 2, 3]", "list")).to_equal(true)
```

</details>

#### validates empty tuple

- validates empty tuple
- Verify: validates empty tuple
   - Expected: validate_field_type("()", "tuple") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates empty tuple")
step("Verify: validates empty tuple")
expect(validate_field_type("()", "tuple")).to_equal(true)
```

</details>

#### validates empty dict

- validates empty dict
- Verify: validates empty dict
   - Expected: validate_field_type(input, "dict") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates empty dict")
step("Verify: validates empty dict")
val input = "\{" + "\}"
expect(validate_field_type(input, "dict")).to_equal(true)
```

</details>

### validate_field_type unknown type

#### returns true for unknown type

- returns true for unknown type
- Verify: returns true for unknown type
   - Expected: validate_field_type("anything", "unknown_type") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for unknown type")
step("Verify: returns true for unknown type")
expect(validate_field_type("anything", "unknown_type")).to_equal(true)
```

</details>

#### returns false for wrong int

- returns false for wrong int
- Verify: returns false for wrong int
   - Expected: validate_field_type("abc", "int") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for wrong int")
step("Verify: returns false for wrong int")
expect(validate_field_type("abc", "int")).to_equal(false)
```

</details>

#### returns false for wrong bool

- returns false for wrong bool
- Verify: returns false for wrong bool
   - Expected: validate_field_type("yes", "bool") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for wrong bool")
step("Verify: returns false for wrong bool")
expect(validate_field_type("yes", "bool")).to_equal(false)
```

</details>

#### returns false for wrong nil

- returns false for wrong nil
- Verify: returns false for wrong nil
   - Expected: validate_field_type("none", "nil") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for wrong nil")
step("Verify: returns false for wrong nil")
expect(validate_field_type("none", "nil")).to_equal(false)
```

</details>

#### returns false for wrong text

- returns false for wrong text
- Verify: returns false for wrong text
   - Expected: validate_field_type("abc", "text") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for wrong text")
step("Verify: returns false for wrong text")
expect(validate_field_type("abc", "text")).to_equal(false)
```

</details>

#### returns false for wrong list

- returns false for wrong list
- Verify: returns false for wrong list
   - Expected: validate_field_type("abc", "list") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for wrong list")
step("Verify: returns false for wrong list")
expect(validate_field_type("abc", "list")).to_equal(false)
```

</details>

#### returns false for wrong tuple

- returns false for wrong tuple
- Verify: returns false for wrong tuple
   - Expected: validate_field_type("abc", "tuple") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for wrong tuple")
step("Verify: returns false for wrong tuple")
expect(validate_field_type("abc", "tuple")).to_equal(false)
```

</details>

#### returns false for wrong dict

- returns false for wrong dict
- Verify: returns false for wrong dict
   - Expected: validate_field_type("abc", "dict") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for wrong dict")
step("Verify: returns false for wrong dict")
expect(validate_field_type("abc", "dict")).to_equal(false)
```

</details>

### is_numeric_text edge cases

#### returns false for just minus sign

- returns false for just minus sign
- Verify: returns false for just minus sign
   - Expected: is_numeric_text("-") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for just minus sign")
step("Verify: returns false for just minus sign")
expect(is_numeric_text("-")).to_equal(false)
```

</details>

#### returns true for single digit zero

- returns true for single digit zero
- Verify: returns true for single digit zero
   - Expected: is_numeric_text("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for single digit zero")
step("Verify: returns true for single digit zero")
expect(is_numeric_text("0")).to_equal(true)
```

</details>

#### returns false for plus sign prefix

- returns false for plus sign prefix
- Verify: returns false for plus sign prefix
   - Expected: is_numeric_text("+5") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for plus sign prefix")
step("Verify: returns false for plus sign prefix")
expect(is_numeric_text("+5")).to_equal(false)
```

</details>

#### returns false for letter only

- returns false for letter only
- Verify: returns false for letter only
   - Expected: is_numeric_text("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for letter only")
step("Verify: returns false for letter only")
expect(is_numeric_text("a")).to_equal(false)
```

</details>

#### returns true for negative single digit

- returns true for negative single digit
- Verify: returns true for negative single digit
   - Expected: is_numeric_text("-1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for negative single digit")
step("Verify: returns true for negative single digit")
expect(is_numeric_text("-1")).to_equal(true)
```

</details>

### get_type_tag edge cases

#### returns nil for empty string

- returns nil for empty string
- Verify: returns nil for empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty string")
step("Verify: returns nil for empty string")
val result = get_type_tag("")
expect(result).to_be_nil()
```

</details>

#### returns nil for single char

- returns nil for single char
- Verify: returns nil for single char


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for single char")
step("Verify: returns nil for single char")
val result = get_type_tag("a")
expect(result).to_be_nil()
```

</details>

#### returns nil for two chars

- returns nil for two chars
- Verify: returns nil for two chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for two chars")
step("Verify: returns nil for two chars")
val result = get_type_tag("ab")
expect(result).to_be_nil()
```

</details>

#### returns nil for non-at prefix

- returns nil for non-at prefix
- Verify: returns nil for non-at prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for non-at prefix")
step("Verify: returns nil for non-at prefix")
val result = get_type_tag("hello\{x\}")
expect(result).to_be_nil()
```

</details>

### strip_type_tag edge cases

#### returns original for non-tagged string

- returns original for non-tagged string
- Verify: returns original for non-tagged string
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original for non-tagged string")
step("Verify: returns original for non-tagged string")
val result = strip_type_tag("hello")
expect(result).to_equal("hello")
```

</details>

#### returns original for empty string

- returns original for empty string
- Verify: returns original for empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original for empty string")
step("Verify: returns original for empty string")
val result = strip_type_tag("")
expect(result).to_equal("")
```

</details>

#### returns original for at-sign without brace

- returns original for at-sign without brace
- Verify: returns original for at-sign without brace
   - Expected: result equals `@NoClose`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original for at-sign without brace")
step("Verify: returns original for at-sign without brace")
val result = strip_type_tag("@NoClose")
expect(result).to_equal("@NoClose")
```

</details>

#### handles brace at very end

- handles brace at very end
- Verify: handles brace at very end
   - Expected: result equals `@T\{`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles brace at very end")
step("Verify: handles brace at very end")
val result = strip_type_tag("@T\{")
expect(result).to_equal("@T\{")
```

</details>

### get_version edge cases

#### returns nil for empty string

- returns nil for empty string
- Verify: returns nil for empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty string")
step("Verify: returns nil for empty string")
val result = get_version("")
expect(result).to_be_nil()
```

</details>

#### returns nil for non-versioned input

- returns nil for non-versioned input
- Verify: returns nil for non-versioned input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for non-versioned input")
step("Verify: returns nil for non-versioned input")
val result = get_version("just text")
expect(result).to_be_nil()
```

</details>

#### returns nil for partial prefix

- returns nil for partial prefix
- Verify: returns nil for partial prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for partial prefix")
step("Verify: returns nil for partial prefix")
val result = get_version("\{v:")
expect(result).to_be_nil()
```

</details>

### strip_version edge cases

#### returns original for non-versioned string

- returns original for non-versioned string
- Verify: returns original for non-versioned string
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original for non-versioned string")
step("Verify: returns original for non-versioned string")
val result = strip_version("hello world")
expect(result).to_equal("hello world")
```

</details>

#### returns original for empty string

- returns original for empty string
- Verify: returns original for empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original for empty string")
step("Verify: returns original for empty string")
val result = strip_version("")
expect(result).to_equal("")
```

</details>

### parse_int_safe edge cases

#### returns 0 for empty string

- returns 0 for empty string
- Verify: returns 0 for empty string
   - Expected: parse_int_safe("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty string")
step("Verify: returns 0 for empty string")
expect(parse_int_safe("")).to_equal(0)
```

</details>

#### returns 0 for just minus sign

- returns 0 for just minus sign
- Verify: returns 0 for just minus sign
   - Expected: parse_int_safe("-") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for just minus sign")
step("Verify: returns 0 for just minus sign")
expect(parse_int_safe("-")).to_equal(0)
```

</details>

#### parses zero

- parses zero
- Verify: parses zero
   - Expected: parse_int_safe("0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses zero")
step("Verify: parses zero")
expect(parse_int_safe("0")).to_equal(0)
```

</details>

#### stops at non-digit immediately

- stops at non-digit immediately
- Verify: stops at non-digit immediately
   - Expected: parse_int_safe("abc") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops at non-digit immediately")
step("Verify: stops at non-digit immediately")
expect(parse_int_safe("abc")).to_equal(0)
```

</details>

### char_to_digit_safe edge cases

#### returns 0 for non-digit char

- returns 0 for non-digit char
- Verify: returns 0 for non-digit char
   - Expected: char_to_digit_safe("x") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for non-digit char")
step("Verify: returns 0 for non-digit char")
expect(char_to_digit_safe("x")).to_equal(0)
```

</details>

#### returns correct value for 5

- returns correct value for 5
- Verify: returns correct value for 5
   - Expected: char_to_digit_safe("5") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct value for 5")
step("Verify: returns correct value for 5")
expect(char_to_digit_safe("5")).to_equal(5)
```

</details>

### read_bytes boundary cases

#### handles zero length read

- handles zero length read
- Verify: handles zero length read
   - Expected: data.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero length read")
step("Verify: handles zero length read")
val result = read_bytes([1, 2, 3], 0, 0)
val data = result.0
expect(data.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reads exactly all bytes

- reads exactly all bytes
- Verify: reads exactly all bytes
   - Expected: bytes.len() equals `3`
   - Expected: bytes[0] equals `10`
   - Expected: bytes[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads exactly all bytes")
step("Verify: reads exactly all bytes")
val data = [10, 20, 30]
val result = read_bytes(data, 0, 3)
val bytes = result.0
expect(bytes.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(bytes[0]).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(bytes[2]).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### reads partially beyond array end

- reads partially beyond array end
- Verify: reads partially beyond array end
   - Expected: result.1 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads partially beyond array end")
step("Verify: reads partially beyond array end")
val data = [10, 20]
val result = read_bytes(data, 0, 4)
val bytes = result.0
# Only 2 of 4 requested bytes are in bounds
expect(result.1).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### rejects negative offset

- rejects negative offset
- Verify: rejects negative offset
   - Expected: bytes.len() equals `0`
   - Expected: result.1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative offset")
step("Verify: rejects negative offset")
val result = read_bytes([10, 20], 0 - 1, 2)
val bytes = result.0
expect(bytes.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.1).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### read_bytes_with_length edge cases

#### reads empty data

- reads empty data
- Verify: reads empty data
   - Expected: bytes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads empty data")
step("Verify: reads empty data")
val data = [0]
val result = read_bytes_with_length(data, 0)
val bytes = result.0
expect(bytes.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reads single byte data

- reads single byte data
- Verify: reads single byte data
   - Expected: bytes.len() equals `1`
   - Expected: bytes[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads single byte data")
step("Verify: reads single byte data")
val data = [1, 42]
val result = read_bytes_with_length(data, 0)
val bytes = result.0
expect(bytes.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(bytes[0]).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### rejects negative offset

- rejects negative offset
- Verify: rejects negative offset
   - Expected: bytes.len() equals `0`
   - Expected: result.1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative offset")
step("Verify: rejects negative offset")
val result = read_bytes_with_length([1, 42], 0 - 1)
val bytes = result.0
expect(bytes.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.1).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### write_varint edge single byte

#### encodes 1 as single byte

- encodes 1 as single byte
- Verify: encodes 1 as single byte
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 1 as single byte")
step("Verify: encodes 1 as single byte")
val result = write_varint(1)
expect(result.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### encodes 127 as single byte

- encodes 127 as single byte
- Verify: encodes 127 as single byte
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 127 as single byte")
step("Verify: encodes 127 as single byte")
val result = write_varint(127)
expect(result.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result[0]).to_equal(127)  # oracle: 127 — named expected value from the requirement
```

</details>

#### encodes -1 with sign marker

- encodes -1 with sign marker
- Verify: encodes -1 with sign marker
   - Expected: result[0] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes -1 with sign marker")
step("Verify: encodes -1 with sign marker")
val result = write_varint(-1)
expect(result[0]).to_equal(255)  # oracle: 255 — named expected value from the requirement
```

</details>

### escape_string empty

#### escapes empty string

- escapes empty string
- Verify: escapes empty string
   - Expected: escape_string("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes empty string")
step("Verify: escapes empty string")
expect(escape_string("")).to_equal("")
```

</details>

#### escapes newline alone

- escapes newline alone
- Verify: escapes newline alone
   - Expected: escape_string("\n") equals `\\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes newline alone")
step("Verify: escapes newline alone")
expect(escape_string("\n")).to_equal("\\n")
```

</details>

### unescape_string edge

#### unescapes empty string

- unescapes empty string
- Verify: unescapes empty string
   - Expected: unescape_string("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes empty string")
step("Verify: unescapes empty string")
expect(unescape_string("")).to_equal("")
```

</details>

#### unescapes tab escape

- unescapes tab escape
- Verify: unescapes tab escape
   - Expected: unescape_string("\\t") equals `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes tab escape")
step("Verify: unescapes tab escape")
expect(unescape_string("\\t")).to_equal("\t")
```

</details>

#### unescapes carriage return escape

- unescapes carriage return escape
- Verify: unescapes carriage return escape
   - Expected: unescape_string("\\r") equals `\r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes carriage return escape")
step("Verify: unescapes carriage return escape")
expect(unescape_string("\\r")).to_equal("\r")
```

</details>

### unquote_string empty

#### returns empty string unchanged

- returns empty string unchanged
- Verify: returns empty string unchanged
   - Expected: unquote_string("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string unchanged")
step("Verify: returns empty string unchanged")
expect(unquote_string("")).to_equal("")
```

</details>

### detect_format all branches

#### detects tagged format

- detects tagged format
- Verify: detects tagged format
   - Expected: detect_format("@Type\{data\}") equals `tagged`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects tagged format")
step("Verify: detects tagged format")
expect(detect_format("@Type\{data\}")).to_equal("tagged")
```

</details>

#### detects sdn for curly brace

- detects sdn for curly brace
- Verify: detects sdn for curly brace
   - Expected: detect_format("\{key: val\}") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for curly brace")
step("Verify: detects sdn for curly brace")
expect(detect_format("\{key: val\}")).to_equal("sdn")
```

</details>

#### detects sdn for bracket

- detects sdn for bracket
- Verify: detects sdn for bracket
   - Expected: detect_format("[1, 2]") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for bracket")
step("Verify: detects sdn for bracket")
expect(detect_format("[1, 2]")).to_equal("sdn")
```

</details>

#### detects sdn for quoted string

- detects sdn for quoted string
- Verify: detects sdn for quoted string
   - Expected: detect_format("\"hello\"") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for quoted string")
step("Verify: detects sdn for quoted string")
expect(detect_format("\"hello\"")).to_equal("sdn")
```

</details>

#### detects sdn for true literal

- detects sdn for true literal
- Verify: detects sdn for true literal
   - Expected: detect_format("true") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for true literal")
step("Verify: detects sdn for true literal")
expect(detect_format("true")).to_equal("sdn")
```

</details>

#### detects sdn for false literal

- detects sdn for false literal
- Verify: detects sdn for false literal
   - Expected: detect_format("false") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for false literal")
step("Verify: detects sdn for false literal")
expect(detect_format("false")).to_equal("sdn")
```

</details>

#### detects sdn for nil literal

- detects sdn for nil literal
- Verify: detects sdn for nil literal
   - Expected: detect_format("nil") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for nil literal")
step("Verify: detects sdn for nil literal")
expect(detect_format("nil")).to_equal("sdn")
```

</details>

#### detects sdn for positive number

- detects sdn for positive number
- Verify: detects sdn for positive number
   - Expected: detect_format("42") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for positive number")
step("Verify: detects sdn for positive number")
expect(detect_format("42")).to_equal("sdn")
```

</details>

#### detects sdn for zero

- detects sdn for zero
- Verify: detects sdn for zero
   - Expected: detect_format("0") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for zero")
step("Verify: detects sdn for zero")
expect(detect_format("0")).to_equal("sdn")
```

</details>

#### returns unknown for empty

- returns unknown for empty
- Verify: returns unknown for empty
   - Expected: detect_format("") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for empty")
step("Verify: returns unknown for empty")
expect(detect_format("")).to_equal("unknown")
```

</details>

#### returns unknown for random text

- returns unknown for random text
- Verify: returns unknown for random text
   - Expected: detect_format("hello") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for random text")
step("Verify: returns unknown for random text")
expect(detect_format("hello")).to_equal("unknown")
```

</details>

### is_valid_sdn all branches

#### accepts tagged format as valid

- accepts tagged format as valid
- Verify: accepts tagged format as valid
   - Expected: is_valid_sdn("@T\{x\}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts tagged format as valid")
step("Verify: accepts tagged format as valid")
expect(is_valid_sdn("@T\{x\}")).to_equal(true)
```

</details>

#### accepts list as valid

- accepts list as valid
- Verify: accepts list as valid
   - Expected: is_valid_sdn("[1]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts list as valid")
step("Verify: accepts list as valid")
expect(is_valid_sdn("[1]")).to_equal(true)
```

</details>

#### rejects unknown format

- rejects unknown format
- Verify: rejects unknown format
   - Expected: is_valid_sdn("~weird~") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown format")
step("Verify: rejects unknown format")
expect(is_valid_sdn("~weird~")).to_equal(false)
```

</details>

### pretty_print empty collections

#### pretty prints empty list

- pretty prints empty list
- Verify: pretty prints empty list
   - Expected: pretty_list([], 0) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints empty list")
step("Verify: pretty prints empty list")
expect(pretty_list([], 0)).to_equal("[]")
```

</details>

#### pretty prints empty tuple

- pretty prints empty tuple
- Verify: pretty prints empty tuple
   - Expected: pretty_tuple([], 0) equals `()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints empty tuple")
step("Verify: pretty prints empty tuple")
expect(pretty_tuple([], 0)).to_equal("()")
```

</details>

#### pretty prints empty dict

- pretty prints empty dict
- Verify: pretty prints empty dict
   - Expected: pretty_dict([], 0) equals `\{\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints empty dict")
step("Verify: pretty prints empty dict")
expect(pretty_dict([], 0)).to_equal("\{\}")
```

</details>

#### pretty prints single-item list

- pretty prints single-item list
- Verify: pretty prints single-item list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints single-item list")
step("Verify: pretty prints single-item list")
val result = pretty_list(["x"], 0)
expect(result).to_contain("x")
```

</details>

#### pretty prints single-item tuple

- pretty prints single-item tuple
- Verify: pretty prints single-item tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints single-item tuple")
step("Verify: pretty prints single-item tuple")
val result = pretty_tuple(["x"], 0)
expect(result).to_contain("x")
```

</details>

#### pretty prints single-entry dict

- pretty prints single-entry dict
- Verify: pretty prints single-entry dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty prints single-entry dict")
step("Verify: pretty prints single-entry dict")
val result = pretty_dict([("k", "v")], 0)
expect(result).to_contain("k: v")
```

</details>

### pretty_print_indent level zero

#### does not indent at level 0

- does not indent at level 0
- Verify: does not indent at level 0
   - Expected: pretty_print_indent("test", 0) equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not indent at level 0")
step("Verify: does not indent at level 0")
expect(pretty_print_indent("test", 0)).to_equal("test")
```

</details>

#### indents one level

- indents one level
- Verify: indents one level
   - Expected: pretty_print_indent("x", 1) equals `  x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indents one level")
step("Verify: indents one level")
expect(pretty_print_indent("x", 1)).to_equal("  x")
```

</details>

### serialize empty collections

#### serializes empty list

- serializes empty list
- Verify: serializes empty list
   - Expected: serialize_list([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty list")
step("Verify: serializes empty list")
expect(serialize_list([])).to_equal("[]")
```

</details>

#### serializes empty tuple

- serializes empty tuple
- Verify: serializes empty tuple
   - Expected: serialize_tuple_text([]) equals `()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty tuple")
step("Verify: serializes empty tuple")
expect(serialize_tuple_text([])).to_equal("()")
```

</details>

#### serializes empty dict

- serializes empty dict
- Verify: serializes empty dict
   - Expected: serialize_dict([]) equals `\{\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty dict")
step("Verify: serializes empty dict")
expect(serialize_dict([])).to_equal("\{\}")
```

</details>

#### serializes single-item list

- serializes single-item list
- Verify: serializes single-item list
   - Expected: serialize_list(["a"]) equals `[a]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes single-item list")
step("Verify: serializes single-item list")
expect(serialize_list(["a"])).to_equal("[a]")
```

</details>

#### serializes single-value tuple

- serializes single-value tuple
- Verify: serializes single-value tuple
   - Expected: serialize_tuple_text(["x"]) equals `(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes single-value tuple")
step("Verify: serializes single-value tuple")
expect(serialize_tuple_text(["x"])).to_equal("(x)")
```

</details>

#### serializes single-entry dict

- serializes single-entry dict
- Verify: serializes single-entry dict
   - Expected: result equals `\{k: v\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes single-entry dict")
step("Verify: serializes single-entry dict")
val result = serialize_dict([("k", "v")])
expect(result).to_equal("\{k: v\}")
```

</details>

### serialize_int_list empty

#### serializes empty int list

- serializes empty int list
- Verify: serializes empty int list
   - Expected: serialize_int_list([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty int list")
step("Verify: serializes empty int list")
expect(serialize_int_list([])).to_equal("[]")
```

</details>

#### serializes empty text list

- serializes empty text list
- Verify: serializes empty text list
   - Expected: serialize_text_list([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty text list")
step("Verify: serializes empty text list")
expect(serialize_text_list([])).to_equal("[]")
```

</details>

#### serializes empty bool list

- serializes empty bool list
- Verify: serializes empty bool list
   - Expected: serialize_bool_list([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty bool list")
step("Verify: serializes empty bool list")
expect(serialize_bool_list([])).to_equal("[]")
```

</details>

### binary list serialization empty

#### serializes empty int list bytes

- serializes empty int list bytes
- Verify: serializes empty int list bytes
   - Expected: result[0] equals `type_list()`
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty int list bytes")
step("Verify: serializes empty int list bytes")
val result = serialize_int_list_bytes([])
expect(result[0]).to_equal(type_list())
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### serializes empty text list bytes

- serializes empty text list bytes
- Verify: serializes empty text list bytes
   - Expected: result[0] equals `type_list()`
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty text list bytes")
step("Verify: serializes empty text list bytes")
val result = serialize_text_list_bytes([])
expect(result[0]).to_equal(type_list())
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### SDN empty collections

#### converts empty list to SDN

- converts empty list to SDN
- Verify: converts empty list to SDN
   - Expected: to_sdn_list([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts empty list to SDN")
step("Verify: converts empty list to SDN")
expect(to_sdn_list([])).to_equal("[]")
```

</details>

#### converts empty tuple to SDN

- converts empty tuple to SDN
- Verify: converts empty tuple to SDN
   - Expected: to_sdn_tuple([]) equals `()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts empty tuple to SDN")
step("Verify: converts empty tuple to SDN")
expect(to_sdn_tuple([])).to_equal("()")
```

</details>

#### converts empty dict to SDN

- converts empty dict to SDN
- Verify: converts empty dict to SDN
   - Expected: to_sdn_dict([]) equals `\{\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts empty dict to SDN")
step("Verify: converts empty dict to SDN")
expect(to_sdn_dict([])).to_equal("\{\}")
```

</details>

### type tags and compression cross-check

#### tag_type creates proper format

- tag_type creates proper format
- Verify: tag_type creates proper format
   - Expected: result equals `@MyType\{content\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tag_type creates proper format")
step("Verify: tag_type creates proper format")
val result = tag_type("content", "MyType")
expect(result).to_equal("@MyType\{content\}")
```

</details>

#### is_compressed returns false for empty string

- is_compressed returns false for empty string
- Verify: is_compressed returns false for empty string
   - Expected: is_compressed("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_compressed returns false for empty string")
step("Verify: is_compressed returns false for empty string")
expect(is_compressed("")).to_equal(false)
```

</details>

#### is_encrypted returns false for empty string

- is_encrypted returns false for empty string
- Verify: is_encrypted returns false for empty string
   - Expected: is_encrypted("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_encrypted returns false for empty string")
step("Verify: is_encrypted returns false for empty string")
expect(is_encrypted("")).to_equal(false)
```

</details>

#### is_compressed with non-at-sign prefix

- is_compressed with non-at-sign prefix
- Verify: is_compressed with non-at-sign prefix
   - Expected: is_compressed("hello world") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_compressed with non-at-sign prefix")
step("Verify: is_compressed with non-at-sign prefix")
expect(is_compressed("hello world")).to_equal(false)
```

</details>

#### is_encrypted with non-at-sign prefix

- is_encrypted with non-at-sign prefix
- Verify: is_encrypted with non-at-sign prefix
   - Expected: is_encrypted("hello world") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_encrypted with non-at-sign prefix")
step("Verify: is_encrypted with non-at-sign prefix")
expect(is_encrypted("hello world")).to_equal(false)
```

</details>

### deep clone functions

#### deep clones integer

- deep clones integer
- Verify: deep clones integer
   - Expected: deep_clone_int(42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep clones integer")
step("Verify: deep clones integer")
expect(deep_clone_int(42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### deep clones boolean true

- deep clones boolean true
- Verify: deep clones boolean true
   - Expected: deep_clone_bool(true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep clones boolean true")
step("Verify: deep clones boolean true")
expect(deep_clone_bool(true)).to_equal(true)
```

</details>

#### deep clones boolean false

- deep clones boolean false
- Verify: deep clones boolean false
   - Expected: deep_clone_bool(false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep clones boolean false")
step("Verify: deep clones boolean false")
expect(deep_clone_bool(false)).to_equal(false)
```

</details>

#### deep clones text

- deep clones text
- Verify: deep clones text
   - Expected: deep_clone_text("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep clones text")
step("Verify: deep clones text")
expect(deep_clone_text("hello")).to_equal("hello")
```

</details>

#### deep clones empty int list

- deep clones empty int list
- Verify: deep clones empty int list
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep clones empty int list")
step("Verify: deep clones empty int list")
val result = deep_clone_list_int([])
expect(result.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### deep clones empty text list

- deep clones empty text list
- Verify: deep clones empty text list
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep clones empty text list")
step("Verify: deep clones empty text list")
val result = deep_clone_list_text([])
expect(result.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### shallow clones int list

- shallow clones int list
- Verify: shallow clones int list
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shallow clones int list")
step("Verify: shallow clones int list")
val result = shallow_clone_list_int([1, 2])
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### shallow clones text list

- shallow clones text list
- Verify: shallow clones text list
   - Expected: result.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shallow clones text list")
step("Verify: shallow clones text list")
val result = shallow_clone_list_text(["a"])
expect(result.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### deep_equal edge cases

#### compares equal empty int lists

- compares equal empty int lists
- Verify: compares equal empty int lists
   - Expected: deep_equal_list_int([], []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal empty int lists")
step("Verify: compares equal empty int lists")
expect(deep_equal_list_int([], [])).to_equal(true)
```

</details>

#### compares equal empty text lists

- compares equal empty text lists
- Verify: compares equal empty text lists
   - Expected: deep_equal_list_text([], []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal empty text lists")
step("Verify: compares equal empty text lists")
expect(deep_equal_list_text([], [])).to_equal(true)
```

</details>

#### returns false for different length int lists

- returns false for different length int lists
- Verify: returns false for different length int lists
   - Expected: deep_equal_list_int([1], [1, 2]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for different length int lists")
step("Verify: returns false for different length int lists")
expect(deep_equal_list_int([1], [1, 2])).to_equal(false)
```

</details>

#### returns false for different length text lists

- returns false for different length text lists
- Verify: returns false for different length text lists
   - Expected: deep_equal_list_text(["a"], ["a", "b"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for different length text lists")
step("Verify: returns false for different length text lists")
expect(deep_equal_list_text(["a"], ["a", "b"])).to_equal(false)
```

</details>

#### deep_equal_int true

- deep_equal_int true
- Verify: deep_equal_int true
   - Expected: deep_equal_int(5, 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep_equal_int true")
step("Verify: deep_equal_int true")
expect(deep_equal_int(5, 5)).to_equal(true)
```

</details>

#### deep_equal_int false

- deep_equal_int false
- Verify: deep_equal_int false
   - Expected: deep_equal_int(5, 6) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep_equal_int false")
step("Verify: deep_equal_int false")
expect(deep_equal_int(5, 6)).to_equal(false)
```

</details>

#### deep_equal_bool true

- deep_equal_bool true
- Verify: deep_equal_bool true
   - Expected: deep_equal_bool(true, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep_equal_bool true")
step("Verify: deep_equal_bool true")
expect(deep_equal_bool(true, true)).to_equal(true)
```

</details>

#### deep_equal_bool false

- deep_equal_bool false
- Verify: deep_equal_bool false
   - Expected: deep_equal_bool(true, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep_equal_bool false")
step("Verify: deep_equal_bool false")
expect(deep_equal_bool(true, false)).to_equal(false)
```

</details>

#### deep_equal_text true

- deep_equal_text true
- Verify: deep_equal_text true
   - Expected: deep_equal_text("a", "a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep_equal_text true")
step("Verify: deep_equal_text true")
expect(deep_equal_text("a", "a")).to_equal(true)
```

</details>

#### deep_equal_text false

- deep_equal_text false
- Verify: deep_equal_text false
   - Expected: deep_equal_text("a", "b") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deep_equal_text false")
step("Verify: deep_equal_text false")
expect(deep_equal_text("a", "b")).to_equal(false)
```

</details>

### hex digit coverage complete

#### digit_to_hex out of range returns 0

- digit_to_hex out of range returns 0
- Verify: digit_to_hex out of range returns 0
   - Expected: digit_to_hex(16) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("digit_to_hex out of range returns 0")
step("Verify: digit_to_hex out of range returns 0")
expect(digit_to_hex(16)).to_equal("0")
```

</details>

#### digit_to_hex negative returns 0

- digit_to_hex negative returns 0
- Verify: digit_to_hex negative returns 0
   - Expected: digit_to_hex(-1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("digit_to_hex negative returns 0")
step("Verify: digit_to_hex negative returns 0")
expect(digit_to_hex(-1)).to_equal("0")
```

</details>

#### hex_to_digit unknown char returns 0

- hex_to_digit unknown char returns 0
- Verify: hex_to_digit unknown char returns 0
   - Expected: hex_to_digit("z") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hex_to_digit unknown char returns 0")
step("Verify: hex_to_digit unknown char returns 0")
expect(hex_to_digit("z")).to_equal(0)
```

</details>

#### hex_to_digit uppercase A

- hex_to_digit uppercase A
- Verify: hex_to_digit uppercase A
   - Expected: hex_to_digit("A") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hex_to_digit uppercase A")
step("Verify: hex_to_digit uppercase A")
expect(hex_to_digit("A")).to_equal(10)
```

</details>

#### hex_to_digit uppercase F

- hex_to_digit uppercase F
- Verify: hex_to_digit uppercase F
   - Expected: hex_to_digit("F") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hex_to_digit uppercase F")
step("Verify: hex_to_digit uppercase F")
expect(hex_to_digit("F")).to_equal(15)
```

</details>

### serialize_bool text

#### serializes true

- serializes true
- Verify: serializes true
   - Expected: serialize_bool(true) equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes true")
step("Verify: serializes true")
expect(serialize_bool(true)).to_equal("true")
```

</details>

#### serializes false

- serializes false
- Verify: serializes false
   - Expected: serialize_bool(false) equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes false")
step("Verify: serializes false")
expect(serialize_bool(false)).to_equal("false")
```

</details>

### to_sdn_bool both branches

#### converts true to SDN

- converts true to SDN
- Verify: converts true to SDN
   - Expected: to_sdn_bool(true) equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts true to SDN")
step("Verify: converts true to SDN")
expect(to_sdn_bool(true)).to_equal("true")
```

</details>

#### converts false to SDN

- converts false to SDN
- Verify: converts false to SDN
   - Expected: to_sdn_bool(false) equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts false to SDN")
step("Verify: converts false to SDN")
expect(to_sdn_bool(false)).to_equal("false")
```

</details>

### add_version and schema

#### adds version to simple data

- adds version to simple data
- Verify: adds version to simple data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds version to simple data")
step("Verify: adds version to simple data")
val result = add_version("data", 1)
expect(result).to_contain("v: 1")
expect(result).to_contain("data")
```

</details>

#### defines empty schema

- defines empty schema
- Verify: defines empty schema
   - Expected: result equals `\{\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines empty schema")
step("Verify: defines empty schema")
val result = define_schema([])
expect(result).to_equal("\{\}")
```

</details>

### serialize_nil text

#### returns nil string

- returns nil string
- Verify: returns nil string
   - Expected: serialize_nil() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil string")
step("Verify: returns nil string")
expect(serialize_nil()).to_equal("nil")
```

</details>

### to_sdn_nil

#### returns nil string

- returns nil string
- Verify: returns nil string
   - Expected: to_sdn_nil() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil string")
step("Verify: returns nil string")
expect(to_sdn_nil()).to_equal("nil")
```

</details>

### char_code_safe special symbols

#### handles dollar sign

- handles dollar sign
- Verify: handles dollar sign
   - Expected: char_code_safe("$") equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles dollar sign")
step("Verify: handles dollar sign")
expect(char_code_safe("$")).to_equal(36)
```

</details>

#### handles percent

- handles percent
- Verify: handles percent
   - Expected: char_code_safe("%") equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles percent")
step("Verify: handles percent")
expect(char_code_safe("%")).to_equal(37)
```

</details>

#### handles ampersand

- handles ampersand
- Verify: handles ampersand
   - Expected: char_code_safe("&") equals `38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles ampersand")
step("Verify: handles ampersand")
expect(char_code_safe("&")).to_equal(38)
```

</details>

#### handles single quote

- handles single quote
- Verify: handles single quote
   - Expected: char_code_safe("'") equals `39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single quote")
step("Verify: handles single quote")
expect(char_code_safe("'")).to_equal(39)
```

</details>

#### handles open paren

- handles open paren
- Verify: handles open paren
   - Expected: char_code_safe("(") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles open paren")
step("Verify: handles open paren")
expect(char_code_safe("(")).to_equal(40)
```

</details>

#### handles close paren

- handles close paren
- Verify: handles close paren
   - Expected: char_code_safe(")") equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles close paren")
step("Verify: handles close paren")
expect(char_code_safe(")")).to_equal(41)
```

</details>

#### handles asterisk

- handles asterisk
- Verify: handles asterisk
   - Expected: char_code_safe("*") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles asterisk")
step("Verify: handles asterisk")
expect(char_code_safe("*")).to_equal(42)
```

</details>

#### handles plus

- handles plus
- Verify: handles plus
   - Expected: char_code_safe("+") equals `43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles plus")
step("Verify: handles plus")
expect(char_code_safe("+")).to_equal(43)
```

</details>

#### handles comma

- handles comma
- Verify: handles comma
   - Expected: char_code_safe(",") equals `44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles comma")
step("Verify: handles comma")
expect(char_code_safe(",")).to_equal(44)
```

</details>

#### handles hyphen

- handles hyphen
- Verify: handles hyphen
   - Expected: char_code_safe("-") equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles hyphen")
step("Verify: handles hyphen")
expect(char_code_safe("-")).to_equal(45)
```

</details>

#### handles period

- handles period
- Verify: handles period
   - Expected: char_code_safe(".") equals `46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles period")
step("Verify: handles period")
expect(char_code_safe(".")).to_equal(46)
```

</details>

#### handles slash

- handles slash
- Verify: handles slash
   - Expected: char_code_safe("/") equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles slash")
step("Verify: handles slash")
expect(char_code_safe("/")).to_equal(47)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 155 |
| Active scenarios | 155 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bddbc939a3b9c753e2a2c6b2f9a4603a490f8a83429bee40d4b0e555adfb34dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bddbc939a3b9c753e2a2c6b2f9a4603a490f8a83429bee40d4b0e555adfb34dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bddbc939a3b9c753e2a2c6b2f9a4603a490f8a83429bee40d4b0e555adfb34dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/serialization_extended_spec.spl
mirror: doc/06_spec/unit/lib/common/serialization_extended_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/serialization_extended_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/serialization_extended_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/serialization_extended_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/serialization_extended_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pretty prints nested list at indent 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/serialization_extended_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pretty prints nested tuple at indent 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/serialization_extended_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pretty prints nested dict at indent 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
