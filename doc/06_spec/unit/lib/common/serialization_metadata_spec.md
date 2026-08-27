# Serialization Metadata Coverage Specification

> Branch-coverage tests for metadata, tagging, versioning, schema, cloning, hashing, compression/encryption markers, binary I/O, and hex encoding:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 99 | 99 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Metadata Coverage Specification

Branch-coverage tests for metadata, tagging, versioning, schema, cloning, hashing, compression/encryption markers, binary I/O, and hex encoding:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-METADATA |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/lib/common/serialization_metadata_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch-coverage tests for metadata, tagging, versioning, schema, cloning, hashing,
compression/encryption markers, binary I/O, and hex encoding:
- Type tagging: tag_type, get_type_tag, strip_type_tag (utilities.spl)
- Schema validation: define_schema, validate_field_type (utilities.spl)
- Versioning: add_version, get_version, strip_version (utilities.spl)
- Deep cloning, equality, structural hashing (utilities.spl)
- Compression/encryption markers (utilities.spl)
- Binary I/O: write_bytes, read_bytes (serialize.spl)
- Hex encoding: int_to_hex, bytes_to_hex, hex_to_bytes (serialize.spl)

## Scenarios

### tag_type

#### wraps content with type annotation

- wraps content with type annotation
   - Expected: result equals `@MyType\{payload\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps content with type annotation")
val result = tag_type("payload", "MyType")
expect(result).to_equal("@MyType\{payload\}")
```

</details>

### get_type_tag

#### extracts tag from tagged string

- extracts tag from tagged string
   - Expected: result equals `MyType`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts tag from tagged string")
val result = get_type_tag("@MyType\{payload\}")
expect(result).to_equal("MyType")
```

</details>

#### returns nil for short string

- returns nil for short string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for short string")
val result = get_type_tag("ab")
expect(result).to_be_nil()
```

</details>

#### returns nil when not starting with @

- returns nil when not starting with @


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when not starting with @")
val result = get_type_tag("NoAt\{payload\}")
expect(result).to_be_nil()
```

</details>

#### returns nil when no opening brace

- returns nil when no opening brace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when no opening brace")
val result = get_type_tag("@NobraceHere")
expect(result).to_be_nil()
```

</details>

### strip_type_tag

#### strips tag and returns inner content

- strips tag and returns inner content
   - Expected: result equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips tag and returns inner content")
val result = strip_type_tag("@MyType\{payload\}")
expect(result).to_equal("payload")
```

</details>

#### returns original when no tag present

- returns original when no tag present
   - Expected: result equals `notatag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original when no tag present")
val result = strip_type_tag("notatag")
expect(result).to_equal("notatag")
```

</details>

#### returns original for short input

- returns original for short input
   - Expected: result equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original for short input")
val result = strip_type_tag("ab")
expect(result).to_equal("ab")
```

</details>

### define_schema

#### creates dict representation of schema

- creates dict representation of schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates dict representation of schema")
val result = define_schema([("name", "text"), ("age", "int")])
expect(result).to_contain("name: text")
expect(result).to_contain("age: int")
```

</details>

### validate_field_type

#### validates int type

- validates int type
   - Expected: validate_field_type("42", "int") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates int type")
expect(validate_field_type("42", "int")).to_equal(true)
```

</details>

#### rejects non-numeric as int

- rejects non-numeric as int
   - Expected: validate_field_type("abc", "int") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-numeric as int")
expect(validate_field_type("abc", "int")).to_equal(false)
```

</details>

#### validates true as bool

- validates true as bool
   - Expected: validate_field_type("true", "bool") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates true as bool")
expect(validate_field_type("true", "bool")).to_equal(true)
```

</details>

#### validates false as bool

- validates false as bool
   - Expected: validate_field_type("false", "bool") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates false as bool")
expect(validate_field_type("false", "bool")).to_equal(true)
```

</details>

#### rejects non-bool as bool

- rejects non-bool as bool
   - Expected: validate_field_type("42", "bool") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-bool as bool")
expect(validate_field_type("42", "bool")).to_equal(false)
```

</details>

#### validates nil type

- validates nil type
   - Expected: validate_field_type("nil", "nil") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates nil type")
expect(validate_field_type("nil", "nil")).to_equal(true)
```

</details>

#### rejects non-nil as nil

- rejects non-nil as nil
   - Expected: validate_field_type("42", "nil") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-nil as nil")
expect(validate_field_type("42", "nil")).to_equal(false)
```

</details>

#### validates text type by leading quote

- validates text type by leading quote
   - Expected: validate_field_type("\"hello\"", "text") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates text type by leading quote")
expect(validate_field_type("\"hello\"", "text")).to_equal(true)
```

</details>

#### rejects non-quoted as text

- rejects non-quoted as text
   - Expected: validate_field_type("hello", "text") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-quoted as text")
expect(validate_field_type("hello", "text")).to_equal(false)
```

</details>

#### validates list type by leading bracket

- validates list type by leading bracket
   - Expected: validate_field_type("[1, 2]", "list") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates list type by leading bracket")
expect(validate_field_type("[1, 2]", "list")).to_equal(true)
```

</details>

#### rejects non-list as list

- rejects non-list as list
   - Expected: validate_field_type("42", "list") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-list as list")
expect(validate_field_type("42", "list")).to_equal(false)
```

</details>

#### validates tuple type by leading paren

- validates tuple type by leading paren
   - Expected: validate_field_type("(1, 2)", "tuple") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates tuple type by leading paren")
expect(validate_field_type("(1, 2)", "tuple")).to_equal(true)
```

</details>

#### rejects non-tuple as tuple

- rejects non-tuple as tuple
   - Expected: validate_field_type("42", "tuple") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-tuple as tuple")
expect(validate_field_type("42", "tuple")).to_equal(false)
```

</details>

#### validates dict type by leading brace

- validates dict type by leading brace
   - Expected: validate_field_type("{k: v}", "dict") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates dict type by leading brace")
expect(validate_field_type("{k: v}", "dict")).to_equal(true)
```

</details>

#### rejects non-dict as dict

- rejects non-dict as dict
   - Expected: validate_field_type("42", "dict") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-dict as dict")
expect(validate_field_type("42", "dict")).to_equal(false)
```

</details>

#### returns true for unknown type

- returns true for unknown type
   - Expected: validate_field_type("anything", "custom_type") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for unknown type")
expect(validate_field_type("anything", "custom_type")).to_equal(true)
```

</details>

### add_version

#### wraps data with version number

- wraps data with version number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps data with version number")
val result = add_version("[1, 2]", 3)
expect(result).to_contain("v: 3")
expect(result).to_contain("data: [1, 2]")
```

</details>

### get_version

#### extracts version from versioned string

- extracts version from versioned string
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts version from versioned string")
val versioned = add_version("data", 5)
val result = get_version(versioned)
expect(result).to_equal(5)
```

</details>

#### returns nil for non-versioned string

- returns nil for non-versioned string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for non-versioned string")
val result = get_version("not versioned")
expect(result).to_be_nil()
```

</details>

#### returns nil for empty string

- returns nil for empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty string")
val result = get_version("")
expect(result).to_be_nil()
```

</details>

### strip_version

#### strips version and returns inner data

- strips version and returns inner data
   - Expected: result equals `[1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips version and returns inner data")
val versioned = add_version("[1, 2]", 1)
val result = strip_version(versioned)
expect(result).to_equal("[1, 2]")
```

</details>

#### returns original for non-versioned input

- returns original for non-versioned input
   - Expected: result equals `plain data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original for non-versioned input")
val result = strip_version("plain data")
expect(result).to_equal("plain data")
```

</details>

### parse_int_safe

#### returns 0 for empty string

- returns 0 for empty string
   - Expected: parse_int_safe("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty string")
expect(parse_int_safe("")).to_equal(0)
```

</details>

#### parses positive integer

- parses positive integer
   - Expected: parse_int_safe("42") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses positive integer")
expect(parse_int_safe("42")).to_equal(42)
```

</details>

#### parses negative integer

- parses negative integer
   - Expected: parse_int_safe("-7") equals `-7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses negative integer")
expect(parse_int_safe("-7")).to_equal(-7)
```

</details>

#### stops parsing at non-digit

- stops parsing at non-digit
   - Expected: parse_int_safe("12abc") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops parsing at non-digit")
expect(parse_int_safe("12abc")).to_equal(12)
```

</details>

#### parses zero

- parses zero
   - Expected: parse_int_safe("0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses zero")
expect(parse_int_safe("0")).to_equal(0)
```

</details>

### char_to_digit_safe

#### converts all digit characters

- converts all digit characters
   - Expected: char_to_digit_safe("0") equals `0`
   - Expected: char_to_digit_safe("1") equals `1`
   - Expected: char_to_digit_safe("2") equals `2`
   - Expected: char_to_digit_safe("3") equals `3`
   - Expected: char_to_digit_safe("4") equals `4`
   - Expected: char_to_digit_safe("5") equals `5`
   - Expected: char_to_digit_safe("6") equals `6`
   - Expected: char_to_digit_safe("7") equals `7`
   - Expected: char_to_digit_safe("8") equals `8`
   - Expected: char_to_digit_safe("9") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts all digit characters")
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

#### returns 0 for non-digit

- returns 0 for non-digit
   - Expected: char_to_digit_safe("x") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for non-digit")
expect(char_to_digit_safe("x")).to_equal(0)
```

</details>

### Deep Cloning

#### clones integer

- clones integer
   - Expected: deep_clone_int(42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones integer")
expect(deep_clone_int(42)).to_equal(42)
```

</details>

#### clones boolean true

- clones boolean true
   - Expected: deep_clone_bool(true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones boolean true")
expect(deep_clone_bool(true)).to_equal(true)
```

</details>

#### clones boolean false

- clones boolean false
   - Expected: deep_clone_bool(false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones boolean false")
expect(deep_clone_bool(false)).to_equal(false)
```

</details>

#### clones text

- clones text
   - Expected: deep_clone_text("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones text")
expect(deep_clone_text("hello")).to_equal("hello")
```

</details>

#### clones int list

- clones int list
   - Expected: deep_equal_list_int(original, cloned) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones int list")
val original = [1, 2, 3]
val cloned = deep_clone_list_int(original)
expect(deep_equal_list_int(original, cloned)).to_equal(true)
```

</details>

#### clones text list

- clones text list
   - Expected: deep_equal_list_text(original, cloned) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones text list")
val original = ["a", "b"]
val cloned = deep_clone_list_text(original)
expect(deep_equal_list_text(original, cloned)).to_equal(true)
```

</details>

#### clones empty int list

- clones empty int list
   - Expected: cloned.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones empty int list")
val cloned = deep_clone_list_int([])
expect(cloned.len()).to_equal(0)
```

</details>

#### clones empty text list

- clones empty text list
   - Expected: cloned.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones empty text list")
val cloned = deep_clone_list_text([])
expect(cloned.len()).to_equal(0)
```

</details>

### Shallow Cloning

#### shallow clones int list

- shallow clones int list
   - Expected: deep_equal_list_int(original, cloned) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shallow clones int list")
val original = [10, 20]
val cloned = shallow_clone_list_int(original)
expect(deep_equal_list_int(original, cloned)).to_equal(true)
```

</details>

#### shallow clones text list

- shallow clones text list
   - Expected: deep_equal_list_text(original, cloned) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shallow clones text list")
val original = ["x", "y"]
val cloned = shallow_clone_list_text(original)
expect(deep_equal_list_text(original, cloned)).to_equal(true)
```

</details>

### Deep Equality

#### compares equal integers

- compares equal integers
   - Expected: deep_equal_int(5, 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal integers")
expect(deep_equal_int(5, 5)).to_equal(true)
```

</details>

#### compares unequal integers

- compares unequal integers
   - Expected: deep_equal_int(5, 6) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares unequal integers")
expect(deep_equal_int(5, 6)).to_equal(false)
```

</details>

#### compares equal booleans

- compares equal booleans
   - Expected: deep_equal_bool(true, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal booleans")
expect(deep_equal_bool(true, true)).to_equal(true)
```

</details>

#### compares unequal booleans

- compares unequal booleans
   - Expected: deep_equal_bool(true, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares unequal booleans")
expect(deep_equal_bool(true, false)).to_equal(false)
```

</details>

#### compares equal text

- compares equal text
   - Expected: deep_equal_text("abc", "abc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal text")
expect(deep_equal_text("abc", "abc")).to_equal(true)
```

</details>

#### compares unequal text

- compares unequal text
   - Expected: deep_equal_text("abc", "xyz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares unequal text")
expect(deep_equal_text("abc", "xyz")).to_equal(false)
```

</details>

#### compares equal int lists

- compares equal int lists
   - Expected: deep_equal_list_int([1, 2], [1, 2]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal int lists")
expect(deep_equal_list_int([1, 2], [1, 2])).to_equal(true)
```

</details>

#### compares unequal int lists by element

- compares unequal int lists by element
   - Expected: deep_equal_list_int([1, 2], [1, 3]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares unequal int lists by element")
expect(deep_equal_list_int([1, 2], [1, 3])).to_equal(false)
```

</details>

#### compares int lists of different lengths

- compares int lists of different lengths
   - Expected: deep_equal_list_int([1], [1, 2]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares int lists of different lengths")
expect(deep_equal_list_int([1], [1, 2])).to_equal(false)
```

</details>

#### compares empty int lists

- compares empty int lists
   - Expected: deep_equal_list_int([], []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares empty int lists")
expect(deep_equal_list_int([], [])).to_equal(true)
```

</details>

#### compares equal text lists

- compares equal text lists
   - Expected: deep_equal_list_text(["a", "b"], ["a", "b"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal text lists")
expect(deep_equal_list_text(["a", "b"], ["a", "b"])).to_equal(true)
```

</details>

#### compares unequal text lists by element

- compares unequal text lists by element
   - Expected: deep_equal_list_text(["a"], ["b"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares unequal text lists by element")
expect(deep_equal_list_text(["a"], ["b"])).to_equal(false)
```

</details>

#### compares text lists of different lengths

- compares text lists of different lengths
   - Expected: deep_equal_list_text(["a"], ["a", "b"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares text lists of different lengths")
expect(deep_equal_list_text(["a"], ["a", "b"])).to_equal(false)
```

</details>

#### compares empty text lists

- compares empty text lists
   - Expected: deep_equal_list_text([], []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares empty text lists")
expect(deep_equal_list_text([], [])).to_equal(true)
```

</details>

### Structural Hashing

#### hashes integer deterministically

- hashes integer deterministically
   - Expected: h1 equals `h2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes integer deterministically")
val h1 = structural_hash_int(42)
val h2 = structural_hash_int(42)
expect(h1).to_equal(h2)
```

</details>

#### hashes different integers differently

- hashes different integers differently


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes different integers differently")
val h1 = structural_hash_int(1)
val h2 = structural_hash_int(2)
expect(h1).to_not_equal(h2)
```

</details>

#### hashes true and false differently

- hashes true and false differently


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes true and false differently")
val h_true = structural_hash_bool(true)
val h_false = structural_hash_bool(false)
expect(h_true).to_not_equal(h_false)
```

</details>

#### hashes bool true to 1

- hashes bool true to 1
   - Expected: structural_hash_bool(true) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes bool true to 1")
expect(structural_hash_bool(true)).to_equal(1)
```

</details>

#### hashes bool false to 0

- hashes bool false to 0
   - Expected: structural_hash_bool(false) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes bool false to 0")
expect(structural_hash_bool(false)).to_equal(0)
```

</details>

#### hashes empty text to seed value

- hashes empty text to seed value
   - Expected: h equals `2166136261`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes empty text to seed value")
val h = structural_hash_text("")
expect(h).to_equal(2166136261)
```

</details>

#### hashes single char text without overflow

- hashes single char text without overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes single char text without overflow")
val h = structural_hash_text("a")
expect(h).to_not_equal(0)
```

</details>

#### hashes empty int list to seed value

- hashes empty int list to seed value
   - Expected: h equals `2166136261`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes empty int list to seed value")
val h = structural_hash_list_int([])
expect(h).to_equal(2166136261)
```

</details>

#### hashes single element int list

- hashes single element int list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes single element int list")
val h = structural_hash_list_int([1])
expect(h).to_not_equal(0)
```

</details>

#### hashes empty text list to seed value

- hashes empty text list to seed value
   - Expected: h equals `2166136261`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes empty text list to seed value")
val h = structural_hash_list_text([])
expect(h).to_equal(2166136261)
```

</details>

#### combines hashes

- combines hashes
   - Expected: combined equals `100 * 31 + 200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines hashes")
val combined = combine_hashes(100, 200)
expect(combined).to_equal(100 * 31 + 200)
```

</details>

### Compression Markers

#### marks data as compressed

- marks data as compressed
   - Expected: result equals `@Compressed\{payload\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks data as compressed")
val result = mark_compressed("payload")
expect(result).to_equal("@Compressed\{payload\}")
```

</details>

#### detects compressed data

- detects compressed data
   - Expected: is_compressed(marked) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects compressed data")
val marked = mark_compressed("payload")
expect(is_compressed(marked)).to_equal(true)
```

</details>

#### returns false for non-compressed data

- returns false for non-compressed data
   - Expected: is_compressed("plain") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-compressed data")
expect(is_compressed("plain")).to_equal(false)
```

</details>

#### returns false for short input

- returns false for short input
   - Expected: is_compressed("ab") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for short input")
expect(is_compressed("ab")).to_equal(false)
```

</details>

### Encryption Markers

#### marks data as encrypted

- marks data as encrypted
   - Expected: result equals `@Encrypted\{payload\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks data as encrypted")
val result = mark_encrypted("payload")
expect(result).to_equal("@Encrypted\{payload\}")
```

</details>

#### detects encrypted data

- detects encrypted data
   - Expected: is_encrypted(marked) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects encrypted data")
val marked = mark_encrypted("payload")
expect(is_encrypted(marked)).to_equal(true)
```

</details>

#### returns false for non-encrypted data

- returns false for non-encrypted data
   - Expected: is_encrypted("plain") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-encrypted data")
expect(is_encrypted("plain")).to_equal(false)
```

</details>

#### returns false for short input

- returns false for short input
   - Expected: is_encrypted("ab") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for short input")
expect(is_encrypted("ab")).to_equal(false)
```

</details>

### write_bytes

#### prepends length as varint

- prepends length as varint
   - Expected: result[0] equals `3`
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prepends length as varint")
val result = write_bytes([10, 20, 30])
expect(result[0]).to_equal(3)
expect(result.len()).to_equal(4)
```

</details>

#### writes empty byte array

- writes empty byte array
   - Expected: result[0] equals `0`
   - Expected: result.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes empty byte array")
val result = write_bytes([])
expect(result[0]).to_equal(0)
expect(result.len()).to_equal(1)
```

</details>

### read_bytes

#### reads specified number of bytes

- reads specified number of bytes
   - Expected: bytes.len() equals `3`
   - Expected: bytes[0] equals `20`
   - Expected: bytes[1] equals `30`
   - Expected: bytes[2] equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads specified number of bytes")
val data = [10, 20, 30, 40, 50]
val result = read_bytes(data, 1, 3)
val bytes = result.0
expect(bytes.len()).to_equal(3)
expect(bytes[0]).to_equal(20)
expect(bytes[1]).to_equal(30)
expect(bytes[2]).to_equal(40)
```

</details>

#### handles read beyond array bounds

- handles read beyond array bounds
   - Expected: bytes.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles read beyond array bounds")
val data = [10, 20]
val result = read_bytes(data, 0, 5)
val bytes = result.0
expect(bytes.len()).to_equal(2)
```

</details>

#### reads zero bytes

- reads zero bytes
   - Expected: bytes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads zero bytes")
val result = read_bytes([1, 2, 3], 0, 0)
val bytes = result.0
expect(bytes.len()).to_equal(0)
```

</details>

### read_bytes_with_length

#### roundtrips with write_bytes

- roundtrips with write_bytes
   - Expected: data.len() equals `3`
   - Expected: data[0] equals `65`
   - Expected: data[1] equals `66`
   - Expected: data[2] equals `67`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips with write_bytes")
val original = [65, 66, 67]
val written = write_bytes(original)
val result = read_bytes_with_length(written, 0)
val data = result.0
val consumed = result.1
expect(data.len()).to_equal(3)
expect(data[0]).to_equal(65)
expect(data[1]).to_equal(66)
expect(data[2]).to_equal(67)
```

</details>

### int_to_hex

#### converts zero

- converts zero
   - Expected: int_to_hex(0) equals `00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts zero")
expect(int_to_hex(0)).to_equal("00")
```

</details>

#### converts single digit

- converts single digit
   - Expected: int_to_hex(10) equals `0a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts single digit")
expect(int_to_hex(10)).to_equal("0a")
```

</details>

#### converts 255

- converts 255
   - Expected: int_to_hex(255) equals `ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts 255")
expect(int_to_hex(255)).to_equal("ff")
```

</details>

#### converts mid-range value

- converts mid-range value
   - Expected: int_to_hex(171) equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts mid-range value")
expect(int_to_hex(171)).to_equal("ab")
```

</details>

### bytes_to_hex

#### converts empty byte array

- converts empty byte array
   - Expected: bytes_to_hex([]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts empty byte array")
expect(bytes_to_hex([])).to_equal("")
```

</details>

#### converts single byte

- converts single byte
   - Expected: bytes_to_hex([255]) equals `ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts single byte")
expect(bytes_to_hex([255])).to_equal("ff")
```

</details>

#### converts multiple bytes

- converts multiple bytes
   - Expected: bytes_to_hex([0, 171, 255]) equals `00abff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts multiple bytes")
expect(bytes_to_hex([0, 171, 255])).to_equal("00abff")
```

</details>

### hex_to_bytes

#### converts empty hex string

- converts empty hex string
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts empty hex string")
val result = hex_to_bytes("")
expect(result.len()).to_equal(0)
```

</details>

#### converts valid hex pairs

- converts valid hex pairs
   - Expected: result.len() equals `3`
   - Expected: result[0] equals `0`
   - Expected: result[1] equals `171`
   - Expected: result[2] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts valid hex pairs")
val result = hex_to_bytes("00abff")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(0)
expect(result[1]).to_equal(171)
expect(result[2]).to_equal(255)
```

</details>

#### handles uppercase hex

- handles uppercase hex
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `171`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles uppercase hex")
val result = hex_to_bytes("AB")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(171)
```

</details>

#### handles odd-length hex string by skipping trailing nibble

- handles odd-length hex string by skipping trailing nibble
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `171`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles odd-length hex string by skipping trailing nibble")
val result = hex_to_bytes("abc")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(171)
```

</details>

#### roundtrips with bytes_to_hex

- roundtrips with bytes_to_hex
   - Expected: deep_equal_list_int(original, roundtripped) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips with bytes_to_hex")
val original = [0, 42, 255, 128]
val roundtripped = hex_to_bytes(bytes_to_hex(original))
expect(deep_equal_list_int(original, roundtripped)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 99 |
| Active scenarios | 99 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `54bbda4c419116613879d6942e2965f74688a0ebed9f09581d14d170866e6170`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54bbda4c419116613879d6942e2965f74688a0ebed9f09581d14d170866e6170`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54bbda4c419116613879d6942e2965f74688a0ebed9f09581d14d170866e6170`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/serialization_metadata_spec.spl
mirror: doc/06_spec/unit/lib/common/serialization_metadata_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/serialization_metadata_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/serialization_metadata_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/serialization_metadata_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 48 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/serialization_metadata_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps content with type annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/serialization_metadata_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts tag from tagged string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/serialization_metadata_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for short string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
