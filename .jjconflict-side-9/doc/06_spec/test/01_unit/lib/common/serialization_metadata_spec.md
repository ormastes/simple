# Serialization Metadata Coverage Specification

> Branch-coverage tests for metadata, tagging, versioning, schema, cloning, hashing, compression/encryption markers, binary I/O, and hex encoding:

<!-- sdn-diagram:id=serialization_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serialization_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serialization_metadata_spec -> serialization
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serialization_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/common/serialization_metadata_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tag_type("payload", "MyType")
expect(result).to_equal("@MyType\{payload\}")
```

</details>

### get_type_tag

#### extracts tag from tagged string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("@MyType\{payload\}")
expect(result).to_equal("MyType")
```

</details>

#### returns nil for short string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("ab")
expect(result).to_be_nil()
```

</details>

#### returns nil when not starting with @

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("NoAt\{payload\}")
expect(result).to_be_nil()
```

</details>

#### returns nil when no opening brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_type_tag("@NobraceHere")
expect(result).to_be_nil()
```

</details>

### strip_type_tag

#### strips tag and returns inner content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("@MyType\{payload\}")
expect(result).to_equal("payload")
```

</details>

#### returns original when no tag present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("notatag")
expect(result).to_equal("notatag")
```

</details>

#### returns original for short input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_type_tag("ab")
expect(result).to_equal("ab")
```

</details>

### define_schema

#### creates dict representation of schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = define_schema([("name", "text"), ("age", "int")])
expect(result).to_contain("name: text")
expect(result).to_contain("age: int")
```

</details>

### validate_field_type

#### validates int type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("42", "int")).to_equal(true)
```

</details>

#### rejects non-numeric as int

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("abc", "int")).to_equal(false)
```

</details>

#### validates true as bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("true", "bool")).to_equal(true)
```

</details>

#### validates false as bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("false", "bool")).to_equal(true)
```

</details>

#### rejects non-bool as bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("42", "bool")).to_equal(false)
```

</details>

#### validates nil type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("nil", "nil")).to_equal(true)
```

</details>

#### rejects non-nil as nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("42", "nil")).to_equal(false)
```

</details>

#### validates text type by leading quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("\"hello\"", "text")).to_equal(true)
```

</details>

#### rejects non-quoted as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("hello", "text")).to_equal(false)
```

</details>

#### validates list type by leading bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("[1, 2]", "list")).to_equal(true)
```

</details>

#### rejects non-list as list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("42", "list")).to_equal(false)
```

</details>

#### validates tuple type by leading paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("(1, 2)", "tuple")).to_equal(true)
```

</details>

#### rejects non-tuple as tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("42", "tuple")).to_equal(false)
```

</details>

#### validates dict type by leading brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("{k: v}", "dict")).to_equal(true)
```

</details>

#### rejects non-dict as dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("42", "dict")).to_equal(false)
```

</details>

#### returns true for unknown type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_field_type("anything", "custom_type")).to_equal(true)
```

</details>

### add_version

#### wraps data with version number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_version("[1, 2]", 3)
expect(result).to_contain("v: 3")
expect(result).to_contain("data: [1, 2]")
```

</details>

### get_version

#### extracts version from versioned string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versioned = add_version("data", 5)
val result = get_version(versioned)
expect(result).to_equal(5)
```

</details>

#### returns nil for non-versioned string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_version("not versioned")
expect(result).to_be_nil()
```

</details>

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

### strip_version

#### strips version and returns inner data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versioned = add_version("[1, 2]", 1)
val result = strip_version(versioned)
expect(result).to_equal("[1, 2]")
```

</details>

#### returns original for non-versioned input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_version("plain data")
expect(result).to_equal("plain data")
```

</details>

### parse_int_safe

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("")).to_equal(0)
```

</details>

#### parses positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("42")).to_equal(42)
```

</details>

#### parses negative integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("-7")).to_equal(-7)
```

</details>

#### stops parsing at non-digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int_safe("12abc")).to_equal(12)
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

### char_to_digit_safe

#### converts all digit characters

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

#### returns 0 for non-digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_to_digit_safe("x")).to_equal(0)
```

</details>

### Deep Cloning

#### clones integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_clone_int(42)).to_equal(42)
```

</details>

#### clones boolean true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_clone_bool(true)).to_equal(true)
```

</details>

#### clones boolean false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_clone_bool(false)).to_equal(false)
```

</details>

#### clones text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_clone_text("hello")).to_equal("hello")
```

</details>

#### clones int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [1, 2, 3]
val cloned = deep_clone_list_int(original)
expect(deep_equal_list_int(original, cloned)).to_equal(true)
```

</details>

#### clones text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = ["a", "b"]
val cloned = deep_clone_list_text(original)
expect(deep_equal_list_text(original, cloned)).to_equal(true)
```

</details>

#### clones empty int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = deep_clone_list_int([])
expect(cloned.len()).to_equal(0)
```

</details>

#### clones empty text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = deep_clone_list_text([])
expect(cloned.len()).to_equal(0)
```

</details>

### Shallow Cloning

#### shallow clones int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [10, 20]
val cloned = shallow_clone_list_int(original)
expect(deep_equal_list_int(original, cloned)).to_equal(true)
```

</details>

#### shallow clones text list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = ["x", "y"]
val cloned = shallow_clone_list_text(original)
expect(deep_equal_list_text(original, cloned)).to_equal(true)
```

</details>

### Deep Equality

#### compares equal integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_int(5, 5)).to_equal(true)
```

</details>

#### compares unequal integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_int(5, 6)).to_equal(false)
```

</details>

#### compares equal booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_bool(true, true)).to_equal(true)
```

</details>

#### compares unequal booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_bool(true, false)).to_equal(false)
```

</details>

#### compares equal text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_text("abc", "abc")).to_equal(true)
```

</details>

#### compares unequal text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_text("abc", "xyz")).to_equal(false)
```

</details>

#### compares equal int lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([1, 2], [1, 2])).to_equal(true)
```

</details>

#### compares unequal int lists by element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([1, 2], [1, 3])).to_equal(false)
```

</details>

#### compares int lists of different lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([1], [1, 2])).to_equal(false)
```

</details>

#### compares empty int lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_int([], [])).to_equal(true)
```

</details>

#### compares equal text lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_text(["a", "b"], ["a", "b"])).to_equal(true)
```

</details>

#### compares unequal text lists by element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_text(["a"], ["b"])).to_equal(false)
```

</details>

#### compares text lists of different lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_text(["a"], ["a", "b"])).to_equal(false)
```

</details>

#### compares empty text lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(deep_equal_list_text([], [])).to_equal(true)
```

</details>

### Structural Hashing

#### hashes integer deterministically

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = structural_hash_int(42)
val h2 = structural_hash_int(42)
expect(h1).to_equal(h2)
```

</details>

#### hashes different integers differently

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = structural_hash_int(1)
val h2 = structural_hash_int(2)
expect(h1 == h2).to_equal(false)
```

</details>

#### hashes true and false differently

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h_true = structural_hash_bool(true)
val h_false = structural_hash_bool(false)
expect(h_true == h_false).to_equal(false)
```

</details>

#### hashes bool true to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(structural_hash_bool(true)).to_equal(1)
```

</details>

#### hashes bool false to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(structural_hash_bool(false)).to_equal(0)
```

</details>

#### hashes empty text to seed value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_text("")
expect(h).to_equal(2166136261)
```

</details>

#### hashes single char text without overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_text("a")
expect(h == 0).to_equal(false)
```

</details>

#### hashes empty int list to seed value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_list_int([])
expect(h).to_equal(2166136261)
```

</details>

#### hashes single element int list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_list_int([1])
expect(h == 0).to_equal(false)
```

</details>

#### hashes empty text list to seed value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = structural_hash_list_text([])
expect(h).to_equal(2166136261)
```

</details>

#### combines hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = combine_hashes(100, 200)
expect(combined).to_equal(100 * 31 + 200)
```

</details>

### Compression Markers

#### marks data as compressed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mark_compressed("payload")
expect(result).to_equal("@Compressed\{payload\}")
```

</details>

#### detects compressed data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marked = mark_compressed("payload")
expect(is_compressed(marked)).to_equal(true)
```

</details>

#### returns false for non-compressed data

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed("plain")).to_equal(false)
```

</details>

#### returns false for short input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed("ab")).to_equal(false)
```

</details>

### Encryption Markers

#### marks data as encrypted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mark_encrypted("payload")
expect(result).to_equal("@Encrypted\{payload\}")
```

</details>

#### detects encrypted data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marked = mark_encrypted("payload")
expect(is_encrypted(marked)).to_equal(true)
```

</details>

#### returns false for non-encrypted data

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_encrypted("plain")).to_equal(false)
```

</details>

#### returns false for short input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_encrypted("ab")).to_equal(false)
```

</details>

### write_bytes

#### prepends length as varint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_bytes([10, 20, 30])
expect(result[0]).to_equal(3)
expect(result.len()).to_equal(4)
```

</details>

#### writes empty byte array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = write_bytes([])
expect(result[0]).to_equal(0)
expect(result.len()).to_equal(1)
```

</details>

### read_bytes

#### reads specified number of bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [10, 20]
val result = read_bytes(data, 0, 5)
val bytes = result.0
expect(bytes.len()).to_equal(2)
```

</details>

#### reads zero bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_bytes([1, 2, 3], 0, 0)
val bytes = result.0
expect(bytes.len()).to_equal(0)
```

</details>

### read_bytes_with_length

#### roundtrips with write_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(0)).to_equal("00")
```

</details>

#### converts single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(10)).to_equal("0a")
```

</details>

#### converts 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(255)).to_equal("ff")
```

</details>

#### converts mid-range value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(int_to_hex(171)).to_equal("ab")
```

</details>

### bytes_to_hex

#### converts empty byte array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex([])).to_equal("")
```

</details>

#### converts single byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex([255])).to_equal("ff")
```

</details>

#### converts multiple bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex([0, 171, 255])).to_equal("00abff")
```

</details>

### hex_to_bytes

#### converts empty hex string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_bytes("")
expect(result.len()).to_equal(0)
```

</details>

#### converts valid hex pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_bytes("00abff")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(0)
expect(result[1]).to_equal(171)
expect(result[2]).to_equal(255)
```

</details>

#### handles uppercase hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_bytes("AB")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(171)
```

</details>

#### handles odd-length hex string by skipping trailing nibble

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_bytes("abc")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal(171)
```

</details>

#### roundtrips with bytes_to_hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
