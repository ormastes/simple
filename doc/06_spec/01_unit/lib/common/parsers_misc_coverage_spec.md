# Parsers Coverage Specification

> Purpose: Prove that YAML Types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 123 | 123 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parsers Coverage Specification

Purpose: Prove that YAML Types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-JSON-SDN-YAML |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/parsers_misc_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that YAML Types.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### YAML Types

#### constructors

#### creates null

- creates null
- Verify: creates null
   - Expected: is_yaml_null(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates null")
step("Verify: creates null")
# @req: REQ-LIB-COMMON-001
val v = yaml_null()
expect(is_yaml_null(v)).to_equal(true)
```

</details>

#### creates boolean true

- creates boolean true
- Verify: creates boolean true
   - Expected: is_yaml_boolean(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates boolean true")
step("Verify: creates boolean true")
val v = yaml_boolean(true)
expect(is_yaml_boolean(v)).to_equal(true)
```

</details>

#### creates boolean false

- creates boolean false
- Verify: creates boolean false
   - Expected: is_yaml_boolean(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates boolean false")
step("Verify: creates boolean false")
val v = yaml_boolean(false)
expect(is_yaml_boolean(v)).to_equal(true)
```

</details>

#### creates number

- creates number
- Verify: creates number
   - Expected: is_yaml_number(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates number")
step("Verify: creates number")
val v = yaml_number("42")
expect(is_yaml_number(v)).to_equal(true)
```

</details>

#### creates string

- creates string
- Verify: creates string
   - Expected: is_yaml_string(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates string")
step("Verify: creates string")
val v = yaml_string("hello")
expect(is_yaml_string(v)).to_equal(true)
```

</details>

#### creates sequence

- creates sequence
- Verify: creates sequence
   - Expected: is_yaml_sequence(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates sequence")
step("Verify: creates sequence")
val v = yaml_sequence([yaml_number("1")])
expect(is_yaml_sequence(v)).to_equal(true)
```

</details>

#### creates empty sequence

- creates empty sequence
- Verify: creates empty sequence
   - Expected: is_yaml_sequence(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty sequence")
step("Verify: creates empty sequence")
val v = yaml_sequence([])
expect(is_yaml_sequence(v)).to_equal(true)
```

</details>

#### creates mapping

- creates mapping
- Verify: creates mapping
   - Expected: is_yaml_mapping(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates mapping")
step("Verify: creates mapping")
val v = yaml_mapping([("key", yaml_string("val"))])
expect(is_yaml_mapping(v)).to_equal(true)
```

</details>

#### creates empty mapping

- creates empty mapping
- Verify: creates empty mapping
   - Expected: is_yaml_mapping(v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty mapping")
step("Verify: creates empty mapping")
val v = yaml_mapping([])
expect(is_yaml_mapping(v)).to_equal(true)
```

</details>

#### type checks - negative

#### is_yaml_null false for non-null

- is_yaml_null false for non-null
- Verify: is_yaml_null false for non-null
   - Expected: is_yaml_null(yaml_string("x")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_yaml_null false for non-null")
step("Verify: is_yaml_null false for non-null")
expect(is_yaml_null(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_boolean false for non-boolean

- is_yaml_boolean false for non-boolean
- Verify: is_yaml_boolean false for non-boolean
   - Expected: is_yaml_boolean(yaml_string("x")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_yaml_boolean false for non-boolean")
step("Verify: is_yaml_boolean false for non-boolean")
expect(is_yaml_boolean(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_number false for non-number

- is_yaml_number false for non-number
- Verify: is_yaml_number false for non-number
   - Expected: is_yaml_number(yaml_string("x")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_yaml_number false for non-number")
step("Verify: is_yaml_number false for non-number")
expect(is_yaml_number(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_string false for non-string

- is_yaml_string false for non-string
- Verify: is_yaml_string false for non-string
   - Expected: is_yaml_string(yaml_number("1")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_yaml_string false for non-string")
step("Verify: is_yaml_string false for non-string")
expect(is_yaml_string(yaml_number("1"))).to_equal(false)
```

</details>

#### is_yaml_sequence false for non-sequence

- is_yaml_sequence false for non-sequence
- Verify: is_yaml_sequence false for non-sequence
   - Expected: is_yaml_sequence(yaml_string("x")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_yaml_sequence false for non-sequence")
step("Verify: is_yaml_sequence false for non-sequence")
expect(is_yaml_sequence(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_mapping false for non-mapping

- is_yaml_mapping false for non-mapping
- Verify: is_yaml_mapping false for non-mapping
   - Expected: is_yaml_mapping(yaml_string("x")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_yaml_mapping false for non-mapping")
step("Verify: is_yaml_mapping false for non-mapping")
expect(is_yaml_mapping(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_scalar true for scalar types

- is_yaml_scalar true for scalar types
- Verify: is_yaml_scalar true for scalar types
   - Expected: is_yaml_scalar(yaml_string("x")) is true
   - Expected: is_yaml_scalar(yaml_number("1")) is true
   - Expected: is_yaml_scalar(yaml_null()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_yaml_scalar true for scalar types")
step("Verify: is_yaml_scalar true for scalar types")
expect(is_yaml_scalar(yaml_string("x"))).to_equal(true)
expect(is_yaml_scalar(yaml_number("1"))).to_equal(true)
expect(is_yaml_scalar(yaml_null())).to_equal(true)
```

</details>

#### is_yaml_scalar false for compound types

- is_yaml_scalar false for compound types
- Verify: is_yaml_scalar false for compound types
   - Expected: is_yaml_scalar(yaml_sequence([])) is false
   - Expected: is_yaml_scalar(yaml_mapping([])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_yaml_scalar false for compound types")
step("Verify: is_yaml_scalar false for compound types")
expect(is_yaml_scalar(yaml_sequence([]))).to_equal(false)
expect(is_yaml_scalar(yaml_mapping([]))).to_equal(false)
```

</details>

#### value extraction

#### gets scalar type

- gets scalar type
- Verify: gets scalar type
   - Expected: t equals `string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets scalar type")
step("Verify: gets scalar type")
val t = yaml_get_scalar_type(yaml_string("x"))
expect(t).to_equal("string")
```

</details>

#### gets scalar content

- gets scalar content
- Verify: gets scalar content
   - Expected: c equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets scalar content")
step("Verify: gets scalar content")
val c = yaml_get_scalar_content(yaml_string("hello"))
expect(c).to_equal("hello")
```

</details>

#### gets sequence items

- gets sequence items
- Verify: gets sequence items
   - Expected: items.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets sequence items")
step("Verify: gets sequence items")
val items = yaml_get_sequence_items(yaml_sequence([yaml_number("1"), yaml_number("2")]))
expect(items.length()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### gets mapping pairs

- gets mapping pairs
- Verify: gets mapping pairs
   - Expected: pairs.length() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets mapping pairs")
step("Verify: gets mapping pairs")
val pairs = yaml_get_mapping_pairs(yaml_mapping([("a", yaml_number("1"))]))
expect(pairs.length()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### YAML Parse

#### yaml_parse_scalar

#### parses null values

- parses null values
- Verify: parses null values
   - Expected: is_yaml_null(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses null values")
step("Verify: parses null values")
val result = yaml_parse_scalar("null")
expect(is_yaml_null(result)).to_equal(true)
```

</details>

#### parses tilde as null

- parses tilde as null
- Verify: parses tilde as null
   - Expected: is_yaml_null(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses tilde as null")
step("Verify: parses tilde as null")
val result = yaml_parse_scalar("~")
expect(is_yaml_null(result)).to_equal(true)
```

</details>

#### parses true

- parses true
- Verify: parses true
   - Expected: is_yaml_boolean(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses true")
step("Verify: parses true")
val result = yaml_parse_scalar("true")
expect(is_yaml_boolean(result)).to_equal(true)
```

</details>

#### parses false

- parses false
- Verify: parses false
   - Expected: is_yaml_boolean(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses false")
step("Verify: parses false")
val result = yaml_parse_scalar("false")
expect(is_yaml_boolean(result)).to_equal(true)
```

</details>

#### parses integer

- parses integer
- Verify: parses integer
   - Expected: is_yaml_number(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses integer")
step("Verify: parses integer")
val result = yaml_parse_scalar("42")
expect(is_yaml_number(result)).to_equal(true)
```

</details>

#### parses negative number

- parses negative number
- Verify: parses negative number
   - Expected: is_yaml_number(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses negative number")
step("Verify: parses negative number")
val result = yaml_parse_scalar("-10")
expect(is_yaml_number(result)).to_equal(true)
```

</details>

#### parses decimal number

- parses decimal number
- Verify: parses decimal number
   - Expected: is_yaml_number(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses decimal number")
step("Verify: parses decimal number")
val result = yaml_parse_scalar("3.14")
expect(is_yaml_number(result)).to_equal(true)
```

</details>

#### parses plain string

- parses plain string
- Verify: parses plain string
   - Expected: is_yaml_string(result) is true
   - Expected: yaml_get_scalar_content(result) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses plain string")
step("Verify: parses plain string")
val result = yaml_parse_scalar("hello")
expect(is_yaml_string(result)).to_equal(true)
expect(yaml_get_scalar_content(result)).to_equal("hello")
```

</details>

#### parses quoted string

- parses quoted string
- Verify: parses quoted string
   - Expected: is_yaml_string(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses quoted string")
step("Verify: parses quoted string")
val result = yaml_parse_scalar("\"hello world\"")
expect(is_yaml_string(result)).to_equal(true)
```

</details>

#### parses empty string

- parses empty string
- Verify: parses empty string
   - Expected: is_yaml_null(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses empty string")
step("Verify: parses empty string")
val result = yaml_parse_scalar("")
expect(is_yaml_null(result)).to_equal(true)
```

</details>

#### yaml_parse flow sequences

#### parses flow sequence

- parses flow sequence
- Verify: parses flow sequence
   - Expected: is_yaml_sequence(result) is true
   - Expected: items.length() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses flow sequence")
step("Verify: parses flow sequence")
val result = yaml_parse_flow_sequence("[1, 2, 3]")
expect(is_yaml_sequence(result)).to_equal(true)
val items = yaml_get_sequence_items(result)
expect(items.length()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### parses empty flow sequence

- parses empty flow sequence
- Verify: parses empty flow sequence
   - Expected: is_yaml_sequence(result) is true
   - Expected: items.length() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses empty flow sequence")
step("Verify: parses empty flow sequence")
val result = yaml_parse_flow_sequence("[]")
expect(is_yaml_sequence(result)).to_equal(true)
val items = yaml_get_sequence_items(result)
expect(items.length()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### yaml_parse flow mappings

#### parses flow mapping

- parses flow mapping
- Verify: parses flow mapping
   - Expected: is_yaml_mapping(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses flow mapping")
step("Verify: parses flow mapping")
val result = yaml_parse_flow_mapping("{name: Alice, age: 30}")
expect(is_yaml_mapping(result)).to_equal(true)
```

</details>

#### parses empty flow mapping

- parses empty flow mapping
- Verify: parses empty flow mapping
   - Expected: is_yaml_mapping(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses empty flow mapping")
step("Verify: parses empty flow mapping")
val result = yaml_parse_flow_mapping("{}")
expect(is_yaml_mapping(result)).to_equal(true)
```

</details>

#### yaml_parse main

#### parses flow sequence via yaml_parse

- parses flow sequence via yaml_parse
- Verify: parses flow sequence via yaml_parse
   - Expected: is_yaml_sequence(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses flow sequence via yaml_parse")
step("Verify: parses flow sequence via yaml_parse")
val result = yaml_parse("[1, 2, 3]")
expect(is_yaml_sequence(result)).to_equal(true)
```

</details>

#### parses flow mapping via yaml_parse

- parses flow mapping via yaml_parse
- Verify: parses flow mapping via yaml_parse
   - Expected: is_yaml_mapping(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses flow mapping via yaml_parse")
step("Verify: parses flow mapping via yaml_parse")
val result = yaml_parse("{name: Alice}")
expect(is_yaml_mapping(result)).to_equal(true)
```

</details>

#### parses scalar via yaml_parse

- parses scalar via yaml_parse
- Verify: parses scalar via yaml_parse
   - Expected: is_yaml_number(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses scalar via yaml_parse")
step("Verify: parses scalar via yaml_parse")
val result = yaml_parse("42")
expect(is_yaml_number(result)).to_equal(true)
```

</details>

#### parses null via yaml_parse

- parses null via yaml_parse
- Verify: parses null via yaml_parse
   - Expected: is_yaml_null(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses null via yaml_parse")
step("Verify: parses null via yaml_parse")
val result = yaml_parse("null")
expect(is_yaml_null(result)).to_equal(true)
```

</details>

#### parses block mapping

- parses block mapping
- Verify: parses block mapping
   - Expected: is_yaml_mapping(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses block mapping")
step("Verify: parses block mapping")
val input = "name: Alice\nage: 30"
val result = yaml_parse(input)
expect(is_yaml_mapping(result)).to_equal(true)
```

</details>

#### parses block sequence

- parses block sequence
- Verify: parses block sequence
   - Expected: is_yaml_sequence(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses block sequence")
step("Verify: parses block sequence")
val input = "- 1\n- 2\n- 3"
val result = yaml_parse(input)
expect(is_yaml_sequence(result)).to_equal(true)
```

</details>

### YAML Serialize

#### flow style

#### serializes scalar in flow

- serializes scalar in flow
- Verify: serializes scalar in flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes scalar in flow")
step("Verify: serializes scalar in flow")
val v = yaml_string("hello")
val result = yaml_serialize_flow(v)
expect(result).to_contain("hello")
```

</details>

#### serializes null in flow

- serializes null in flow
- Verify: serializes null in flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes null in flow")
step("Verify: serializes null in flow")
val result = yaml_serialize_flow(yaml_null())
expect(result).to_contain("null")
```

</details>

#### serializes boolean in flow

- serializes boolean in flow
- Verify: serializes boolean in flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes boolean in flow")
step("Verify: serializes boolean in flow")
val result = yaml_serialize_flow(yaml_boolean(true))
expect(result).to_contain("true")
```

</details>

#### serializes sequence in flow

- serializes sequence in flow
- Verify: serializes sequence in flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes sequence in flow")
step("Verify: serializes sequence in flow")
val seq = yaml_sequence([yaml_number("1"), yaml_number("2")])
val result = yaml_serialize_flow(seq)
expect(result).to_contain("1")
expect(result).to_contain("2")
```

</details>

#### serializes mapping in flow

- serializes mapping in flow
- Verify: serializes mapping in flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes mapping in flow")
step("Verify: serializes mapping in flow")
val m = yaml_mapping([("key", yaml_string("val"))])
val result = yaml_serialize_flow(m)
expect(result).to_contain("key")
expect(result).to_contain("val")
```

</details>

#### block style

#### serializes scalar in block

- serializes scalar in block
- Verify: serializes scalar in block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes scalar in block")
step("Verify: serializes scalar in block")
val v = yaml_string("hello")
val result = yaml_serialize_block(v)
expect(result).to_contain("hello")
```

</details>

#### serializes sequence in block

- serializes sequence in block
- Verify: serializes sequence in block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes sequence in block")
step("Verify: serializes sequence in block")
val seq = yaml_sequence([yaml_number("1"), yaml_number("2")])
val result = yaml_serialize_block(seq)
expect(result).to_contain("1")
```

</details>

#### serializes mapping in block

- serializes mapping in block
- Verify: serializes mapping in block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes mapping in block")
step("Verify: serializes mapping in block")
val m = yaml_mapping([("key", yaml_string("val"))])
val result = yaml_serialize_block(m)
expect(result).to_contain("key")
expect(result).to_contain("val")
```

</details>

#### yaml_serialize with style parameter

#### uses block style

- uses block style
- Verify: uses block style


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses block style")
step("Verify: uses block style")
val v = yaml_string("hello")
val result = yaml_serialize(v, "block")
expect(result).to_contain("hello")
```

</details>

#### uses flow style

- uses flow style
- Verify: uses flow style


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses flow style")
step("Verify: uses flow style")
val v = yaml_string("hello")
val result = yaml_serialize(v, "flow")
expect(result).to_contain("hello")
```

</details>

### YAML Utilities - Strings

#### yaml_escape_string

#### escapes backslash

- escapes backslash
- Verify: escapes backslash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes backslash")
step("Verify: escapes backslash")
val result = yaml_escape_string("a\\b")
expect(result).to_contain("\\\\")
```

</details>

#### escapes double quote

- escapes double quote
- Verify: escapes double quote


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes double quote")
step("Verify: escapes double quote")
val result = yaml_escape_string("a\"b")
expect(result).to_contain("\\\"")
```

</details>

#### escapes newline

- escapes newline
- Verify: escapes newline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes newline")
step("Verify: escapes newline")
val result = yaml_escape_string("a\nb")
expect(result).to_contain("\\n")
```

</details>

#### escapes tab

- escapes tab
- Verify: escapes tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes tab")
step("Verify: escapes tab")
val result = yaml_escape_string("a\tb")
expect(result).to_contain("\\t")
```

</details>

#### escapes carriage return

- escapes carriage return
- Verify: escapes carriage return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes carriage return")
step("Verify: escapes carriage return")
val result = yaml_escape_string("a\rb")
expect(result).to_contain("\\r")
```

</details>

#### passes plain text through

- passes plain text through
- Verify: passes plain text through
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes plain text through")
step("Verify: passes plain text through")
val result = yaml_escape_string("hello")
expect(result).to_equal("hello")
```

</details>

#### yaml_unescape_string

#### unescapes backslash

- unescapes backslash
- Verify: unescapes backslash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes backslash")
step("Verify: unescapes backslash")
val result = yaml_unescape_string("a\\\\b")
expect(result).to_contain("\\")
```

</details>

#### unescapes newline

- unescapes newline
- Verify: unescapes newline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes newline")
step("Verify: unescapes newline")
val result = yaml_unescape_string("a\\nb")
expect(result).to_contain("\n")
```

</details>

#### unescapes tab

- unescapes tab
- Verify: unescapes tab


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes tab")
step("Verify: unescapes tab")
val result = yaml_unescape_string("a\\tb")
expect(result).to_contain("\t")
```

</details>

#### passes plain text through

- passes plain text through
- Verify: passes plain text through
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes plain text through")
step("Verify: passes plain text through")
val result = yaml_unescape_string("hello")
expect(result).to_equal("hello")
```

</details>

#### yaml_needs_quotes

#### needs quotes for empty string

- needs quotes for empty string
- Verify: needs quotes for empty string
   - Expected: yaml_needs_quotes("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("needs quotes for empty string")
step("Verify: needs quotes for empty string")
expect(yaml_needs_quotes("")).to_equal(true)
```

</details>

#### plain alphanumeric does not need quotes

- plain alphanumeric does not need quotes
- Verify: plain alphanumeric does not need quotes
   - Expected: yaml_needs_quotes("hello") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("plain alphanumeric does not need quotes")
step("Verify: plain alphanumeric does not need quotes")
expect(yaml_needs_quotes("hello")).to_equal(false)
```

</details>

#### string with colon needs quotes

- string with colon needs quotes
- Verify: string with colon needs quotes
   - Expected: yaml_needs_quotes("key: value") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("string with colon needs quotes")
step("Verify: string with colon needs quotes")
expect(yaml_needs_quotes("key: value")).to_equal(true)
```

</details>

#### yaml_quote_string

#### quotes a string

- quotes a string
- Verify: quotes a string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("quotes a string")
step("Verify: quotes a string")
val result = yaml_quote_string("hello world")
expect(result).to_start_with("\"")
expect(result).to_end_with("\"")
```

</details>

### YAML Mapping Operations

#### get and has

#### gets value by key

- gets value by key
- Verify: gets value by key
   - Expected: result equals `yaml_string("Alice")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets value by key")
step("Verify: gets value by key")
val m = yaml_mapping([("name", yaml_string("Alice"))])
val result = yaml_mapping_get(m, "name")
expect(result).to_equal(yaml_string("Alice"))
```

</details>

#### returns nil for missing key

- returns nil for missing key
- Verify: returns nil for missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for missing key")
step("Verify: returns nil for missing key")
val m = yaml_mapping([("name", yaml_string("Alice"))])
val result = yaml_mapping_get(m, "age")
expect(result).to_be_nil()
```

</details>

#### has returns true for existing key

- has returns true for existing key
- Verify: has returns true for existing key
   - Expected: yaml_mapping_has(m, "name") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has returns true for existing key")
step("Verify: has returns true for existing key")
val m = yaml_mapping([("name", yaml_string("Alice"))])
expect(yaml_mapping_has(m, "name")).to_equal(true)
```

</details>

#### has returns false for missing key

- has returns false for missing key
- Verify: has returns false for missing key
   - Expected: yaml_mapping_has(m, "age") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has returns false for missing key")
step("Verify: has returns false for missing key")
val m = yaml_mapping([("name", yaml_string("Alice"))])
expect(yaml_mapping_has(m, "age")).to_equal(false)
```

</details>

#### set and remove

#### sets new key

- sets new key
- Verify: sets new key
   - Expected: yaml_mapping_has(updated, "name") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets new key")
step("Verify: sets new key")
val m = yaml_mapping([])
val updated = yaml_mapping_set(m, "name", yaml_string("Alice"))
expect(yaml_mapping_has(updated, "name")).to_equal(true)
```

</details>

#### updates existing key

- updates existing key
- Verify: updates existing key
   - Expected: result equals `yaml_string("Bob")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("updates existing key")
step("Verify: updates existing key")
val m = yaml_mapping([("name", yaml_string("Alice"))])
val updated = yaml_mapping_set(m, "name", yaml_string("Bob"))
val result = yaml_mapping_get(updated, "name")
expect(result).to_equal(yaml_string("Bob"))
```

</details>

#### removes existing key

- removes existing key
- Verify: removes existing key
   - Expected: yaml_mapping_has(updated, "a") is false
   - Expected: yaml_mapping_has(updated, "b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes existing key")
step("Verify: removes existing key")
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2"))])
val updated = yaml_mapping_remove(m, "a")
expect(yaml_mapping_has(updated, "a")).to_equal(false)
expect(yaml_mapping_has(updated, "b")).to_equal(true)
```

</details>

#### keys, values, size

#### gets keys

- gets keys
- Verify: gets keys
   - Expected: keys.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets keys")
step("Verify: gets keys")
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2"))])
val keys = yaml_mapping_keys(m)
expect(keys.length()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### gets values

- gets values
- Verify: gets values
   - Expected: vals.length() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets values")
step("Verify: gets values")
val m = yaml_mapping([("a", yaml_number("1"))])
val vals = yaml_mapping_values(m)
expect(vals.length()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### gets size

- gets size
- Verify: gets size
   - Expected: yaml_mapping_size(m) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets size")
step("Verify: gets size")
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2"))])
expect(yaml_mapping_size(m)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### empty mapping size is 0

- empty mapping size is 0
- Verify: empty mapping size is 0
   - Expected: yaml_mapping_size(yaml_mapping([])) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty mapping size is 0")
step("Verify: empty mapping size is 0")
expect(yaml_mapping_size(yaml_mapping([]))).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### contains and filter

#### contains_value finds existing value

- contains_value finds existing value
- Verify: contains_value finds existing value
   - Expected: yaml_mapping_contains_value(m, yaml_string("Alice")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains_value finds existing value")
step("Verify: contains_value finds existing value")
val m = yaml_mapping([("name", yaml_string("Alice"))])
expect(yaml_mapping_contains_value(m, yaml_string("Alice"))).to_equal(true)
```

</details>

#### contains_value returns false for missing value

- contains_value returns false for missing value
- Verify: contains_value returns false for missing value
   - Expected: yaml_mapping_contains_value(m, yaml_string("Bob")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains_value returns false for missing value")
step("Verify: contains_value returns false for missing value")
val m = yaml_mapping([("name", yaml_string("Alice"))])
expect(yaml_mapping_contains_value(m, yaml_string("Bob"))).to_equal(false)
```

</details>

#### filters keys

- filters keys
- Verify: filters keys
   - Expected: yaml_mapping_size(filtered) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("filters keys")
step("Verify: filters keys")
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2")), ("c", yaml_number("3"))])
val filtered = yaml_mapping_filter_keys(m, ["a", "c"])
expect(yaml_mapping_size(filtered)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### excludes keys

- excludes keys
- Verify: excludes keys
   - Expected: yaml_mapping_has(excluded, "b") is false
   - Expected: yaml_mapping_size(excluded) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("excludes keys")
step("Verify: excludes keys")
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2")), ("c", yaml_number("3"))])
val excluded = yaml_mapping_exclude_keys(m, ["b"])
expect(yaml_mapping_has(excluded, "b")).to_equal(false)
expect(yaml_mapping_size(excluded)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### YAML Sequence Operations

#### basic operations

#### gets element by index

- gets element by index
- Verify: gets element by index
   - Expected: result equals `yaml_number("10")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets element by index")
step("Verify: gets element by index")
val seq = yaml_sequence([yaml_number("10"), yaml_number("20")])
val result = yaml_sequence_get(seq, 0)
expect(result).to_equal(yaml_number("10"))
```

</details>

#### sets element at index

- sets element at index
- Verify: sets element at index
   - Expected: result equals `yaml_number("99")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets element at index")
step("Verify: sets element at index")
val seq = yaml_sequence([yaml_number("10"), yaml_number("20")])
val updated = yaml_sequence_set(seq, 0, yaml_number("99"))
val result = yaml_sequence_get(updated, 0)
expect(result).to_equal(yaml_number("99"))
```

</details>

#### appends element

- appends element
- Verify: appends element
   - Expected: yaml_sequence_length(updated) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("appends element")
step("Verify: appends element")
val seq = yaml_sequence([yaml_number("1")])
val updated = yaml_sequence_append(seq, yaml_number("2"))
expect(yaml_sequence_length(updated)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### gets length

- gets length
- Verify: gets length
   - Expected: yaml_sequence_length(seq) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets length")
step("Verify: gets length")
val seq = yaml_sequence([yaml_number("1"), yaml_number("2"), yaml_number("3")])
expect(yaml_sequence_length(seq)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### inserts at index

- inserts at index
- Verify: inserts at index
   - Expected: yaml_sequence_length(updated) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("inserts at index")
step("Verify: inserts at index")
val seq = yaml_sequence([yaml_number("1"), yaml_number("3")])
val updated = yaml_sequence_insert(seq, 1, yaml_number("2"))
expect(yaml_sequence_length(updated)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### removes at index

- removes at index
- Verify: removes at index
   - Expected: yaml_sequence_length(updated) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes at index")
step("Verify: removes at index")
val seq = yaml_sequence([yaml_number("1"), yaml_number("2"), yaml_number("3")])
val updated = yaml_sequence_remove(seq, 1)
expect(yaml_sequence_length(updated)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### search and transform

#### contains finds element

- contains finds element
- Verify: contains finds element
   - Expected: yaml_sequence_contains(seq, yaml_number("2")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains finds element")
step("Verify: contains finds element")
val seq = yaml_sequence([yaml_number("1"), yaml_number("2")])
expect(yaml_sequence_contains(seq, yaml_number("2"))).to_equal(true)
```

</details>

#### contains returns false for missing

- contains returns false for missing
- Verify: contains returns false for missing
   - Expected: yaml_sequence_contains(seq, yaml_number("99")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains returns false for missing")
step("Verify: contains returns false for missing")
val seq = yaml_sequence([yaml_number("1")])
expect(yaml_sequence_contains(seq, yaml_number("99"))).to_equal(false)
```

</details>

#### index_of finds element

- index_of finds element
- Verify: index_of finds element
   - Expected: yaml_sequence_index_of(seq, yaml_number("20")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("index_of finds element")
step("Verify: index_of finds element")
val seq = yaml_sequence([yaml_number("10"), yaml_number("20"), yaml_number("30")])
expect(yaml_sequence_index_of(seq, yaml_number("20"))).to_equal(1)
```

</details>

#### index_of returns -1 for missing

- index_of returns -1 for missing
- Verify: index_of returns -1 for missing
   - Expected: yaml_sequence_index_of(seq, yaml_number("99")) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("index_of returns -1 for missing")
step("Verify: index_of returns -1 for missing")
val seq = yaml_sequence([yaml_number("1")])
expect(yaml_sequence_index_of(seq, yaml_number("99"))).to_equal(-1)
```

</details>

#### reverses sequence

- reverses sequence
- Verify: reverses sequence
   - Expected: first equals `yaml_number("3")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reverses sequence")
step("Verify: reverses sequence")
val seq = yaml_sequence([yaml_number("1"), yaml_number("2"), yaml_number("3")])
val reversed = yaml_sequence_reverse(seq)
val first = yaml_sequence_get(reversed, 0)
expect(first).to_equal(yaml_number("3"))
```

</details>

#### slices sequence

- slices sequence
- Verify: slices sequence
   - Expected: yaml_sequence_length(sliced) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("slices sequence")
step("Verify: slices sequence")
val seq = yaml_sequence([yaml_number("1"), yaml_number("2"), yaml_number("3"), yaml_number("4")])
val sliced = yaml_sequence_slice(seq, 1, 3)
expect(yaml_sequence_length(sliced)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### YAML Advanced Utilities

#### equality and copy

#### equal values are equal

- equal values are equal
- Verify: equal values are equal
   - Expected: yaml_equals(a, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("equal values are equal")
step("Verify: equal values are equal")
val a = yaml_string("hello")
val b = yaml_string("hello")
expect(yaml_equals(a, b)).to_equal(true)
```

</details>

#### different values are not equal

- different values are not equal
- Verify: different values are not equal
   - Expected: yaml_equals(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("different values are not equal")
step("Verify: different values are not equal")
val a = yaml_string("hello")
val b = yaml_string("world")
expect(yaml_equals(a, b)).to_equal(false)
```

</details>

#### deep copy produces equal value

- deep copy produces equal value
- Verify: deep copy produces equal value
   - Expected: yaml_equals(orig, copy) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("deep copy produces equal value")
step("Verify: deep copy produces equal value")
val orig = yaml_mapping([("key", yaml_string("val"))])
val copy = yaml_deep_copy(orig)
expect(yaml_equals(orig, copy)).to_equal(true)
```

</details>

#### merge

#### merges two mappings

- merges two mappings
- Verify: merges two mappings
   - Expected: yaml_mapping_has(merged, "a") is true
   - Expected: yaml_mapping_has(merged, "b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges two mappings")
step("Verify: merges two mappings")
val m1 = yaml_mapping([("a", yaml_number("1"))])
val m2 = yaml_mapping([("b", yaml_number("2"))])
val merged = yaml_merge_mappings(m1, m2)
expect(yaml_mapping_has(merged, "a")).to_equal(true)
expect(yaml_mapping_has(merged, "b")).to_equal(true)
```

</details>

#### second mapping overrides first

- second mapping overrides first
- Verify: second mapping overrides first
   - Expected: result equals `yaml_number("2")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("second mapping overrides first")
step("Verify: second mapping overrides first")
val m1 = yaml_mapping([("a", yaml_number("1"))])
val m2 = yaml_mapping([("a", yaml_number("2"))])
val merged = yaml_merge_mappings(m1, m2)
val result = yaml_mapping_get(merged, "a")
expect(result).to_equal(yaml_number("2"))
```

</details>

#### emptiness check

#### empty mapping is empty

- empty mapping is empty
- Verify: empty mapping is empty
   - Expected: yaml_is_empty(yaml_mapping([])) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty mapping is empty")
step("Verify: empty mapping is empty")
expect(yaml_is_empty(yaml_mapping([]))).to_equal(true)
```

</details>

#### empty sequence is empty

- empty sequence is empty
- Verify: empty sequence is empty
   - Expected: yaml_is_empty(yaml_sequence([])) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty sequence is empty")
step("Verify: empty sequence is empty")
expect(yaml_is_empty(yaml_sequence([]))).to_equal(true)
```

</details>

#### non-empty mapping is not empty

- non-empty mapping is not empty
- Verify: non-empty mapping is not empty
   - Expected: yaml_is_empty(yaml_mapping([("a", yaml_number("1"))])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("non-empty mapping is not empty")
step("Verify: non-empty mapping is not empty")
expect(yaml_is_empty(yaml_mapping([("a", yaml_number("1"))]))).to_equal(false)
```

</details>

#### non-empty sequence is not empty

- non-empty sequence is not empty
- Verify: non-empty sequence is not empty
   - Expected: yaml_is_empty(yaml_sequence([yaml_number("1")])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("non-empty sequence is not empty")
step("Verify: non-empty sequence is not empty")
expect(yaml_is_empty(yaml_sequence([yaml_number("1")]))).to_equal(false)
```

</details>

#### node counting and depth

#### counts nodes in scalar

- counts nodes in scalar
- Verify: counts nodes in scalar
   - Expected: yaml_count_nodes(yaml_string("x")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts nodes in scalar")
step("Verify: counts nodes in scalar")
expect(yaml_count_nodes(yaml_string("x"))).to_equal(1)
```

</details>

#### counts nodes in sequence

- counts nodes in sequence
- Verify: counts nodes in sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts nodes in sequence")
step("Verify: counts nodes in sequence")
val seq = yaml_sequence([yaml_number("1"), yaml_number("2")])
expect(yaml_count_nodes(seq)).to_be_greater_than(1)
```

</details>

#### depth of scalar is 1

- depth of scalar is 1
- Verify: depth of scalar is 1
   - Expected: yaml_depth(yaml_string("x")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("depth of scalar is 1")
step("Verify: depth of scalar is 1")
expect(yaml_depth(yaml_string("x"))).to_equal(1)
```

</details>

#### depth of nested structure

- depth of nested structure
- Verify: depth of nested structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("depth of nested structure")
step("Verify: depth of nested structure")
val inner = yaml_mapping([("a", yaml_string("b"))])
val outer = yaml_mapping([("nested", inner)])
expect(yaml_depth(outer)).to_be_greater_than(1)
```

</details>

#### nested access

#### gets nested value

- gets nested value
- Verify: gets nested value
   - Expected: result equals `yaml_string("value")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets nested value")
step("Verify: gets nested value")
val inner = yaml_mapping([("b", yaml_string("value"))])
val outer = yaml_mapping([("a", inner)])
val result = yaml_get_nested(outer, ["a", "b"])
expect(result).to_equal(yaml_string("value"))
```

</details>

#### sets nested value

- sets nested value
- Verify: sets nested value
   - Expected: result equals `yaml_string("new")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets nested value")
step("Verify: sets nested value")
val inner = yaml_mapping([("b", yaml_string("old"))])
val outer = yaml_mapping([("a", inner)])
val updated = yaml_set_nested(outer, ["a", "b"], yaml_string("new"))
val result = yaml_get_nested(updated, ["a", "b"])
expect(result).to_equal(yaml_string("new"))
```

</details>

#### to_string and from_string

#### round-trips through string

- round-trips through string
- Verify: round-trips through string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips through string")
step("Verify: round-trips through string")
val v = yaml_mapping([("key", yaml_string("val"))])
val s = yaml_to_string(v)
expect(s).to_contain("key")
```

</details>

#### pretty and compact print

#### pretty prints value

- pretty prints value
- Verify: pretty prints value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pretty prints value")
step("Verify: pretty prints value")
val v = yaml_mapping([("key", yaml_string("val"))])
val result = yaml_pretty_print(v)
expect(result).to_contain("key")
```

</details>

#### compact prints value

- compact prints value
- Verify: compact prints value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compact prints value")
step("Verify: compact prints value")
val v = yaml_mapping([("key", yaml_string("val"))])
val result = yaml_compact_print(v)
expect(result).to_contain("key")
```

</details>

### YAML Validate

#### multi-document

#### parses multiple documents

- parses multiple documents
- Verify: parses multiple documents


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses multiple documents")
step("Verify: parses multiple documents")
val input = "name: Alice\n---\nname: Bob"
val docs = yaml_parse_documents(input)
expect(docs.length()).to_be_greater_than(0)
```

</details>

#### serializes multiple documents

- serializes multiple documents
- Verify: serializes multiple documents


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes multiple documents")
step("Verify: serializes multiple documents")
val docs = [yaml_string("doc1"), yaml_string("doc2")]
val result = yaml_serialize_documents(docs, "flow")
expect(result).to_contain("doc1")
expect(result).to_contain("doc2")
```

</details>

#### anchors and aliases

#### creates anchor

- creates anchor
- Verify: creates anchor
   - Expected: yaml_is_anchor(anchor) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates anchor")
step("Verify: creates anchor")
val anchor = yaml_create_anchor("myanchor", yaml_string("value"))
expect(yaml_is_anchor(anchor)).to_equal(true)
```

</details>

#### creates alias

- creates alias
- Verify: creates alias
   - Expected: yaml_is_alias(alias) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates alias")
step("Verify: creates alias")
val alias = yaml_create_alias("myanchor")
expect(yaml_is_alias(alias)).to_equal(true)
```

</details>

#### is_anchor false for non-anchor

- is_anchor false for non-anchor
- Verify: is_anchor false for non-anchor
   - Expected: yaml_is_anchor(yaml_string("x")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_anchor false for non-anchor")
step("Verify: is_anchor false for non-anchor")
expect(yaml_is_anchor(yaml_string("x"))).to_equal(false)
```

</details>

#### is_alias false for non-alias

- is_alias false for non-alias
- Verify: is_alias false for non-alias
   - Expected: yaml_is_alias(yaml_string("x")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_alias false for non-alias")
step("Verify: is_alias false for non-alias")
expect(yaml_is_alias(yaml_string("x"))).to_equal(false)
```

</details>

#### gets anchor name

- gets anchor name
- Verify: gets anchor name
   - Expected: yaml_get_anchor_name(anchor) equals `myanchor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets anchor name")
step("Verify: gets anchor name")
val anchor = yaml_create_anchor("myanchor", yaml_string("value"))
expect(yaml_get_anchor_name(anchor)).to_equal("myanchor")
```

</details>

#### gets anchor value

- gets anchor value
- Verify: gets anchor value
   - Expected: yaml_equals(v, yaml_string("value")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets anchor value")
step("Verify: gets anchor value")
val anchor = yaml_create_anchor("myanchor", yaml_string("value"))
val v = yaml_get_anchor_value(anchor)
expect(yaml_equals(v, yaml_string("value"))).to_equal(true)
```

</details>

#### gets alias name

- gets alias name
- Verify: gets alias name
   - Expected: yaml_get_alias_name(alias) equals `myanchor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets alias name")
step("Verify: gets alias name")
val alias = yaml_create_alias("myanchor")
expect(yaml_get_alias_name(alias)).to_equal("myanchor")
```

</details>

#### resolves aliases

- resolves aliases
- Verify: resolves aliases
   - Expected: yaml_equals(resolved, yaml_string("resolved")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves aliases")
step("Verify: resolves aliases")
val anchor = yaml_create_anchor("data", yaml_string("resolved"))
val alias = yaml_create_alias("data")
val resolved = yaml_resolve_aliases(alias, [anchor])
expect(yaml_equals(resolved, yaml_string("resolved"))).to_equal(true)
```

</details>

#### indentation utilities

#### creates indent string

- creates indent string
- Verify: creates indent string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates indent string")
step("Verify: creates indent string")
val result = yaml_indent(2, 2)
expect(result.length()).to_be_greater_than(0)
```

</details>

### YAML Schema Validation

#### validation

#### validates matching type

- validates matching type
- Verify: validates matching type
   - Expected: result.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates matching type")
step("Verify: validates matching type")
val schema = yaml_mapping([("type", yaml_string("scalar"))])
val result = yaml_validate_schema(yaml_string("hello"), schema)
expect(result.0).to_equal(true)
```

</details>

#### flatten mapping

#### flattens nested mapping

- flattens nested mapping
- Verify: flattens nested mapping
   - Expected: yaml_mapping_has(flat, "a.b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flattens nested mapping")
step("Verify: flattens nested mapping")
val inner = yaml_mapping([("b", yaml_string("val"))])
val outer = yaml_mapping([("a", inner)])
val flat = yaml_flatten_mapping(outer)
expect(yaml_mapping_has(flat, "a.b")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 123 |
| Active scenarios | 123 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d55f347eb4a5c4ffd5183ebdd1f267be0077da848efa730f8224008260d085a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d55f347eb4a5c4ffd5183ebdd1f267be0077da848efa730f8224008260d085a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d55f347eb4a5c4ffd5183ebdd1f267be0077da848efa730f8224008260d085a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/parsers_misc_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/parsers_misc_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/parsers_misc_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/parsers_misc_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/parsers_misc_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/parsers_misc_coverage_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates null' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/parsers_misc_coverage_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates boolean true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/parsers_misc_coverage_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates boolean false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
