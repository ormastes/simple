# Parsers Coverage Specification

> Comprehensive branch-coverage tests for the three parser libraries:

<!-- sdn-diagram:id=parsers_misc_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parsers_misc_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parsers_misc_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parsers_misc_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 123 | 123 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parsers Coverage Specification

Comprehensive branch-coverage tests for the three parser libraries:

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive branch-coverage tests for the three parser libraries:
- `src/lib/common/json/` -- JSON types, parser, serializer, builder, object/array ops, path ops, validation, utilities
- `src/lib/common/sdn/` -- SDN value, lexer, parser, document, handler, error
- `src/lib/common/yaml/` -- YAML types, parse, serialize, utilities, validate

Targets 90%+ branch coverage by exercising both true and false branches of every
conditional in each module.

## Scenarios

### YAML Types

#### constructors

#### creates null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_null()
expect(is_yaml_null(v)).to_equal(true)
```

</details>

#### creates boolean true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_boolean(true)
expect(is_yaml_boolean(v)).to_equal(true)
```

</details>

#### creates boolean false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_boolean(false)
expect(is_yaml_boolean(v)).to_equal(true)
```

</details>

#### creates number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_number("42")
expect(is_yaml_number(v)).to_equal(true)
```

</details>

#### creates string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_string("hello")
expect(is_yaml_string(v)).to_equal(true)
```

</details>

#### creates sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_sequence([yaml_number("1")])
expect(is_yaml_sequence(v)).to_equal(true)
```

</details>

#### creates empty sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_sequence([])
expect(is_yaml_sequence(v)).to_equal(true)
```

</details>

#### creates mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_mapping([("key", yaml_string("val"))])
expect(is_yaml_mapping(v)).to_equal(true)
```

</details>

#### creates empty mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_mapping([])
expect(is_yaml_mapping(v)).to_equal(true)
```

</details>

#### type checks - negative

#### is_yaml_null false for non-null

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_yaml_null(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_boolean false for non-boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_yaml_boolean(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_number false for non-number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_yaml_number(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_string false for non-string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_yaml_string(yaml_number("1"))).to_equal(false)
```

</details>

#### is_yaml_sequence false for non-sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_yaml_sequence(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_mapping false for non-mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_yaml_mapping(yaml_string("x"))).to_equal(false)
```

</details>

#### is_yaml_scalar true for scalar types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_yaml_scalar(yaml_string("x"))).to_equal(true)
expect(is_yaml_scalar(yaml_number("1"))).to_equal(true)
expect(is_yaml_scalar(yaml_null())).to_equal(true)
```

</details>

#### is_yaml_scalar false for compound types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_yaml_scalar(yaml_sequence([]))).to_equal(false)
expect(is_yaml_scalar(yaml_mapping([]))).to_equal(false)
```

</details>

#### value extraction

#### gets scalar type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = yaml_get_scalar_type(yaml_string("x"))
expect(t).to_equal("string")
```

</details>

#### gets scalar content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = yaml_get_scalar_content(yaml_string("hello"))
expect(c).to_equal("hello")
```

</details>

#### gets sequence items

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = yaml_get_sequence_items(yaml_sequence([yaml_number("1"), yaml_number("2")]))
expect(items.length()).to_equal(2)
```

</details>

#### gets mapping pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = yaml_get_mapping_pairs(yaml_mapping([("a", yaml_number("1"))]))
expect(pairs.length()).to_equal(1)
```

</details>

### YAML Parse

#### yaml_parse_scalar

#### parses null values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("null")
expect(is_yaml_null(result)).to_equal(true)
```

</details>

#### parses tilde as null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("~")
expect(is_yaml_null(result)).to_equal(true)
```

</details>

#### parses true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("true")
expect(is_yaml_boolean(result)).to_equal(true)
```

</details>

#### parses false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("false")
expect(is_yaml_boolean(result)).to_equal(true)
```

</details>

#### parses integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("42")
expect(is_yaml_number(result)).to_equal(true)
```

</details>

#### parses negative number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("-10")
expect(is_yaml_number(result)).to_equal(true)
```

</details>

#### parses decimal number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("3.14")
expect(is_yaml_number(result)).to_equal(true)
```

</details>

#### parses plain string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("hello")
expect(is_yaml_string(result)).to_equal(true)
expect(yaml_get_scalar_content(result)).to_equal("hello")
```

</details>

#### parses quoted string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("\"hello world\"")
expect(is_yaml_string(result)).to_equal(true)
```

</details>

#### parses empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_scalar("")
expect(is_yaml_null(result)).to_equal(true)
```

</details>

#### yaml_parse flow sequences

#### parses flow sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_flow_sequence("[1, 2, 3]")
expect(is_yaml_sequence(result)).to_equal(true)
val items = yaml_get_sequence_items(result)
expect(items.length()).to_equal(3)
```

</details>

#### parses empty flow sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_flow_sequence("[]")
expect(is_yaml_sequence(result)).to_equal(true)
val items = yaml_get_sequence_items(result)
expect(items.length()).to_equal(0)
```

</details>

#### yaml_parse flow mappings

#### parses flow mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_flow_mapping("{name: Alice, age: 30}")
expect(is_yaml_mapping(result)).to_equal(true)
```

</details>

#### parses empty flow mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse_flow_mapping("{}")
expect(is_yaml_mapping(result)).to_equal(true)
```

</details>

#### yaml_parse main

#### parses flow sequence via yaml_parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse("[1, 2, 3]")
expect(is_yaml_sequence(result)).to_equal(true)
```

</details>

#### parses flow mapping via yaml_parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse("{name: Alice}")
expect(is_yaml_mapping(result)).to_equal(true)
```

</details>

#### parses scalar via yaml_parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse("42")
expect(is_yaml_number(result)).to_equal(true)
```

</details>

#### parses null via yaml_parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_parse("null")
expect(is_yaml_null(result)).to_equal(true)
```

</details>

#### parses block mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "name: Alice\nage: 30"
val result = yaml_parse(input)
expect(is_yaml_mapping(result)).to_equal(true)
```

</details>

#### parses block sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "- 1\n- 2\n- 3"
val result = yaml_parse(input)
expect(is_yaml_sequence(result)).to_equal(true)
```

</details>

### YAML Serialize

#### flow style

#### serializes scalar in flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_string("hello")
val result = yaml_serialize_flow(v)
expect(result).to_contain("hello")
```

</details>

#### serializes null in flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_serialize_flow(yaml_null())
expect(result).to_contain("null")
```

</details>

#### serializes boolean in flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_serialize_flow(yaml_boolean(true))
expect(result).to_contain("true")
```

</details>

#### serializes sequence in flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("2")])
val result = yaml_serialize_flow(seq)
expect(result).to_contain("1")
expect(result).to_contain("2")
```

</details>

#### serializes mapping in flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("key", yaml_string("val"))])
val result = yaml_serialize_flow(m)
expect(result).to_contain("key")
expect(result).to_contain("val")
```

</details>

#### block style

#### serializes scalar in block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_string("hello")
val result = yaml_serialize_block(v)
expect(result).to_contain("hello")
```

</details>

#### serializes sequence in block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("2")])
val result = yaml_serialize_block(seq)
expect(result).to_contain("1")
```

</details>

#### serializes mapping in block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("key", yaml_string("val"))])
val result = yaml_serialize_block(m)
expect(result).to_contain("key")
expect(result).to_contain("val")
```

</details>

#### yaml_serialize with style parameter

#### uses block style

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_string("hello")
val result = yaml_serialize(v, "block")
expect(result).to_contain("hello")
```

</details>

#### uses flow style

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_string("hello")
val result = yaml_serialize(v, "flow")
expect(result).to_contain("hello")
```

</details>

### YAML Utilities - Strings

#### yaml_escape_string

#### escapes backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_escape_string("a\\b")
expect(result).to_contain("\\\\")
```

</details>

#### escapes double quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_escape_string("a\"b")
expect(result).to_contain("\\\"")
```

</details>

#### escapes newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_escape_string("a\nb")
expect(result).to_contain("\\n")
```

</details>

#### escapes tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_escape_string("a\tb")
expect(result).to_contain("\\t")
```

</details>

#### escapes carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_escape_string("a\rb")
expect(result).to_contain("\\r")
```

</details>

#### passes plain text through

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_escape_string("hello")
expect(result).to_equal("hello")
```

</details>

#### yaml_unescape_string

#### unescapes backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_unescape_string("a\\\\b")
expect(result).to_contain("\\")
```

</details>

#### unescapes newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_unescape_string("a\\nb")
expect(result).to_contain("\n")
```

</details>

#### unescapes tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_unescape_string("a\\tb")
expect(result).to_contain("\t")
```

</details>

#### passes plain text through

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_unescape_string("hello")
expect(result).to_equal("hello")
```

</details>

#### yaml_needs_quotes

#### needs quotes for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_needs_quotes("")).to_equal(true)
```

</details>

#### plain alphanumeric does not need quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_needs_quotes("hello")).to_equal(false)
```

</details>

#### string with colon needs quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_needs_quotes("key: value")).to_equal(true)
```

</details>

#### yaml_quote_string

#### quotes a string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_quote_string("hello world")
expect(result).to_start_with("\"")
expect(result).to_end_with("\"")
```

</details>

### YAML Mapping Operations

#### get and has

#### gets value by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("name", yaml_string("Alice"))])
val result = yaml_mapping_get(m, "name")
expect(result).to_equal(yaml_string("Alice"))
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("name", yaml_string("Alice"))])
val result = yaml_mapping_get(m, "age")
expect(result).to_be_nil()
```

</details>

#### has returns true for existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("name", yaml_string("Alice"))])
expect(yaml_mapping_has(m, "name")).to_equal(true)
```

</details>

#### has returns false for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("name", yaml_string("Alice"))])
expect(yaml_mapping_has(m, "age")).to_equal(false)
```

</details>

#### set and remove

#### sets new key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([])
val updated = yaml_mapping_set(m, "name", yaml_string("Alice"))
expect(yaml_mapping_has(updated, "name")).to_equal(true)
```

</details>

#### updates existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("name", yaml_string("Alice"))])
val updated = yaml_mapping_set(m, "name", yaml_string("Bob"))
val result = yaml_mapping_get(updated, "name")
expect(result).to_equal(yaml_string("Bob"))
```

</details>

#### removes existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2"))])
val updated = yaml_mapping_remove(m, "a")
expect(yaml_mapping_has(updated, "a")).to_equal(false)
expect(yaml_mapping_has(updated, "b")).to_equal(true)
```

</details>

#### keys, values, size

#### gets keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2"))])
val keys = yaml_mapping_keys(m)
expect(keys.length()).to_equal(2)
```

</details>

#### gets values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("a", yaml_number("1"))])
val vals = yaml_mapping_values(m)
expect(vals.length()).to_equal(1)
```

</details>

#### gets size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2"))])
expect(yaml_mapping_size(m)).to_equal(2)
```

</details>

#### empty mapping size is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_mapping_size(yaml_mapping([]))).to_equal(0)
```

</details>

#### contains and filter

#### contains_value finds existing value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("name", yaml_string("Alice"))])
expect(yaml_mapping_contains_value(m, yaml_string("Alice"))).to_equal(true)
```

</details>

#### contains_value returns false for missing value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("name", yaml_string("Alice"))])
expect(yaml_mapping_contains_value(m, yaml_string("Bob"))).to_equal(false)
```

</details>

#### filters keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2")), ("c", yaml_number("3"))])
val filtered = yaml_mapping_filter_keys(m, ["a", "c"])
expect(yaml_mapping_size(filtered)).to_equal(2)
```

</details>

#### excludes keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = yaml_mapping([("a", yaml_number("1")), ("b", yaml_number("2")), ("c", yaml_number("3"))])
val excluded = yaml_mapping_exclude_keys(m, ["b"])
expect(yaml_mapping_has(excluded, "b")).to_equal(false)
expect(yaml_mapping_size(excluded)).to_equal(2)
```

</details>

### YAML Sequence Operations

#### basic operations

#### gets element by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("10"), yaml_number("20")])
val result = yaml_sequence_get(seq, 0)
expect(result).to_equal(yaml_number("10"))
```

</details>

#### sets element at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("10"), yaml_number("20")])
val updated = yaml_sequence_set(seq, 0, yaml_number("99"))
val result = yaml_sequence_get(updated, 0)
expect(result).to_equal(yaml_number("99"))
```

</details>

#### appends element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1")])
val updated = yaml_sequence_append(seq, yaml_number("2"))
expect(yaml_sequence_length(updated)).to_equal(2)
```

</details>

#### gets length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("2"), yaml_number("3")])
expect(yaml_sequence_length(seq)).to_equal(3)
```

</details>

#### inserts at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("3")])
val updated = yaml_sequence_insert(seq, 1, yaml_number("2"))
expect(yaml_sequence_length(updated)).to_equal(3)
```

</details>

#### removes at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("2"), yaml_number("3")])
val updated = yaml_sequence_remove(seq, 1)
expect(yaml_sequence_length(updated)).to_equal(2)
```

</details>

#### search and transform

#### contains finds element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("2")])
expect(yaml_sequence_contains(seq, yaml_number("2"))).to_equal(true)
```

</details>

#### contains returns false for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1")])
expect(yaml_sequence_contains(seq, yaml_number("99"))).to_equal(false)
```

</details>

#### index_of finds element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("10"), yaml_number("20"), yaml_number("30")])
expect(yaml_sequence_index_of(seq, yaml_number("20"))).to_equal(1)
```

</details>

#### index_of returns -1 for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1")])
expect(yaml_sequence_index_of(seq, yaml_number("99"))).to_equal(-1)
```

</details>

#### reverses sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("2"), yaml_number("3")])
val reversed = yaml_sequence_reverse(seq)
val first = yaml_sequence_get(reversed, 0)
expect(first).to_equal(yaml_number("3"))
```

</details>

#### slices sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("2"), yaml_number("3"), yaml_number("4")])
val sliced = yaml_sequence_slice(seq, 1, 3)
expect(yaml_sequence_length(sliced)).to_equal(2)
```

</details>

### YAML Advanced Utilities

#### equality and copy

#### equal values are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = yaml_string("hello")
val b = yaml_string("hello")
expect(yaml_equals(a, b)).to_equal(true)
```

</details>

#### different values are not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = yaml_string("hello")
val b = yaml_string("world")
expect(yaml_equals(a, b)).to_equal(false)
```

</details>

#### deep copy produces equal value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = yaml_mapping([("key", yaml_string("val"))])
val copy = yaml_deep_copy(orig)
expect(yaml_equals(orig, copy)).to_equal(true)
```

</details>

#### merge

#### merges two mappings

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = yaml_mapping([("a", yaml_number("1"))])
val m2 = yaml_mapping([("b", yaml_number("2"))])
val merged = yaml_merge_mappings(m1, m2)
expect(yaml_mapping_has(merged, "a")).to_equal(true)
expect(yaml_mapping_has(merged, "b")).to_equal(true)
```

</details>

#### second mapping overrides first

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = yaml_mapping([("a", yaml_number("1"))])
val m2 = yaml_mapping([("a", yaml_number("2"))])
val merged = yaml_merge_mappings(m1, m2)
val result = yaml_mapping_get(merged, "a")
expect(result).to_equal(yaml_number("2"))
```

</details>

#### emptiness check

#### empty mapping is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_is_empty(yaml_mapping([]))).to_equal(true)
```

</details>

#### empty sequence is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_is_empty(yaml_sequence([]))).to_equal(true)
```

</details>

#### non-empty mapping is not empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_is_empty(yaml_mapping([("a", yaml_number("1"))]))).to_equal(false)
```

</details>

#### non-empty sequence is not empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_is_empty(yaml_sequence([yaml_number("1")]))).to_equal(false)
```

</details>

#### node counting and depth

#### counts nodes in scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_count_nodes(yaml_string("x"))).to_equal(1)
```

</details>

#### counts nodes in sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = yaml_sequence([yaml_number("1"), yaml_number("2")])
expect(yaml_count_nodes(seq)).to_be_greater_than(1)
```

</details>

#### depth of scalar is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_depth(yaml_string("x"))).to_equal(1)
```

</details>

#### depth of nested structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = yaml_mapping([("a", yaml_string("b"))])
val outer = yaml_mapping([("nested", inner)])
expect(yaml_depth(outer)).to_be_greater_than(1)
```

</details>

#### nested access

#### gets nested value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = yaml_mapping([("b", yaml_string("value"))])
val outer = yaml_mapping([("a", inner)])
val result = yaml_get_nested(outer, ["a", "b"])
expect(result).to_equal(yaml_string("value"))
```

</details>

#### sets nested value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = yaml_mapping([("b", yaml_string("old"))])
val outer = yaml_mapping([("a", inner)])
val updated = yaml_set_nested(outer, ["a", "b"], yaml_string("new"))
val result = yaml_get_nested(updated, ["a", "b"])
expect(result).to_equal(yaml_string("new"))
```

</details>

#### to_string and from_string

#### round-trips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_mapping([("key", yaml_string("val"))])
val s = yaml_to_string(v)
expect(s).to_contain("key")
```

</details>

#### pretty and compact print

#### pretty prints value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_mapping([("key", yaml_string("val"))])
val result = yaml_pretty_print(v)
expect(result).to_contain("key")
```

</details>

#### compact prints value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = yaml_mapping([("key", yaml_string("val"))])
val result = yaml_compact_print(v)
expect(result).to_contain("key")
```

</details>

### YAML Validate

#### multi-document

#### parses multiple documents

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "name: Alice\n---\nname: Bob"
val docs = yaml_parse_documents(input)
expect(docs.length()).to_be_greater_than(0)
```

</details>

#### serializes multiple documents

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docs = [yaml_string("doc1"), yaml_string("doc2")]
val result = yaml_serialize_documents(docs, "flow")
expect(result).to_contain("doc1")
expect(result).to_contain("doc2")
```

</details>

#### anchors and aliases

#### creates anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anchor = yaml_create_anchor("myanchor", yaml_string("value"))
expect(yaml_is_anchor(anchor)).to_equal(true)
```

</details>

#### creates alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alias = yaml_create_alias("myanchor")
expect(yaml_is_alias(alias)).to_equal(true)
```

</details>

#### is_anchor false for non-anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_is_anchor(yaml_string("x"))).to_equal(false)
```

</details>

#### is_alias false for non-alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(yaml_is_alias(yaml_string("x"))).to_equal(false)
```

</details>

#### gets anchor name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anchor = yaml_create_anchor("myanchor", yaml_string("value"))
expect(yaml_get_anchor_name(anchor)).to_equal("myanchor")
```

</details>

#### gets anchor value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anchor = yaml_create_anchor("myanchor", yaml_string("value"))
val v = yaml_get_anchor_value(anchor)
expect(yaml_equals(v, yaml_string("value"))).to_equal(true)
```

</details>

#### gets alias name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alias = yaml_create_alias("myanchor")
expect(yaml_get_alias_name(alias)).to_equal("myanchor")
```

</details>

#### resolves aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anchor = yaml_create_anchor("data", yaml_string("resolved"))
val alias = yaml_create_alias("data")
val resolved = yaml_resolve_aliases(alias, [anchor])
expect(yaml_equals(resolved, yaml_string("resolved"))).to_equal(true)
```

</details>

#### indentation utilities

#### creates indent string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = yaml_indent(2, 2)
expect(result.length()).to_be_greater_than(0)
```

</details>

### YAML Schema Validation

#### validation

#### validates matching type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = yaml_mapping([("type", yaml_string("scalar"))])
val result = yaml_validate_schema(yaml_string("hello"), schema)
expect(result.0).to_equal(true)
```

</details>

#### flatten mapping

#### flattens nested mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
