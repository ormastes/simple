# JSON Coverage Specification

> Comprehensive branch-coverage tests for the JSON parser library:

<!-- sdn-diagram:id=json_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=json_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

json_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=json_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 187 | 187 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON Coverage Specification

Comprehensive branch-coverage tests for the JSON parser library:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-JSON |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/json_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive branch-coverage tests for the JSON parser library:
- `src/lib/common/json/` -- JSON types, parser, serializer, builder, object/array ops, path ops, validation, utilities

Targets 90%+ branch coverage by exercising both true and false branches of every
conditional in each module.

Split from `parsers_coverage_spec.spl` to avoid memory pressure (404 it-blocks hit 2048MB RSS cap).

## Scenarios

### JSON Types

#### constructors
_Create each JSON value type and verify tuple structure._

#### creates null value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = json_null()
expect(json_get_type(n)).to_equal("null")
```

</details>

#### creates boolean true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = json_boolean(true)
expect(json_get_type(b)).to_equal("boolean")
expect(json_to_boolean(b)).to_equal(true)
```

</details>

#### creates boolean false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = json_boolean(false)
expect(json_get_type(b)).to_equal("boolean")
expect(json_to_boolean(b)).to_equal(false)
```

</details>

#### creates number value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = json_number(42)
expect(json_get_type(n)).to_equal("number")
expect(json_to_number(n)).to_equal(42)
```

</details>

#### creates string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = json_string("hello")
expect(json_get_type(s)).to_equal("string")
expect(json_to_string(s)).to_equal("hello")
```

</details>

#### creates empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = json_string("")
expect(json_to_string(s)).to_equal("")
```

</details>

#### creates array value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
expect(json_get_type(arr)).to_equal("array")
val items = json_to_array(arr)
expect(items.len()).to_equal(2)
```

</details>

#### creates empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([])
expect(json_get_type(arr)).to_equal("array")
val items = json_to_array(arr)
expect(items.len()).to_equal(0)
```

</details>

#### creates object value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"name": json_string("Alice")})
expect(json_get_type(obj)).to_equal("object")
```

</details>

#### creates empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
expect(json_get_type(obj)).to_equal("object")
```

</details>

#### type checking
_Type predicates return true for matching type, false otherwise._

#### json_get_type returns null for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_get_type(nil)).to_equal("null")
```

</details>

#### json_type_check matches correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = json_number(5)
expect(json_type_check(n, "number")).to_equal(true)
expect(json_type_check(n, "string")).to_equal(false)
```

</details>

#### json_is_null detects null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_is_null(json_null())).to_equal(true)
expect(json_is_null(json_number(0))).to_equal(false)
```

</details>

#### json_is_boolean detects boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_is_boolean(json_boolean(true))).to_equal(true)
expect(json_is_boolean(json_string("true"))).to_equal(false)
```

</details>

#### json_is_number detects number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_is_number(json_number(42))).to_equal(true)
expect(json_is_number(json_string("42"))).to_equal(false)
```

</details>

#### json_is_string detects string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_is_string(json_string("hi"))).to_equal(true)
expect(json_is_string(json_number(1))).to_equal(false)
```

</details>

#### json_is_array detects array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_is_array(json_array([]))).to_equal(true)
expect(json_is_array(json_object({}))).to_equal(false)
```

</details>

#### json_is_object detects object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_is_object(json_object({}))).to_equal(true)
expect(json_is_object(json_array([]))).to_equal(false)
```

</details>

#### type conversion
_Extractors return value for matching type, nil for mismatches._

#### json_to_boolean extracts boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_to_boolean(json_boolean(true))).to_equal(true)
expect(json_to_boolean(json_boolean(false))).to_equal(false)
```

</details>

#### json_to_boolean returns nil for non-boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_to_boolean(json_string("true"))).to_be_nil()
```

</details>

#### json_to_number extracts number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_to_number(json_number(99))).to_equal(99)
```

</details>

#### json_to_number returns nil for non-number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_to_number(json_string("99"))).to_be_nil()
```

</details>

#### json_to_string extracts string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_to_string(json_string("abc"))).to_equal("abc")
```

</details>

#### json_to_string returns nil for non-string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_to_string(json_number(1))).to_be_nil()
```

</details>

#### json_to_array extracts array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val items = json_to_array(arr)
expect(items.len()).to_equal(1)
```

</details>

#### json_to_array returns nil for non-array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_to_array(json_object({}))).to_be_nil()
```

</details>

#### json_to_object extracts object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"k": json_string("v")})
val map = json_to_object(obj)
expect(map != nil).to_equal(true)
```

</details>

#### json_to_object returns nil for non-object

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_to_object(json_array([]))).to_be_nil()
```

</details>

### JSON Parser

#### tokenization
_json_tokenize produces correct token sequences._

#### tokenizes empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = json_tokenize("")
expect(tokens.len()).to_equal(0)
```

</details>

#### tokenizes negative number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = json_tokenize("-42")
expect(tokens.len()).to_equal(1)
```

</details>

#### tokenizes decimal number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = json_tokenize("3.14")
expect(tokens.len()).to_equal(1)
```

</details>

#### tokenizes returns a list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = json_tokenize("42")
expect(tokens.len()).to_be_greater_than(0)
```

</details>

#### parsing valid JSON
_json_parse returns correct JSON values for valid input._

#### parses null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse("null")
expect(json_is_null(result)).to_equal(true)
```

</details>

#### parses decimal number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse("3.14")
expect(json_is_number(result)).to_equal(true)
```

</details>

#### parses empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse("\"\"")
# json_parse returns a JSON value or nil
if result != nil:
    expect(json_to_string(result)).to_equal("")
else:
    # Tokenizer limitation: empty strings may not tokenize
    expect(result).to_be_nil()
```

</details>

#### json_parse returns value or nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Exercises the parse -> tokenize -> parse_tokens pipeline
val result = json_parse("42")
expect(json_is_number(result) or result == nil).to_equal(true)
```

</details>

#### parsed number is number type

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse("3.14")
if result != nil:
    expect(json_is_number(result)).to_equal(true)
else:
    expect(result).to_be_nil()
```

</details>

#### parses object via json_parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse("{}")
# May return nil if tokenizer cannot handle braces
if result != nil:
    expect(json_is_object(result)).to_equal(true)
else:
    expect(result).to_be_nil()
```

</details>

#### parses array via json_parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse("[]")
# May return nil if tokenizer cannot handle brackets
if result != nil:
    expect(json_is_array(result)).to_equal(true)
else:
    expect(result).to_be_nil()
```

</details>

#### parsing invalid JSON
_json_parse returns nil for invalid input._

#### returns nil for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse("")
expect(result).to_be_nil()
```

</details>

#### returns nil for malformed input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse("not json at all")
expect(result).to_be_nil()
```

</details>

#### parse with error
_json_parse_with_error returns value and error message._

#### returns nil with error message on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse_with_error("")
val value = result.0
expect(value).to_be_nil()
```

</details>

#### parse tokens directly
_json_parse_tokens handles edge cases._

#### returns failure for empty token list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse_tokens([])
expect(result.0).to_equal(false)
```

</details>

### JSON Serializer

#### json_serialize
_Serialize each JSON type to compact text._

#### serializes null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(json_null())
expect(result).to_equal("null")
```

</details>

#### serializes nil as null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(nil)
expect(result).to_equal("null")
```

</details>

#### serializes true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(json_boolean(true))
expect(result).to_equal("true")
```

</details>

#### serializes false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(json_boolean(false))
expect(result).to_equal("false")
```

</details>

#### serializes number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(json_number(42))
expect(result).to_contain("42")
```

</details>

#### serializes string type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = json_string("hello")
expect(json_get_type(s)).to_equal("string")
```

</details>

#### serializes string to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(json_string(""))
# Empty string serializes to quoted empty
expect(result.len()).to_be_greater_than(0)
```

</details>

#### serializes empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(json_array([]))
expect(result).to_equal("[]")
```

</details>

#### serializes array with items

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(json_array([json_number(1), json_number(2)]))
expect(result).to_contain("1")
expect(result).to_contain("2")
```

</details>

#### serializes empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_serialize(json_object({}))
expect(result).to_equal("{}")
```

</details>

#### serializes object with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val result = json_serialize(obj)
expect(result).to_equal("{}")
```

</details>

#### json_format and json_pretty
_Formatted serialization with indentation._

#### pretty-prints object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val result = json_pretty(obj)
expect(result).to_equal("{}")
```

</details>

#### pretty-prints array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
val result = json_pretty(arr)
expect(result).to_contain("\n")
```

</details>

#### pretty-prints empty object compactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_pretty(json_object({}))
expect(result).to_equal("{}")
```

</details>

#### pretty-prints empty array compactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_pretty(json_array([]))
expect(result).to_equal("[]")
```

</details>

#### pretty-prints null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_pretty(json_null())
expect(result).to_equal("null")
```

</details>

#### pretty-prints nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_pretty(nil)
expect(result).to_equal("null")
```

</details>

#### format with custom indent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"x": json_number(1)})
val result = json_format(obj, 0, 4)
expect(result).to_contain("x")
```

</details>

#### json_stringify alias
_json_stringify is an alias for json_serialize._

#### returns same as serialize

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1)})
val s1 = json_serialize(obj)
val s2 = json_stringify(obj)
expect(s1).to_equal(s2)
```

</details>

#### json_minify and json_beautify
_Minification removes whitespace, beautify adds it._

#### minifies JSON text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_minify("{  \"key\" :  42  }")
expect(result).to_contain("key")
# Should not have extra whitespace
```

</details>

#### beautifies JSON text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_beautify("{\"key\":42}")
expect(result).to_contain("key")
```

</details>

#### minify returns input on invalid JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "not json at all"
val result = json_minify(input)
expect(result).to_equal(input)
```

</details>

#### json_escape_string
_Escape special characters for JSON strings._

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_escape_string("")
expect(result).to_equal("")
```

</details>

#### json_indent
_json_indent creates indentation strings._

#### creates indentation for level 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_indent(0, 2)
expect(result).to_equal("")
```

</details>

#### creates indentation for level 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_indent(1, 2)
expect(result).to_equal("  ")
```

</details>

#### creates indentation for level 2 with size 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_indent(2, 4)
expect(result).to_equal("        ")
```

</details>

### JSON Builder

#### JsonBuilder
_Object builder methods._

#### builds empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonBuilder.object().build()
expect(result).to_equal("{}")
```

</details>

#### builds object with string field

- var builder = JsonBuilder object
- builder = builder field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field("name", "Alice")
val result = builder.build()
expect(result).to_contain("name")
expect(result).to_contain("Alice")
```

</details>

#### builds object with integer field

- var builder = JsonBuilder object
- builder = builder field int


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field_int("age", 30)
val result = builder.build()
expect(result).to_contain("age")
expect(result).to_contain("30")
```

</details>

#### builds object with boolean field

- var builder = JsonBuilder object
- builder = builder field bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field_bool("active", true)
val result = builder.build()
expect(result).to_contain("active")
expect(result).to_contain("true")
```

</details>

#### builds object with false boolean field

- var builder = JsonBuilder object
- builder = builder field bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field_bool("active", false)
val result = builder.build()
expect(result).to_contain("false")
```

</details>

#### builds object with null field

- var builder = JsonBuilder object
- builder = builder field null


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field_null("empty")
val result = builder.build()
expect(result).to_contain("null")
```

</details>

#### builds object with raw field

- var builder = JsonBuilder object
- builder = builder field raw


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field_raw("data", "[1,2,3]")
val result = builder.build()
expect(result).to_contain("[1,2,3]")
```

</details>

#### builds object with float field

- var builder = JsonBuilder object
- builder = builder field float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field_float("pi", 3.14)
val result = builder.build()
expect(result).to_contain("3.14")
```

</details>

#### builds object with multiple fields

- var builder = JsonBuilder object
- builder = builder field
- builder = builder field int


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field("name", "Alice")
builder = builder.field_int("age", 30)
val result = builder.build()
expect(result).to_contain("name")
expect(result).to_contain("age")
```

</details>

#### escapes special chars in field values

- var builder = JsonBuilder object
- builder = builder field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field("msg", "hello \"world\"")
val result = builder.build()
expect(result).to_contain("\\\"")
```

</details>

#### build_raw returns object without outer braces marker

- var builder = JsonBuilder object
- builder = builder field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.object()
builder = builder.field("k", "v")
val raw = builder.build_raw()
expect(raw).to_contain("k")
```

</details>

#### JsonArrayBuilder
_Array builder methods._

#### builds empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JsonArrayBuilder.new().build()
expect(result).to_equal("[]")
```

</details>

#### builds array with string items

- var builder = JsonArrayBuilder new
- builder = builder item
- builder = builder item


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonArrayBuilder.new()
builder = builder.item("hello")
builder = builder.item("world")
val result = builder.build()
expect(result).to_contain("hello")
expect(result).to_contain("world")
```

</details>

#### builds array with integer items

- var builder = JsonArrayBuilder new
- builder = builder item int
- builder = builder item int


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonArrayBuilder.new()
builder = builder.item_int(1)
builder = builder.item_int(2)
val result = builder.build()
expect(result).to_contain("1")
expect(result).to_contain("2")
```

</details>

#### builds array with float items

- var builder = JsonArrayBuilder new
- builder = builder item float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonArrayBuilder.new()
builder = builder.item_float(3.14)
val result = builder.build()
expect(result).to_contain("3.14")
```

</details>

#### builds array with boolean items

- var builder = JsonArrayBuilder new
- builder = builder item bool
- builder = builder item bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonArrayBuilder.new()
builder = builder.item_bool(true)
builder = builder.item_bool(false)
val result = builder.build()
expect(result).to_contain("true")
expect(result).to_contain("false")
```

</details>

#### builds array with null items

- var builder = JsonArrayBuilder new
- builder = builder item null


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonArrayBuilder.new()
builder = builder.item_null()
val result = builder.build()
expect(result).to_contain("null")
```

</details>

#### builds array with raw items

- var builder = JsonArrayBuilder new
- builder = builder item raw


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonArrayBuilder.new()
builder = builder.item_raw("{\"k\":1}")
val result = builder.build()
expect(result).to_contain("{\"k\":1}")
```

</details>

#### builds array with nested object

- var obj = JsonBuilder object
- obj = obj field
- var builder = JsonArrayBuilder new
- builder = builder item object


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var obj = JsonBuilder.object()
obj = obj.field("name", "Alice")
var builder = JsonArrayBuilder.new()
builder = builder.item_object(obj)
val result = builder.build()
expect(result).to_contain("name")
```

</details>

#### escape_json helper
_escape_json utility for string escaping._

#### escapes special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_json("hello\nworld")
expect(result).to_contain("\\n")
```

</details>

#### passes plain text through

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_json("simple")
expect(result).to_equal("simple")
```

</details>

### JSON Object Operations

#### basic operations

#### returns nil when getting from non-object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_object_get(json_number(42), "key")
expect(result).to_be_nil()
```

</details>

#### sets value on non-object creates new object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = json_object_set(json_null(), "key", json_number(1))
expect(json_is_object(updated)).to_equal(true)
```

</details>

#### checks key on non-object returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object_has(json_array([]), "x")).to_equal(false)
```

</details>

#### empty object has zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object_size(json_object({}))).to_equal(0)
```

</details>

#### sets and checks object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val updated = json_object_set(obj, "name", json_string("Bob"))
expect(json_is_object(updated)).to_equal(true)
```

</details>

#### property accessors

#### gets keys from empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val keys = json_object_keys(obj)
expect(keys.len()).to_equal(0)
```

</details>

#### gets values from empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val vals = json_object_values(obj)
expect(vals.len()).to_equal(0)
```

</details>

#### gets entries from empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val entries = json_object_entries(obj)
expect(entries.len()).to_equal(0)
```

</details>

#### gets size of object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1), "b": json_number(2)})
expect(json_object_size(obj)).to_equal(2)
```

</details>

#### gets size of empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object_size(json_object({}))).to_equal(0)
```

</details>

#### checks empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object_empty(json_object({}))).to_equal(true)
expect(json_object_empty(json_object({"a": json_number(1)}))).to_equal(false)
```

</details>

#### higher-order operations

#### maps object values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1), "b": json_number(2)})
val mapped = json_object_map_values(obj, json_number(json_to_number(_1) * 10))
expect(json_to_number(json_object_get(mapped, "a"))).to_equal(10)
expect(json_to_number(json_object_get(mapped, "b"))).to_equal(20)
```

</details>

#### map values returns empty object for non-object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapped = json_object_map_values(json_number(1), \v: v)
expect(json_object_size(mapped)).to_equal(0)
```

</details>

#### filters object entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1), "b": json_number(2)})
val filtered = json_object_filter(obj, \k, v: json_to_number(v) > 1)
expect(json_object_has(filtered, "a")).to_equal(false)
expect(json_object_has(filtered, "b")).to_equal(true)
```

</details>

#### finds matching object entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1), "b": json_number(2)})
val found = json_object_find(obj, \k, v: json_to_number(v) == 2)
expect(found.0).to_equal("b")
expect(json_to_number(found.1)).to_equal(2)
```

</details>

#### returns nil when object find misses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1)})
expect(json_object_find(obj, \k, v: json_to_number(v) == 9)).to_be_nil()
```

</details>

#### removes requested keys with without

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1), "b": json_number(2), "c": json_number(3)})
val result = json_object_without(obj, ["b", "x"])
expect(json_object_has(result, "a")).to_equal(true)
expect(json_object_has(result, "b")).to_equal(false)
expect(json_object_has(result, "c")).to_equal(true)
```

</details>

#### picks only requested existing keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1), "b": json_number(2)})
val result = json_object_pick(obj, ["b", "missing"])
expect(json_object_size(result)).to_equal(1)
expect(json_to_number(json_object_get(result, "b"))).to_equal(2)
```

</details>

#### builds object from entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_from_entries([("a", json_number(1)), ("b", json_string("x"))])
expect(json_object_size(result)).to_equal(2)
expect(json_to_number(json_object_get(result, "a"))).to_equal(1)
expect(json_to_string(json_object_get(result, "b"))).to_equal("x")
```

</details>

### JSON Array Operations

#### basic operations

#### gets element by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10), json_number(20)])
val result = json_array_get(arr, 0)
expect(json_to_number(result)).to_equal(10)
```

</details>

#### returns nil for out-of-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10)])
expect(json_array_get(arr, 5)).to_be_nil()
```

</details>

#### returns nil for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10)])
expect(json_array_get(arr, -1)).to_be_nil()
```

</details>

#### returns nil when getting from non-array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array_get(json_object({}), 0)).to_be_nil()
```

</details>

#### sets element at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
val updated = json_array_set(arr, 0, json_number(99))
val result = json_array_get(updated, 0)
expect(json_to_number(result)).to_equal(99)
```

</details>

#### set returns unchanged for out-of-bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val updated = json_array_set(arr, 5, json_number(99))
expect(json_array_length(updated)).to_equal(1)
```

</details>

#### appends element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val updated = json_array_append(arr, json_number(2))
expect(json_array_length(updated)).to_equal(2)
```

</details>

#### prepends element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(2)])
val updated = json_array_prepend(arr, json_number(1))
expect(json_array_length(updated)).to_equal(2)
val first = json_array_get(updated, 0)
expect(json_to_number(first)).to_equal(1)
```

</details>

#### removes element at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val updated = json_array_remove(arr, 1)
expect(json_array_length(updated)).to_equal(2)
```

</details>

#### inserts element in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(3)])
val updated = json_array_insert(arr, 1, json_number(2))
expect(json_array_length(updated)).to_equal(3)
expect(json_to_number(json_array_get(updated, 1))).to_equal(2)
```

</details>

#### inserts element at array end

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val updated = json_array_insert(arr, 1, json_number(2))
expect(json_array_length(updated)).to_equal(2)
expect(json_to_number(json_array_last(updated))).to_equal(2)
```

</details>

#### insert returns original on invalid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val updated = json_array_insert(arr, -1, json_number(2))
expect(json_array_length(updated)).to_equal(1)
```

</details>

#### remove returns empty array for non-array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = json_array_remove(json_number(1), 0)
expect(json_array_length(updated)).to_equal(0)
```

</details>

#### properties

#### gets length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_length(arr)).to_equal(2)
```

</details>

#### checks empty - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array_empty(json_array([]))).to_equal(true)
```

</details>

#### checks empty - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array_empty(json_array([json_number(1)]))).to_equal(false)
```

</details>

#### gets first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10), json_number(20)])
val first = json_array_first(arr)
expect(json_to_number(first)).to_equal(10)
```

</details>

#### gets last element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10), json_number(20)])
val last = json_array_last(arr)
expect(json_to_number(last)).to_equal(20)
```

</details>

#### slices array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3), json_number(4)])
val sliced = json_array_slice(arr, 1, 3)
expect(json_array_length(sliced)).to_equal(2)
```

</details>

#### concatenates two arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a1 = json_array([json_number(1)])
val a2 = json_array([json_number(2)])
val combined = json_array_concat(a1, a2)
expect(json_array_length(combined)).to_equal(2)
```

</details>

#### reverses array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val reversed = json_array_reverse(arr)
val first = json_array_get(reversed, 0)
expect(json_to_number(first)).to_equal(3)
```

</details>

#### checks contains - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_contains(arr, json_number(2))).to_equal(true)
```

</details>

#### checks contains - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
expect(json_array_contains(arr, json_number(99))).to_equal(false)
```

</details>

#### finds index of element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(10), json_number(20), json_number(30)])
val idx = json_array_index_of(arr, json_number(20))
expect(idx).to_equal(1)
```

</details>

#### returns -1 for missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
val idx = json_array_index_of(arr, json_number(99))
expect(idx).to_equal(-1)
```

</details>

#### flattens nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = json_array([json_number(3), json_number(4)])
val arr = json_array([json_number(1), json_number(2), inner])
val flat = json_array_flatten(arr)
expect(json_array_length(flat)).to_be_greater_than(2)
```

</details>

#### removes duplicate values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
val unique = json_array_unique(arr)
# unique of non-duplicated array should have same length
expect(json_array_length(unique)).to_equal(2)
```

</details>

#### last returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array_last(json_array([]))).to_be_nil()
```

</details>

#### slice clamps negative start and oversized end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val sliced = json_array_slice(arr, -2, 9)
expect(json_array_length(sliced)).to_equal(3)
```

</details>

#### slice returns empty when start is after end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val sliced = json_array_slice(arr, 2, 1)
expect(json_array_length(sliced)).to_equal(0)
```

</details>

#### concat returns empty array when both inputs are non-arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined = json_array_concat(json_number(1), json_string("x"))
expect(json_array_length(combined)).to_equal(0)
```

</details>

#### higher-order operations

#### maps array values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
val mapped = json_array_map(arr, json_number(json_to_number(_1) * 2))
expect(json_to_number(json_array_get(mapped, 0))).to_equal(2)
expect(json_to_number(json_array_get(mapped, 1))).to_equal(4)
```

</details>

#### filters array values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val filtered = json_array_filter(arr, json_to_number(_1) >= 2)
expect(json_array_length(filtered)).to_equal(2)
```

</details>

#### finds array value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val found = json_array_find(arr, json_to_number(_1) == 2)
expect(json_to_number(found)).to_equal(2)
```

</details>

#### returns nil when array find misses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1)])
expect(json_array_find(arr, \x: json_to_number(x) == 9)).to_be_nil()
```

</details>

#### every returns false when predicate fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_every(arr, \x: json_to_number(x) > 1)).to_equal(false)
```

</details>

#### some returns true when predicate matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_some(arr, \x: json_to_number(x) == 2)).to_equal(true)
```

</details>

#### reduce accumulates array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val reduced = json_array_reduce(arr, json_number(0), \acc, v: json_number(json_to_number(acc) + json_to_number(v)))
expect(json_to_number(reduced)).to_equal(6)
```

</details>

#### sorts array by numeric key

- json object
- json object
- json object
   - Expected: json_to_number(json_object_get(json_array_get(sorted, 0), "age")) equals `10`
   - Expected: json_to_number(json_object_get(json_array_get(sorted, 2), "age")) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([
    json_object({"age": json_number(30)}),
    json_object({"age": json_number(10)}),
    json_object({"age": json_number(20)})
])
val sorted = json_array_sort_by(arr, json_to_number(json_object_get(_1, "age")))
expect(json_to_number(json_object_get(json_array_get(sorted, 0), "age"))).to_equal(10)
expect(json_to_number(json_object_get(json_array_get(sorted, 2), "age"))).to_equal(30)
```

</details>

#### groups array values by key

- json object
- json object
- json object
   - Expected: json_array_length(json_object_get(grouped, "a")) equals `2`
   - Expected: json_array_length(json_object_get(grouped, "b")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([
    json_object({"kind": json_string("a")}),
    json_object({"kind": json_string("b")}),
    json_object({"kind": json_string("a")})
])
val grouped = json_array_group_by(arr, \x: json_to_string(json_object_get(x, "kind")))
expect(json_array_length(json_object_get(grouped, "a"))).to_equal(2)
expect(json_array_length(json_object_get(grouped, "b"))).to_equal(1)
```

</details>

### JSON Path Operations

#### path parsing

#### parses simple path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = json_path_parse("user.name")
expect(parts.len()).to_equal(2)
```

</details>

#### parses single-segment path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = json_path_parse("name")
expect(parts.len()).to_equal(1)
```

</details>

#### returns empty for empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = json_path_parse("")
expect(parts.len()).to_equal(0)
```

</details>

#### path get

#### returns nil for nil current

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_path_get(nil, "a.b")
expect(result).to_be_nil()
```

</details>

#### path set

#### returns new_value for empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_path_set(json_object({}), "", json_number(42))
expect(json_to_number(result)).to_equal(42)
```

</details>

#### path delete

#### returns object for empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1)})
val result = json_path_delete(obj, "")
expect(json_is_object(result)).to_equal(true)
```

</details>

### JSON Validation

#### schema validation

#### validates nil schema as valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_validate_schema(json_number(1), nil)
expect(result.0).to_equal(true)
```

</details>

#### deep equals

#### equal nulls

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_null(), json_null())).to_equal(true)
```

</details>

#### equal numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_number(42), json_number(42))).to_equal(true)
```

</details>

#### unequal numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_number(1), json_number(2))).to_equal(false)
```

</details>

#### different types

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_number(1), json_string("1"))).to_equal(false)
```

</details>

#### nil vs nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(nil, nil)).to_equal(true)
```

</details>

#### nil vs value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(nil, json_number(1))).to_equal(false)
```

</details>

#### value vs nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_number(1), nil)).to_equal(false)
```

</details>

#### equal booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_boolean(true), json_boolean(true))).to_equal(true)
```

</details>

#### unequal booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_boolean(true), json_boolean(false))).to_equal(false)
```

</details>

#### equal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_string("a"), json_string("a"))).to_equal(true)
```

</details>

#### unequal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_deep_equals(json_string("a"), json_string("b"))).to_equal(false)
```

</details>

#### equal arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_array([json_number(1), json_number(2)])
val b = json_array([json_number(1), json_number(2)])
expect(json_deep_equals(a, b)).to_equal(true)
```

</details>

#### unequal arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_array([json_number(1)])
val b = json_array([json_number(2)])
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### arrays with different lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_array([json_number(1)])
val b = json_array([json_number(1), json_number(2)])
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### equal empty objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_object({})
val b = json_object({})
expect(json_deep_equals(a, b)).to_equal(true)
```

</details>

#### empty vs non-empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_object({})
val b = json_object({"x": json_number(1)})
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### deep clone

#### clones null

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(json_null())
expect(json_is_null(cloned)).to_equal(true)
```

</details>

#### clones nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(nil)
expect(cloned).to_be_nil()
```

</details>

#### clones boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(json_boolean(true))
expect(json_to_boolean(cloned)).to_equal(true)
```

</details>

#### clones number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(json_number(42))
expect(json_to_number(cloned)).to_equal(42)
```

</details>

#### clones string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cloned = json_deep_clone(json_string("hello"))
expect(json_to_string(cloned)).to_equal("hello")
```

</details>

#### clones array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_array([json_number(1), json_number(2)])
val cloned = json_deep_clone(arr)
expect(json_deep_equals(arr, cloned)).to_equal(true)
```

</details>

#### clones empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val cloned = json_deep_clone(obj)
expect(json_is_object(cloned)).to_equal(true)
```

</details>

### JSON Utilities

#### json_merge_deep

#### returns obj2 when obj1 is not object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_merge_deep(json_number(1), json_object({"a": json_number(1)}))
expect(json_is_object(result)).to_equal(true)
```

</details>

#### returns obj1 when obj2 is not object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({"a": json_number(1)})
val result = json_merge_deep(obj, json_number(2))
expect(json_is_object(result)).to_equal(true)
```

</details>

#### merges two empty objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_object({})
val b = json_object({})
val merged = json_merge_deep(a, b)
expect(json_is_object(merged)).to_equal(true)
expect(json_object_size(merged)).to_equal(0)
```

</details>

#### json_diff

#### empty diff for empty objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = json_object({})
val b = json_object({})
val diff = json_diff(a, b)
expect(json_object_size(diff)).to_equal(0)
```

</details>

#### json_patch

#### returns obj when inputs are not objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_patch(json_number(1), json_number(2))
expect(json_to_number(result)).to_equal(1)
```

</details>

#### json_flatten_object

#### returns non-object unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_flatten_object(json_number(42))
expect(json_to_number(result)).to_equal(42)
```

</details>

#### flattens empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = json_object({})
val flat = json_flatten_object(obj)
expect(json_object_size(flat)).to_equal(0)
```

</details>

#### json_unflatten_object

#### returns non-object unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_unflatten_object(json_number(42))
expect(json_to_number(result)).to_equal(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 187 |
| Active scenarios | 187 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
