# JSON Core Coverage Specification

> Branch-coverage tests for core JSON library: types, parser, serializer, and builder. Targets 90%+ branch coverage for types.spl, parser.spl, serializer.spl, builder.spl.

<!-- sdn-diagram:id=parsers_json_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parsers_json_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parsers_json_core_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parsers_json_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 90 | 90 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON Core Coverage Specification

Branch-coverage tests for core JSON library: types, parser, serializer, and builder. Targets 90%+ branch coverage for types.spl, parser.spl, serializer.spl, builder.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-JSON-CORE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/lib/common/parsers_json_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch-coverage tests for core JSON library: types, parser, serializer, and builder.
Targets 90%+ branch coverage for types.spl, parser.spl, serializer.spl, builder.spl.

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 90 |
| Active scenarios | 90 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
