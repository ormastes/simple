# JSON Utilities Specification

> This specification covers JSON utility functions for formatting, parsing, and building JSON structures: 1. JSON value formatting (string, number, boolean, null) 2. JSON array and object construction 3. JSON builder classes for fluent API 4. Common JSON patterns (API responses, pagination) 5. JSON validation (structure, balance checking)

<!-- sdn-diagram:id=json_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=json_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

json_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=json_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON Utilities Specification

This specification covers JSON utility functions for formatting, parsing, and building JSON structures: 1. JSON value formatting (string, number, boolean, null) 2. JSON array and object construction 3. JSON builder classes for fluent API 4. Common JSON patterns (API responses, pagination) 5. JSON validation (structure, balance checking)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #JSON-001 to #JSON-020 |
| Category | Tooling \| Data Format |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/json_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification covers JSON utility functions for formatting, parsing, and building JSON structures:
1. JSON value formatting (string, number, boolean, null)
2. JSON array and object construction
3. JSON builder classes for fluent API
4. Common JSON patterns (API responses, pagination)
5. JSON validation (structure, balance checking)

## Key Concepts

| Concept | Description |
|---------|-------------|
| JSON Formatting | Convert values to JSON-compliant text |
| Escaping | Handle special characters and escape sequences |
| Builder Pattern | Fluent API for constructing complex structures |
| Validation | Check JSON structure validity |
| Common Patterns | API responses, pagination metadata |

## Behavior

- String values are properly escaped and quoted
- Null values produce "null" text
- Booleans produce "true" or "false"
- Numbers are converted to string representation
- Builders provide mutable construction API
- Validation checks for balanced braces and valid structure

## Scenarios

### JSON Utilities

### JSON Value Formatting

#### formats string

1. expect json string


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect json_string("hello") == "\"hello\""
```

</details>

#### escapes quotes in string

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_string("She said \"hi\"")
expect result.contains("\\\"")
```

</details>

#### escapes newlines in string

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_string("line1\nline2")
expect result.contains("\\n")
```

</details>

#### formats number

1. expect json number
2. expect json number


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect json_number(42) == "42"
expect json_number(-10) == "-10"
```

</details>

#### formats boolean

1. expect json bool
2. expect json bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect json_bool(true) == "true"
expect json_bool(false) == "false"
```

</details>

#### formats null

1. expect json null


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect json_null() == "null"
```

</details>

### JSON Arrays

#### formats string array

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_array_strings(["apple", "banana", "cherry"])
expect result.contains("[")
expect result.contains("]")
expect result.contains("\"apple\"")
expect result.contains("\"banana\"")
```

</details>

#### formats number array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_array_numbers([1, 2, 3])
expect result == "[1, 2, 3]"
```

</details>

#### formats mixed array

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [json_string("text"), json_number(42), json_bool(true)]
val result = json_array(items)
expect result.contains("\"text\"")
expect result.contains("42")
expect result.contains("true")
```

</details>

### JSON Objects

#### formats key-value pair

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_pair(key="name", value=json_string("Alice"))
expect result.contains("\"name\"")
expect result.contains("\"Alice\"")
```

</details>

#### formats object

1.
2.
3. expect result contains
4. expect result contains
5. expect result contains
6. expect result contains
7. expect result contains
8. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = [
    ("name", json_string("Alice")),
    ("age", json_number(30))
]
val result = json_object(pairs)
expect result.contains(r"{")
expect result.contains(r"}")
expect result.contains("\"name\"")
expect result.contains("\"Alice\"")
expect result.contains("\"age\"")
expect result.contains("30")
```

</details>

### JSON Builder

#### builds basic object

1. var builder = JsonBuilder create
2. builder add string
3. builder add number
4. builder add bool
5. expect result contains
6. expect result contains
7. expect result contains
8. expect result contains
9. expect result contains
10. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.create()
builder.add_string(key="name", value="Bob")
builder.add_number("age", 25)
builder.add_bool("active", true)
val result = builder.build()
expect result.contains("\"name\"")
expect result.contains("\"Bob\"")
expect result.contains("\"age\"")
expect result.contains("25")
expect result.contains("\"active\"")
expect result.contains("true")
```

</details>

#### builds with null

1. var builder = JsonBuilder create
2. builder add string
3. builder add null
4. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.create()
builder.add_string(key="name", value="Test")
builder.add_null("data")
val result = builder.build()
expect result.contains("null")
```

</details>

#### builds with array

1. var builder = JsonBuilder create
2. builder add array
3. expect result contains
4. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonBuilder.create()
val items = [json_string("a"), json_string("b")]
builder.add_array("items", items)
val result = builder.build()
expect result.contains("\"items\"")
expect result.contains("[")
```

</details>

### JSON Array Builder

#### builds mixed array

1. var builder = JsonArrayBuilder create
2. builder add string
3. builder add number
4. builder add bool
5. builder add null
6. expect result contains
7. expect result contains
8. expect result contains
9. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = JsonArrayBuilder.create()
builder.add_string("apple")
builder.add_number(42)
builder.add_bool(true)
builder.add_null()
val result = builder.build()
expect result.contains("\"apple\"")
expect result.contains("42")
expect result.contains("true")
expect result.contains("null")
```

</details>

### Common Structures

#### creates success response

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_success("Operation completed")
expect result.contains("\"status\"")
expect result.contains("\"success\"")
expect result.contains("\"message\"")
```

</details>

#### creates error response

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_error("Not found", 404)
expect result.contains("\"status\"")
expect result.contains("\"error\"")
expect result.contains("\"code\"")
expect result.contains("404")
```

</details>

#### creates data response

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = json_object([("id", json_number(1))])
val result = json_data(data)
expect result.contains("\"status\"")
expect result.contains("\"data\"")
```

</details>

### Validation

#### detects JSON object

1. expect looks like json
2. expect not looks like json


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json_obj = '{"key": "value"}'
expect looks_like_json(json_obj)
expect not looks_like_json("not json")
```

</details>

#### detects JSON array

1. expect looks like json
2. expect not looks like json


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect looks_like_json("[1, 2, 3]")
expect not looks_like_json("plain text")
```

</details>

#### handles empty string

1. expect not looks like json


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not looks_like_json("")
```

</details>

#### validates balanced braces

1. expect has balanced braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val balanced = '{"a": [1, 2]}'
expect has_balanced_braces(balanced)
```

</details>

#### detects unbalanced braces

1. expect not has balanced braces
2. expect not has balanced braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unbalanced1 = '{"a": [1, 2}'
val unbalanced2 = '{"a": 1]]'
expect not has_balanced_braces(unbalanced1)
expect not has_balanced_braces(unbalanced2)
```

</details>

### Common Patterns

#### creates API response with data

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = json_string("result")
val result = api_response(true, "Success", Some(data))
expect result.contains("\"success\"")
expect result.contains("true")
expect result.contains("\"data\"")
```

</details>

#### creates API response without data

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = api_response(false, "Failed", nil)
expect result.contains("\"success\"")
expect result.contains("false")
expect result.contains("null")
```

</details>

#### creates pagination meta

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains
5. expect result contains
6. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pagination_meta(page=2, per_page=10, total=45)
expect result.contains("\"page\"")
expect result.contains("2")
expect result.contains("\"total\"")
expect result.contains("45")
expect result.contains("\"total_pages\"")
expect result.contains("5")
```

</details>

#### creates timestamp JSON

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = timestamp_json(unix=1640000000, iso="2021-12-20T12:00:00Z")
expect result.contains("\"unix\"")
expect result.contains("1640000000")
expect result.contains("\"iso\"")
expect result.contains("2021-12-20")
```

</details>

### Edge Cases

#### escapes backslash in string

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_string("path\\to\\file")
expect result.contains("\\\\")
```

</details>

#### formats empty object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_object([])
expect result == r"{}"
```

</details>

#### formats empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_array([])
expect result == "[]"
```

</details>

#### handles nested objects

1. var inner = JsonBuilder create
2. inner add string
3. var outer = JsonBuilder create
4. outer add string
5. outer add raw
6. expect result contains
7. expect result contains
8. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inner = JsonBuilder.create()
inner.add_string(key="city", value="NYC")

var outer = JsonBuilder.create()
outer.add_string(key="name", value="Alice")
outer.add_raw(key="address", raw_json=inner.build())

val result = outer.build()
expect result.contains("\"name\"")
expect result.contains("\"address\"")
expect result.contains("\"city\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
