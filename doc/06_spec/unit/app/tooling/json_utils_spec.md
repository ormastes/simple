# Json Utils Specification

> Tests covering JSON Utilities, JSON Value Formatting, JSON Arrays, JSON Objects, JSON Builder, JSON Array Builder, Common Structures, Validation, Common Patterns, Edge Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Utils Specification

## Scenarios

### JSON Utilities

### JSON Value Formatting

#### formats string

- formats string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats string")
expect json_string("hello") == "\"hello\""
```

</details>

#### escapes quotes in string

- escapes quotes in string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes quotes in string")
val result = json_string("She said \"hi\"")
expect result.contains("\\\"")
```

</details>

#### escapes newlines in string

- escapes newlines in string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes newlines in string")
val result = json_string("line1\nline2")
expect result.contains("\\n")
```

</details>

#### formats number

- formats number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats number")
expect json_number(42) == "42"
expect json_number(-10) == "-10"
```

</details>

#### formats boolean

- formats boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats boolean")
expect json_bool(true) == "true"
expect json_bool(false) == "false"
```

</details>

#### formats null

- formats null


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats null")
expect json_null() == "null"
```

</details>

### JSON Arrays

#### formats string array

- formats string array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats string array")
val result = json_array_strings(["apple", "banana", "cherry"])
expect result.contains("[")
expect result.contains("]")
expect result.contains("\"apple\"")
expect result.contains("\"banana\"")
```

</details>

#### formats number array

- formats number array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats number array")
val result = json_array_numbers([1, 2, 3])
expect result == "[1, 2, 3]"
```

</details>

#### formats mixed array

- formats mixed array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats mixed array")
val items = [json_string("text"), json_number(42), json_bool(true)]
val result = json_array(items)
expect result.contains("\"text\"")
expect result.contains("42")
expect result.contains("true")
```

</details>

### JSON Objects

#### formats key-value pair

- formats key-value pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats key-value pair")
val result = json_pair(key="name", value=json_string("Alice"))
expect result.contains("\"name\"")
expect result.contains("\"Alice\"")
```

</details>

#### formats object

- formats object


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats object")
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

- builds basic object


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds basic object")
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

- builds with null


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with null")
var builder = JsonBuilder.create()
builder.add_string(key="name", value="Test")
builder.add_null("data")
val result = builder.build()
expect result.contains("null")
```

</details>

#### builds with array

- builds with array


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with array")
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

- builds mixed array


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds mixed array")
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

- creates success response


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates success response")
val result = json_success("Operation completed")
expect result.contains("\"status\"")
expect result.contains("\"success\"")
expect result.contains("\"message\"")
```

</details>

#### creates error response

- creates error response


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error response")
val result = json_error("Not found", 404)
expect result.contains("\"status\"")
expect result.contains("\"error\"")
expect result.contains("\"code\"")
expect result.contains("404")
```

</details>

#### creates data response

- creates data response


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates data response")
val data = json_object([("id", json_number(1))])
val result = json_data(data)
expect result.contains("\"status\"")
expect result.contains("\"data\"")
```

</details>

### Validation

#### detects JSON object

- detects JSON object


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects JSON object")
val json_obj = '{"key": "value"}'
expect looks_like_json(json_obj)
expect not looks_like_json("not json")
```

</details>

#### detects JSON array

- detects JSON array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects JSON array")
expect looks_like_json("[1, 2, 3]")
expect not looks_like_json("plain text")
```

</details>

#### handles empty string

- handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
expect not looks_like_json("")
```

</details>

#### validates balanced braces

- validates balanced braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates balanced braces")
val balanced = '{"a": [1, 2]}'
expect has_balanced_braces(balanced)
```

</details>

#### detects unbalanced braces

- detects unbalanced braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects unbalanced braces")
val unbalanced1 = '{"a": [1, 2}'
val unbalanced2 = '{"a": 1]]'
expect not has_balanced_braces(unbalanced1)
expect not has_balanced_braces(unbalanced2)
```

</details>

### Common Patterns

#### creates API response with data

- creates API response with data


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates API response with data")
val data = json_string("result")
val result = api_response(true, "Success", Some(data))
expect result.contains("\"success\"")
expect result.contains("true")
expect result.contains("\"data\"")
```

</details>

#### creates API response without data

- creates API response without data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates API response without data")
val result = api_response(false, "Failed", nil)
expect result.contains("\"success\"")
expect result.contains("false")
expect result.contains("null")
```

</details>

#### creates pagination meta

- creates pagination meta


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates pagination meta")
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

- creates timestamp JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates timestamp JSON")
val result = timestamp_json(unix=1640000000, iso="2021-12-20T12:00:00Z")
expect result.contains("\"unix\"")
expect result.contains("1640000000")
expect result.contains("\"iso\"")
expect result.contains("2021-12-20")
```

</details>

### Edge Cases

#### escapes backslash in string

- escapes backslash in string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes backslash in string")
val result = json_string("path\\to\\file")
expect result.contains("\\\\")
```

</details>

#### formats empty object

- formats empty object


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats empty object")
val result = json_object([])
expect result == r"{}"
```

</details>

#### formats empty array

- formats empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats empty array")
val result = json_array([])
expect result == "[]"
```

</details>

#### handles nested objects

- handles nested objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested objects")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/json_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JSON Utilities, JSON Value Formatting, JSON Arrays, JSON Objects, JSON Builder, JSON Array Builder, Common Structures, Validation, Common Patterns, Edge Cases.
- JSON Utilities
- JSON Value Formatting
- JSON Arrays
- JSON Objects
- JSON Builder
- JSON Array Builder
- Common Structures
- Validation
- Common Patterns
- Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `9e14f4004264eaa097e59daf25ae08371a3258a4c09a4c5ae66344f2a23c9645`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e14f4004264eaa097e59daf25ae08371a3258a4c09a4c5ae66344f2a23c9645`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e14f4004264eaa097e59daf25ae08371a3258a4c09a4c5ae66344f2a23c9645`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/json_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/json_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/json_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/json_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/json_utils_spec.spl:226:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/json_utils_spec.spl:231:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes quotes in string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/json_utils_spec.spl:237:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes newlines in string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
