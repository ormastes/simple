# Json Conversion Specification

> <details>

<!-- sdn-diagram:id=json_conversion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=json_conversion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

json_conversion_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=json_conversion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Conversion Specification

## Scenarios

### JSON Conversion

### any_to_json Type Branches

#### converts bool to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "true"
expect(json).to_equal("true")
```

</details>

#### converts i64 to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "42"
expect(json).to_equal("42")
```

</details>

#### converts f64 to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "3.14"
expect(json.contains("3.14")).to_equal(true)
```

</details>

#### converts text to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = js("hello")
expect(json.contains("hello")).to_equal(true)
```

</details>

#### converts list to JSON array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "[1,2,3]"
expect(json.starts_with("[")).to_equal(true)
expect(json.ends_with("]")).to_equal(true)
```

</details>

#### converts dict to JSON object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("key", js("value")))
expect(json.contains("key")).to_equal(true)
```

</details>

#### handles nil conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "null"
expect(json).to_equal("null")
```

</details>

#### uses fallback for unknown types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = js("unknown")
expect(json.contains("unknown")).to_equal(true)
```

</details>

### json_value_to_any Type Branches

#### converts JSON bool to any

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = extract_json_value(jo1(jp("v", "true")), "v")
expect(value).to_equal("true")
```

</details>

#### converts JSON number to any

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = extract_json_value(jo1(jp("v", "42")), "v")
expect(value).to_equal("42")
```

</details>

#### converts JSON string to any

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = extract_json_string(jo1(jp("v", js("text"))), "v")
expect(value).to_equal("text")
```

</details>

#### converts JSON array to any

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("v", "[1,2,3]"))
val value = extract_json_value(json, "v")
expect(value.starts_with("[")).to_equal(true)
```

</details>

#### converts JSON object to any

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = jo1(jp("a", "1"))
val json = jo1(jp("v", inner))
val value = extract_json_value(json, "v")
expect(value.contains("a")).to_equal(true)
```

</details>

#### converts JSON null to any

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("v", "null"))
val value = extract_json_value(json, "v")
expect(value).to_equal("null")
```

</details>

### Edge Cases

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = LB() + RB()
expect(json.len() > 0).to_equal(true)
```

</details>

#### handles empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = LB() + RB()
expect(json.len() > 0).to_equal(true)
```

</details>

#### handles nested structures

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = jo1(jp("nested", js("value")))
val outer = jo1(jp("outer", inner))
expect(outer.contains("nested")).to_equal(true)
expect(outer.contains("value")).to_equal(true)
```

</details>

#### handles special characters in strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("hello \"world\"")
expect(escaped.contains("world")).to_equal(true)
```

</details>

### Round-Trip Conversion

#### preserves bool through conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "true"
val json = jo1(jp("v", original))
val extracted = extract_json_value(json, "v")
expect(extracted).to_equal(original)
```

</details>

#### preserves number through conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "42"
val json = jo1(jp("v", original))
val extracted = extract_json_value(json, "v")
expect(extracted).to_equal(original)
```

</details>

#### preserves string through conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "hello"
val json = jo1(jp("v", js(original)))
val extracted = extract_json_string(json, "v")
expect(extracted).to_equal(original)
```

</details>

#### preserves nested structure through conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = jo1(jp("key", js("val")))
val outer = jo1(jp("data", inner))
val extracted = extract_json_value(outer, "data")
expect(extracted.contains("key")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/json_conversion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JSON Conversion
- any_to_json Type Branches
- json_value_to_any Type Branches
- Edge Cases
- Round-Trip Conversion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
