# Json Logic Specification

> <details>

<!-- sdn-diagram:id=json_logic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=json_logic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

json_logic_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=json_logic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Logic Specification

## Scenarios

### JSON Library Logic

### parser strictness

#### parses nested object and array values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = json_parse("{\"user\":{\"name\":\"Ada\",\"scores\":[1,2]}}")
expect(json_is_object(parsed)).to_equal(true)
expect(json_to_string(json_path_get(parsed, "user.name"))).to_equal("Ada")
expect(json_to_number(json_path_get(parsed, "user.scores.1"))).to_equal(2)
```

</details>

#### rejects trailing tokens after a valid value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = json_parse("{\"ok\":true} []")
expect(parsed).to_be_nil()

val result = json_parse_with_error("{\"ok\":true} []")
expect(result.0).to_be_nil()
expect(result.1).to_contain("trailing")
```

</details>

#### rejects trailing commas in objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = json_parse("{\"ok\":true,}")
expect(parsed).to_be_nil()

val result = json_parse_with_error("{\"ok\":true,}")
expect(result.0).to_be_nil()
expect(result.1).to_contain("Trailing comma")
```

</details>

#### rejects trailing commas in arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = json_parse("[1,2,]")
expect(parsed).to_be_nil()

val result = json_parse_with_error("[1,2,]")
expect(result.0).to_be_nil()
expect(result.1).to_contain("Unexpected token")
```

</details>

#### reports unterminated strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = json_parse_with_error("{\"name\":\"Ada}")
expect(result.0).to_be_nil()
expect(result.1).to_contain("Unterminated string")
```

</details>

#### decodes escaped slash and control escapes in strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = json_parse("{\"path\":\"https:\\/\\/example.com\\b\\f\"}")
expect(json_to_string(json_path_get(parsed, "path"))).to_equal("https://example.com\b\f")
```

</details>

#### keeps invalid trailing input unchanged during minify and beautify

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "{\"ok\":true} garbage"
expect(json_minify(input)).to_equal(input)
expect(json_beautify(input)).to_equal(input)
```

</details>

### path write semantics

#### creates missing nested objects for dotted paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = json_path_set(json_object({}), "user.profile.name", json_string("Ada"))
expect(json_is_object(json_object_get(updated, "user"))).to_equal(true)
expect(json_to_string(json_path_get(updated, "user.profile.name"))).to_equal("Ada")
```

</details>

#### preserves existing siblings when writing nested paths

1. "id": json number
   - Expected: json_to_number(json_path_get(updated, "user.id")) equals `7`
   - Expected: json_to_string(json_path_get(updated, "user.profile.name")) equals `Ada`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = json_object({
    "user": json_object({
        "id": json_number(7)
    })
})
val updated = json_path_set(original, "user.profile.name", json_string("Ada"))
expect(json_to_number(json_path_get(updated, "user.id"))).to_equal(7)
expect(json_to_string(json_path_get(updated, "user.profile.name"))).to_equal("Ada")
```

</details>

### unflatten behavior

#### builds nested objects from dotted keys

1. "user name": json string
2. "user age": json number
   - Expected: json_to_string(json_path_get(nested, "user.name")) equals `Ada`
   - Expected: json_to_number(json_path_get(nested, "user.age")) equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flat = json_object({
    "user.name": json_string("Ada"),
    "user.age": json_number(37)
})
val nested = json_unflatten_object(flat)
expect(json_to_string(json_path_get(nested, "user.name"))).to_equal("Ada")
expect(json_to_number(json_path_get(nested, "user.age"))).to_equal(37)
```

</details>

### diff and patch behavior

#### applies object diffs back to the original object

1. "name": json string
2. "age": json number
3. "tags": json array
4. "name": json string
5. "age": json number
6. "tags": json array
7. "active": json string
   - Expected: json_deep_equals(patched, updated) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = json_object({
    "user": json_object({
        "name": json_string("Ada"),
        "age": json_number(36)
    }),
    "tags": json_array([json_string("core")])
})
val updated = json_object({
    "user": json_object({
        "name": json_string("Ada"),
        "age": json_number(37)
    }),
    "tags": json_array([json_string("core")]),
    "active": json_string("yes")
})

val diff = json_diff(original, updated)
val patched = json_patch(original, diff)

expect(json_deep_equals(patched, updated)).to_equal(true)
```

</details>

### builder escaping

#### escapes object keys as well as values

1.  field
2.  build
   - Expected: built equals `{"say\\"hi": "line\\nbreak"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val built = JsonBuilder.object()
    .field("say\"hi", "line\nbreak")
    .build()

expect(built).to_equal("{\"say\\\"hi\": \"line\\nbreak\"}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/json_logic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JSON Library Logic
- parser strictness
- path write semantics
- unflatten behavior
- diff and patch behavior
- builder escaping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
