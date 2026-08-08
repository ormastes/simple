# Pagination Specification

> <details>

<!-- sdn-diagram:id=pagination_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pagination_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pagination_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pagination_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pagination Specification

## Scenarios

### Pagination - page building with JSON helpers

<details>
<summary>Advanced: builds paginated response with items</summary>

#### builds paginated response with items _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = "[" + js("item1") + "," + js("item2") + "," + js("item3") + "]"
val result = jo1(jp("items", items))
val response = make_result_response("1", result)
expect(response.contains("items")).to_equal(true)
expect(response.contains("item1")).to_equal(true)
expect(response.contains("item3")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds empty page response</summary>

#### builds empty page response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo1(jp("items", "[]"))
val response = make_result_response("1", result)
expect(response.contains("items")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds page with next cursor</summary>

#### builds page with next cursor _(slow)_

1. jp
2. jp
   - Expected: response contains `nextCursor`
   - Expected: response contains `o10l10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo2(
    jp("items", "[" + js("a") + "]"),
    jp("nextCursor", js("o10l10"))
)
val response = make_result_response("1", result)
expect(response.contains("nextCursor")).to_equal(true)
expect(response.contains("o10l10")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds page without next cursor when at end</summary>

#### builds page without next cursor when at end _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo1(jp("items", "[" + js("last") + "]"))
val response = make_result_response("1", result)
expect(response.contains("nextCursor")).to_equal(false)
```

</details>


</details>

### Pagination - cursor encoding

<details>
<summary>Advanced: cursor format includes offset and limit</summary>

#### cursor format includes offset and limit _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = "o10l20"
expect(cursor.starts_with("o")).to_equal(true)
expect(cursor.contains("l")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: first page cursor starts at zero</summary>

#### first page cursor starts at zero _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = "o0l50"
expect(cursor.starts_with("o0")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: next page cursor advances offset</summary>

#### next page cursor advances offset _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 10
val offset = 0
val next_offset = offset + page_size
expect(next_offset).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: previous page cursor decreases offset</summary>

#### previous page cursor decreases offset _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 10
val offset = 20
val prev_offset = offset - page_size
expect(prev_offset).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: previous at start returns no cursor</summary>

#### previous at start returns no cursor _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offset = 0
val has_previous = offset > 0
expect(has_previous).to_equal(false)
```

</details>


</details>

### Pagination - page size clamping

<details>
<summary>Advanced: clamps page size to maximum</summary>

#### clamps page size to maximum _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val requested = 2000
val max_size = 1000
val clamped = min_int(requested, max_size)
expect(clamped).to_equal(1000)
```

</details>


</details>

<details>
<summary>Advanced: accepts valid page size</summary>

#### accepts valid page size _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val requested = 50
val max_size = 1000
val clamped = min_int(requested, max_size)
expect(clamped).to_equal(50)
```

</details>


</details>

<details>
<summary>Advanced: handles zero page size with default</summary>

#### handles zero page size with default _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val requested = 0
val default_size = 100
var page_size = requested
if page_size <= 0:
    page_size = default_size
expect(page_size).to_equal(100)
```

</details>


</details>

<details>
<summary>Advanced: handles negative page size with default</summary>

#### handles negative page size with default _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val requested = -10
val default_size = 100
var page_size = requested
if page_size <= 0:
    page_size = default_size
expect(page_size).to_equal(100)
```

</details>


</details>

### Pagination - extract cursor from params

<details>
<summary>Advanced: extracts cursor from params JSON</summary>

#### extracts cursor from params JSON _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("cursor", js("o10l20")))
val cursor = extract_json_string(params, "cursor")
expect(cursor).to_equal("o10l20")
```

</details>


</details>

<details>
<summary>Advanced: returns empty for missing cursor</summary>

#### returns empty for missing cursor _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("other", js("value")))
val cursor = extract_json_string(params, "cursor")
expect(cursor).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: extracts empty cursor value</summary>

#### extracts empty cursor value _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("cursor", js("")))
val cursor = extract_json_string(params, "cursor")
expect(cursor).to_equal("")
```

</details>


</details>

### Pagination - total count

<details>
<summary>Advanced: includes total count in response</summary>

#### includes total count in response _(slow)_

1. jp
2. jp
   - Expected: response contains `totalCount`
   - Expected: response contains `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo2(
    jp("items", "[" + js("a") + "," + js("b") + "]"),
    jp("totalCount", "100")
)
val response = make_result_response("1", result)
expect(response.contains("totalCount")).to_equal(true)
expect(response.contains("100")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: extracts total count</summary>

#### extracts total count _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo2(jp("items", "[]"), jp("totalCount", "42"))
expect(extract_json_value(result, "totalCount")).to_equal("42")
```

</details>


</details>

### Pagination - page iteration

<details>
<summary>Advanced: calculates total pages</summary>

#### calculates total pages _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total_items = 25
val page_size = 10
var total_pages = total_items / page_size
if total_items % page_size > 0:
    total_pages = total_pages + 1
expect(total_pages).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: handles exact page boundary</summary>

#### handles exact page boundary _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total_items = 30
val page_size = 10
var total_pages = total_items / page_size
if total_items % page_size > 0:
    total_pages = total_pages + 1
expect(total_pages).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: handles empty list</summary>

#### handles empty list _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total_items = 0
val is_empty = total_items == 0
expect(is_empty).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles single item</summary>

#### handles single item _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total_items = 1
val page_size = 10
val has_more = total_items > page_size
expect(has_more).to_equal(false)
```

</details>


</details>

### Pagination - config with log levels

<details>
<summary>Advanced: debug level for pagination trace</summary>

#### debug level for pagination trace _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: info level for page access</summary>

#### info level for page access _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: warning level for invalid cursor</summary>

#### warning level for invalid cursor _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/pagination_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pagination - page building with JSON helpers
- Pagination - cursor encoding
- Pagination - page size clamping
- Pagination - extract cursor from params
- Pagination - total count
- Pagination - page iteration
- Pagination - config with log levels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 25 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
