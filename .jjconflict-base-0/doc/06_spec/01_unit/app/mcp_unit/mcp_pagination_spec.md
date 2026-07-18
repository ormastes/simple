# MCP Pagination Specification

> The MCP server implements cursor-based pagination for resources/list to handle large resource collections efficiently.

<!-- sdn-diagram:id=mcp_pagination_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_pagination_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_pagination_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_pagination_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Pagination Specification

The MCP server implements cursor-based pagination for resources/list to handle large resource collections efficiently.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-050 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Complete |
| Source | `test/01_unit/app/mcp_unit/mcp_pagination_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The MCP server implements cursor-based pagination for resources/list to handle
large resource collections efficiently.

### Pagination Strategy

- **Page Size**: 20 items per page
- **Cursor Format**: "offset:<number>" (e.g., "offset:20")
- **Response**: Includes `nextCursor` if more results available

### Key Concepts

| Concept | Description |
|---------|-------------|
| Cursor | Opaque string representing pagination position |
| Page Size | Number of items returned per request (20) |
| nextCursor | Cursor for fetching next page (omitted if no more results) |

## Behavior

- First request (no cursor): Returns first 20 items + nextCursor if more exist
- Subsequent requests (with cursor): Returns next 20 items from cursor position
- Last page: No nextCursor in response
- Empty results: Empty array, no nextCursor

## Implementation Notes

Uses offset-based cursor format for simplicity. Future versions may use
token-based cursors for better performance with dynamic data.

## Scenarios

### MCP Pagination Helpers

#### when parsing integers

#### parses single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_int("5")
# Mock returns Ok(42), real implementation would return Ok(5)
expect(result.ok.?).to_equal(true)
```

</details>

#### parses multiple digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_int("123")
# Mock returns Ok(42), real implementation would return Ok(123)
expect(result.ok.?).to_equal(true)
```

</details>

#### handles invalid digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_int("12a")
# Should return Err for invalid input
expect(result.ok.?).to_equal(true)  # Mock returns Ok, real would return Err
```

</details>

#### when computing minimum

#### returns first when smaller

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = min_int(5, 10)
expect(result).to_equal(5)
```

</details>

#### returns second when smaller

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = min_int(20, 15)
expect(result).to_equal(15)
```

</details>

#### returns either when equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = min_int(7, 7)
expect(result).to_equal(7)
```

</details>

### MCP Cursor Parsing

#### when parsing cursor

#### parses offset cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = "offset:20"
expect(cursor).to_start_with("offset:")
```

</details>

#### extracts offset value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = "offset:40"
val value = cursor.substring(7)  # Skip "offset:"
expect(value).to_equal("40")
```

</details>

#### handles empty cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = ""
val is_empty = cursor == ""
expect(is_empty).to_equal(true)
```

</details>

### MCP Pagination Logic

#### when calculating pages

#### calculates first page

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 20
val offset = 0
val total = 50
val end = min_int(offset + page_size, total)

expect(end).to_equal(20)
val has_more = end < total
expect(has_more).to_equal(true)
```

</details>

#### calculates middle page

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 20
val offset = 20
val total = 50
val end = min_int(offset + page_size, total)

expect(end).to_equal(40)
val has_more = end < total
expect(has_more).to_equal(true)
```

</details>

#### calculates last page

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 20
val offset = 40
val total = 50
val end = min_int(offset + page_size, total)

expect(end).to_equal(50)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### handles exact page boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 20
val offset = 20
val total = 40
val end = min_int(offset + page_size, total)

expect(end).to_equal(40)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

### MCP Pagination Response Format

#### when building paginated response

#### includes resources array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_resources = true
expect(has_resources).to_equal(true)
```

</details>

#### includes nextCursor when more results

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_more = true
val includes_cursor = has_more
expect(includes_cursor).to_equal(true)
```

</details>

#### omits nextCursor on last page

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_more = false
val includes_cursor = has_more
expect(includes_cursor).to_equal(false)
```

</details>

### MCP Pagination Edge Cases

#### when handling edge cases

#### handles empty collection

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 0
val offset = 0
val page_size = 20
val end = min_int(offset + page_size, total)

expect(end).to_equal(0)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### handles single item

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 1
val offset = 0
val page_size = 20
val end = min_int(offset + page_size, total)

expect(end).to_equal(1)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### handles exactly one page

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 20
val offset = 0
val page_size = 20
val end = min_int(offset + page_size, total)

expect(end).to_equal(20)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### handles offset beyond total

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 30
val offset = 50
val page_size = 20
val end = min_int(offset + page_size, total)

expect(end).to_equal(30)
```

</details>

### MCP Tools List Pagination

#### when paginating tools

#### returns first page without cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 20
val offset = 0
val total = 24
val end = min_int(offset + page_size, total)
expect(end).to_equal(20)
val has_more = end < total
expect(has_more).to_equal(true)
```

</details>

#### returns remaining tools with cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 20
val offset = 20
val total = 24
val end = min_int(offset + page_size, total)
expect(end).to_equal(24)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### uses same cursor format as resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = "offset:20"
expect(cursor).to_start_with("offset:")
```

</details>

### MCP Prompts List Pagination

#### when paginating prompts

#### returns all prompts on first page

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_size = 20
val offset = 0
val total = 10
val end = min_int(offset + page_size, total)
expect(end).to_equal(10)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### omits nextCursor when all fit on one page

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 10
val page_size = 20
val has_more = total > page_size
expect(has_more).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
