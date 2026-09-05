# T32 MCP Server -- JSON & Protocol Tests

> Tests for the T32 MCP server JSON helpers: encoding, object builders, field extraction, and JSON-RPC / MCP protocol response builders. All functions under test are pure (no I/O, no side effects).

<!-- sdn-diagram:id=t32_mcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_mcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_mcp_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_mcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Server -- JSON & Protocol Tests

Tests for the T32 MCP server JSON helpers: encoding, object builders, field extraction, and JSON-RPC / MCP protocol response builders. All functions under test are pure (no I/O, no side effects).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-MCP-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/t32_tools/t32_mcp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the T32 MCP server JSON helpers: encoding, object builders,
field extraction, and JSON-RPC / MCP protocol response builders.
All functions under test are pure (no I/O, no side effects).

## Source

`examples/10_tooling/trace32_tools/t32_mcp/json_helpers.spl`

## Scenarios

### T32 MCP JSON Encoding

#### character helpers

#### returns double-quote char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_Q()).to_equal("\"")
```

</details>

#### returns left brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_LB()).to_equal("{")
```

</details>

#### returns right brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_RB()).to_equal("}")
```

</details>

#### escape_json

#### escapes double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_escape_json("he\"llo")
expect(result).to_contain("\\\"")
```

</details>

#### escapes backslashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_escape_json("a\\b")
expect(result).to_contain("\\\\")
```

</details>

#### escapes newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_escape_json("a\nb")
expect(result).to_contain("\\n")
```

</details>

#### escapes tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_escape_json("a\tb")
expect(result).to_contain("\\t")
```

</details>

#### leaves plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_escape_json("hello world")
expect(result).to_equal("hello world")
```

</details>

#### t32_js wraps string with quotes

#### wraps simple string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_js("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### wraps and escapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_js("a\"b")
expect(result).to_contain("\\\"")
```

</details>

#### t32_jp builds key-value pair

#### builds quoted key with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_jp("name", "\"Alice\"")
expect(result).to_equal("\"name\":\"Alice\"")
```

</details>

### T32 MCP JSON Object Builders

#### t32_jo1 builds 1-pair object

#### wraps single pair in braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = t32_jp("k", t32_js("v"))
val result = t32_jo1(pair)
expect(result).to_equal("{\"k\":\"v\"}")
```

</details>

#### t32_jo2 builds 2-pair object

#### joins two pairs with comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = t32_jp("a", t32_js("1"))
val p2 = t32_jp("b", t32_js("2"))
val result = t32_jo2(p1, p2)
expect(result).to_equal("{\"a\":\"1\",\"b\":\"2\"}")
```

</details>

#### t32_jo3 builds 3-pair object

#### joins three pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = t32_jp("x", "1")
val p2 = t32_jp("y", "2")
val p3 = t32_jp("z", "3")
val result = t32_jo3(p1, p2, p3)
expect(result).to_contain("\"x\":1")
expect(result).to_contain("\"y\":2")
expect(result).to_contain("\"z\":3")
```

</details>

#### t32_jo4 builds 4-pair object

#### joins four pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = t32_jp("a", "1")
val p2 = t32_jp("b", "2")
val p3 = t32_jp("c", "3")
val p4 = t32_jp("d", "4")
val result = t32_jo4(p1, p2, p3, p4)
expect(result).to_contain("\"a\":1")
expect(result).to_contain("\"d\":4")
```

</details>

### T32 MCP JSON Extraction

#### t32_extract_field

#### extracts string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"host\":\"localhost\",\"port\":20000}"
val result = t32_extract_field(json, "host")
expect(result).to_equal("localhost")
```

</details>

#### extracts numeric value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"host\":\"localhost\",\"port\":20000}"
val result = t32_extract_field(json, "port")
expect(result).to_equal("20000")
```

</details>

#### returns empty for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"host\":\"localhost\"}"
val result = t32_extract_field(json, "xxx")
expect(result).to_equal("")
```

</details>

#### t32_extract_field_raw

#### extracts raw quoted value with quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\":\"test\"}"
val result = t32_extract_field_raw(json, "name")
expect(result).to_start_with("\"")
```

</details>

#### extracts raw numeric value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"count\":42}"
val result = t32_extract_field_raw(json, "count")
expect(result).to_equal("42")
```

</details>

#### returns null for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"a\":1}"
val result = t32_extract_field_raw(json, "missing")
expect(result).to_equal("null")
```

</details>

#### t32_extract_id

#### extracts numeric id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"test\"}"
val result = t32_extract_id(json)
expect(result).to_equal("42")
```

</details>

#### extracts string id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"jsonrpc\":\"2.0\",\"id\":\"abc\",\"method\":\"test\"}"
val result = t32_extract_id(json)
expect(result).to_start_with("\"")
```

</details>

#### t32_extract_nested

#### extracts from params object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\":\"test\",\"params\":{\"name\":\"hello\",\"x\":1}}"
val result = t32_extract_nested(json, "name")
expect(result).to_equal("hello")
```

</details>

#### returns empty when params missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\":\"test\"}"
val result = t32_extract_nested(json, "name")
expect(result).to_equal("")
```

</details>

### T32 MCP Protocol Responses

#### JSON-RPC result builders

#### builds success response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_make_json_result("1", "{\"ok\":true}")
expect(result).to_contain("\"jsonrpc\":\"2.0\"")
expect(result).to_contain("\"id\":1")
expect(result).to_contain("\"result\":")
```

</details>

#### builds error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_make_error("1", -32601, "Method not found")
expect(result).to_contain("\"jsonrpc\":\"2.0\"")
expect(result).to_contain("\"error\":")
expect(result).to_contain("\"code\":-32601")
expect(result).to_contain("Method not found")
```

</details>

#### MCP tool result builders

#### builds tool result with content array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_make_tool_result("1", "hello world")
expect(result).to_contain("\"type\":\"text\"")
expect(result).to_contain("\"content\":")
expect(result).to_contain("hello world")
```

</details>

#### builds tool error with isError flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_make_tool_error("1", 500, "Something broke")
expect(result).to_contain("\"isError\":true")
expect(result).to_contain("Something broke")
```

</details>

### T32 MCP Protocol — New Tools

#### t32_setup_headless schema

#### includes area_name and semihost parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = t32_make_tool_schema("t32_setup_headless", "Headless setup")
expect(schema).to_contain("area_name")
expect(schema).to_contain("semihost")
expect(schema).to_contain("error_handler")
expect(schema).to_contain("t32_setup_headless")
```

</details>

#### t32_area_read schema

#### includes area_name and clear parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = t32_make_tool_schema("t32_area_read", "Read AREA")
expect(schema).to_contain("area_name")
expect(schema).to_contain("clear")
expect(schema).to_contain("t32_area_read")
```

</details>

#### t32_cmm_commands schema

#### includes group and search parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = t32_make_tool_schema("t32_cmm_commands", "CMM commands")
expect(schema).to_contain("group")
expect(schema).to_contain("search")
expect(schema).to_contain("t32_cmm_commands")
```

</details>

#### t32_cmm_run schema updated

#### includes capture_area parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = t32_make_tool_schema("t32_cmm_run", "Run CMM")
expect(schema).to_contain("capture_area")
expect(schema).to_contain("script")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
