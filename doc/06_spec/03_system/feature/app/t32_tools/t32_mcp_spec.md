# T32 MCP Server -- JSON & Protocol Tests

> Tests for the T32 MCP server JSON helpers: encoding, object builders, field extraction, and JSON-RPC / MCP protocol response builders. All functions under test are pure (no I/O, no side effects).

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
| Updated | 2026-08-26 |
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

- returns double-quote char
   - Expected: t32_Q() equals `"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns double-quote char")
expect(t32_Q()).to_equal("\"")
```

</details>

#### returns left brace

- returns left brace
   - Expected: t32_LB() equals `{`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns left brace")
expect(t32_LB()).to_equal("{")
```

</details>

#### returns right brace

- returns right brace
   - Expected: t32_RB() equals `}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns right brace")
expect(t32_RB()).to_equal("}")
```

</details>

#### escape_json

#### escapes double quotes

- escapes double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes double quotes")
val result = t32_escape_json("he\"llo")
expect(result).to_contain("\\\"")
```

</details>

#### escapes backslashes

- escapes backslashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes backslashes")
val result = t32_escape_json("a\\b")
expect(result).to_contain("\\\\")
```

</details>

#### escapes newlines

- escapes newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes newlines")
val result = t32_escape_json("a\nb")
expect(result).to_contain("\\n")
```

</details>

#### escapes tabs

- escapes tabs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes tabs")
val result = t32_escape_json("a\tb")
expect(result).to_contain("\\t")
```

</details>

#### leaves plain text unchanged

- leaves plain text unchanged
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves plain text unchanged")
val result = t32_escape_json("hello world")
expect(result).to_equal("hello world")
```

</details>

#### t32_js wraps string with quotes

#### wraps simple string

- wraps simple string
   - Expected: result equals `"hello"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps simple string")
val result = t32_js("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### wraps and escapes

- wraps and escapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps and escapes")
val result = t32_js("a\"b")
expect(result).to_contain("\\\"")
```

</details>

#### t32_jp builds key-value pair

#### builds quoted key with value

- builds quoted key with value
   - Expected: result equals `"name":"Alice"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds quoted key with value")
val result = t32_jp("name", "\"Alice\"")
expect(result).to_equal("\"name\":\"Alice\"")
```

</details>

### T32 MCP JSON Object Builders

#### t32_jo1 builds 1-pair object

#### wraps single pair in braces

- wraps single pair in braces
   - Expected: result equals `{"k":"v"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps single pair in braces")
val pair = t32_jp("k", t32_js("v"))
val result = t32_jo1(pair)
expect(result).to_equal("{\"k\":\"v\"}")
```

</details>

#### t32_jo2 builds 2-pair object

#### joins two pairs with comma

- joins two pairs with comma
   - Expected: result equals `{"a":"1","b":"2"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("joins two pairs with comma")
val p1 = t32_jp("a", t32_js("1"))
val p2 = t32_jp("b", t32_js("2"))
val result = t32_jo2(p1, p2)
expect(result).to_equal("{\"a\":\"1\",\"b\":\"2\"}")
```

</details>

#### t32_jo3 builds 3-pair object

#### joins three pairs

- joins three pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("joins three pairs")
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

- joins four pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("joins four pairs")
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

- extracts string value
   - Expected: result equals `localhost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts string value")
val json = "{\"host\":\"localhost\",\"port\":20000}"
val result = t32_extract_field(json, "host")
expect(result).to_equal("localhost")
```

</details>

#### extracts numeric value

- extracts numeric value
   - Expected: result equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts numeric value")
val json = "{\"host\":\"localhost\",\"port\":20000}"
val result = t32_extract_field(json, "port")
expect(result).to_equal("20000")
```

</details>

#### returns empty for missing key

- returns empty for missing key
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty for missing key")
val json = "{\"host\":\"localhost\"}"
val result = t32_extract_field(json, "xxx")
expect(result).to_equal("")
```

</details>

#### t32_extract_field_raw

#### extracts raw quoted value with quotes

- extracts raw quoted value with quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts raw quoted value with quotes")
val json = "{\"name\":\"test\"}"
val result = t32_extract_field_raw(json, "name")
expect(result).to_start_with("\"")
```

</details>

#### extracts raw numeric value

- extracts raw numeric value
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts raw numeric value")
val json = "{\"count\":42}"
val result = t32_extract_field_raw(json, "count")
expect(result).to_equal("42")
```

</details>

#### returns null for missing key

- returns null for missing key
   - Expected: result equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns null for missing key")
val json = "{\"a\":1}"
val result = t32_extract_field_raw(json, "missing")
expect(result).to_equal("null")
```

</details>

#### t32_extract_id

#### extracts numeric id

- extracts numeric id
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts numeric id")
val json = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"test\"}"
val result = t32_extract_id(json)
expect(result).to_equal("42")
```

</details>

#### extracts string id

- extracts string id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts string id")
val json = "{\"jsonrpc\":\"2.0\",\"id\":\"abc\",\"method\":\"test\"}"
val result = t32_extract_id(json)
expect(result).to_start_with("\"")
```

</details>

#### t32_extract_nested

#### extracts from params object

- extracts from params object
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts from params object")
val json = "{\"method\":\"test\",\"params\":{\"name\":\"hello\",\"x\":1}}"
val result = t32_extract_nested(json, "name")
expect(result).to_equal("hello")
```

</details>

#### returns empty when params missing

- returns empty when params missing
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty when params missing")
val json = "{\"method\":\"test\"}"
val result = t32_extract_nested(json, "name")
expect(result).to_equal("")
```

</details>

### T32 MCP Protocol Responses

#### JSON-RPC result builders

#### builds success response

- builds success response


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds success response")
val result = t32_make_json_result("1", "{\"ok\":true}")
expect(result).to_contain("\"jsonrpc\":\"2.0\"")
expect(result).to_contain("\"id\":1")
expect(result).to_contain("\"result\":")
```

</details>

#### builds error response

- builds error response


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds error response")
val result = t32_make_error("1", -32601, "Method not found")
expect(result).to_contain("\"jsonrpc\":\"2.0\"")
expect(result).to_contain("\"error\":")
expect(result).to_contain("\"code\":-32601")
expect(result).to_contain("Method not found")
```

</details>

#### MCP tool result builders

#### builds tool result with content array

- builds tool result with content array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds tool result with content array")
val result = t32_make_tool_result("1", "hello world")
expect(result).to_contain("\"type\":\"text\"")
expect(result).to_contain("\"content\":")
expect(result).to_contain("hello world")
```

</details>

#### builds tool error with isError flag

- builds tool error with isError flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds tool error with isError flag")
val result = t32_make_tool_error("1", 500, "Something broke")
expect(result).to_contain("\"isError\":true")
expect(result).to_contain("Something broke")
```

</details>

### T32 MCP Protocol — New Tools

#### t32_setup_headless schema

#### includes area_name and semihost parameters

- includes area_name and semihost parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes area_name and semihost parameters")
val schema = t32_make_tool_schema("t32_setup_headless", "Headless setup")
expect(schema).to_contain("area_name")
expect(schema).to_contain("semihost")
expect(schema).to_contain("error_handler")
expect(schema).to_contain("t32_setup_headless")
```

</details>

#### t32_area_read schema

#### includes area_name and clear parameters

- includes area_name and clear parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes area_name and clear parameters")
val schema = t32_make_tool_schema("t32_area_read", "Read AREA")
expect(schema).to_contain("area_name")
expect(schema).to_contain("clear")
expect(schema).to_contain("t32_area_read")
```

</details>

#### t32_cmm_commands schema

#### includes group and search parameters

- includes group and search parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes group and search parameters")
val schema = t32_make_tool_schema("t32_cmm_commands", "CMM commands")
expect(schema).to_contain("group")
expect(schema).to_contain("search")
expect(schema).to_contain("t32_cmm_commands")
```

</details>

#### t32_cmm_run schema updated

#### includes capture_area parameter

- includes capture_area parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes capture_area parameter")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `737d3ed8c4094d484f822e3d30031c85540ded9336f756f69443c7c2a9008756`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `737d3ed8c4094d484f822e3d30031c85540ded9336f756f69443c7c2a9008756`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `737d3ed8c4094d484f822e3d30031c85540ded9336f756f69443c7c2a9008756`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/app/t32_tools/t32_mcp_spec.spl
mirror: doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/t32_tools/t32_mcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/t32_tools/t32_mcp_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns double-quote char' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/t32_tools/t32_mcp_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns left brace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/t32_tools/t32_mcp_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns right brace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
