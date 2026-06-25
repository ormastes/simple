# MCP Library Helpers

> Tests the MCP library helper functions including JSON-RPC message construction, parameter validation, and response formatting. Verifies that helper utilities correctly build well-formed protocol messages for MCP communication.

<!-- sdn-diagram:id=helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helpers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Library Helpers

Tests the MCP library helper functions including JSON-RPC message construction, parameter validation, and response formatting. Verifies that helper utilities correctly build well-formed protocol messages for MCP communication.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/03_system/feature/lib/mcp/helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP library helper functions including JSON-RPC message construction,
parameter validation, and response formatting. Verifies that helper utilities
correctly build well-formed protocol messages for MCP communication.

## Scenarios

### MCP Library - Helpers

#### provides brace helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LB()).to_equal("{")
expect(RB()).to_equal("}")
expect(Q()).to_equal("\"")
```

</details>

#### parses integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_int("123")).to_equal(123)
expect(parse_int("0")).to_equal(0)
expect(parse_int("999")).to_equal(999)
```

</details>

#### calculates minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_int(5, 10)).to_equal(5)
expect(min_int(10, 5)).to_equal(5)
expect(min_int(7, 7)).to_equal(7)
```

</details>

#### builds JSON pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(jp("key", "value")).to_equal("\"key\":value")
expect(js("text")).to_equal("\"text\"")
```

</details>

#### builds JSON objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = jo2(jp("a", "1"), jp("b", "2"))
expect(obj).to_equal("{\"a\":1,\"b\":2}")
```

</details>

#### extracts JSON strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\":\"initialize\",\"id\":1}"
expect(extract_json_string_v2(json, "method")).to_equal("initialize")
```

</details>

#### extracts JSON values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"id\":42,\"name\":\"test\"}"
expect(extract_json_value(json, "id")).to_equal("42")
```

</details>

#### creates result responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", "{\"status\":\"ok\"}")
expect(response).to_contain("\"jsonrpc\":\"2.0\"")
expect(response).to_contain("\"id\":1")
expect(response).to_contain("\"result\":{\"status\":\"ok\"}")
```

</details>

#### creates error responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("2", -32600, "Invalid request")
expect(response).to_contain("\"jsonrpc\":\"2.0\"")
expect(response).to_contain("\"id\":2")
expect(response).to_contain("\"error\"")
expect(response).to_contain("-32600")
```

</details>

#### creates tool results

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_tool_result("42", "Output text")
expect(result).to_contain("\"jsonrpc\":\"2.0\"")
expect(result).to_contain("\"id\":42")
expect(result).to_contain("\"type\":\"text\"")
expect(result).to_contain("\"text\":\"Output text\"")
```

</details>

#### extracts arguments from request body

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "{\"params\":{\"arguments\":{\"path\":\"test.spl\",\"name\":\"value\"}}}"
val path = extract_arg(body, "path")
val name = extract_arg(body, "name")
expect(path).to_equal("test.spl")
expect(name).to_equal("value")
```

</details>

#### returns empty string for missing arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "{\"params\":{\"arguments\":{\"path\":\"test.spl\"}}}"
val missing = extract_arg(body, "nonexistent")
expect(missing).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
