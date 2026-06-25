# Mcp Elicitation Specification

> <details>

<!-- sdn-diagram:id=mcp_elicitation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_elicitation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_elicitation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_elicitation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Elicitation Specification

## Scenarios

### MCP Elicitation Create

#### when building elicitation request

#### uses correct method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = jo1(jp("type", js("object")))
val req = make_elicitation_request("srv-1", "Please enter your API key", schema)
expect(req.contains("\"method\":\"elicitation/create\"")).to_equal(true)
```

</details>

#### includes message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = jo1(jp("type", js("object")))
val req = make_elicitation_request("srv-1", "Please enter your API key", schema)
expect(req.contains("Please enter your API key")).to_equal(true)
```

</details>

#### includes requestedSchema

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = jo2(jp("type", js("object")), jp("properties", jo1(jp("key", jo1(jp("type", js("string")))))))
val req = make_elicitation_request("srv-1", "Enter key", schema)
expect(req.contains("requestedSchema")).to_equal(true)
```

</details>

#### is a request (has id)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = jo1(jp("type", js("object")))
val req = make_elicitation_request("srv-1", "Enter", schema)
expect(req.contains("\"id\":srv-1")).to_equal(true)
```

</details>

#### is valid JSON-RPC

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = jo1(jp("type", js("object")))
val req = make_elicitation_request("srv-1", "test", schema)
expect(req.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP Elicitation Schema Types

#### when using string schema

#### supports basic string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prop = jo1(jp("type", js("string")))
val schema = jo2(jp("type", js("object")), jp("properties", jo1(jp("name", prop))))
val req = make_elicitation_request("1", "Name?", schema)
expect(req.contains("string")).to_equal(true)
```

</details>

#### supports minLength/maxLength constraints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prop = jo3(jp("type", js("string")), jp("minLength", "1"), jp("maxLength", "255"))
expect(prop.contains("minLength")).to_equal(true)
expect(prop.contains("maxLength")).to_equal(true)
```

</details>

#### when using numeric schema

#### supports number type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prop = jo1(jp("type", js("number")))
expect(prop.contains("number")).to_equal(true)
```

</details>

#### supports integer type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prop = jo1(jp("type", js("integer")))
expect(prop.contains("integer")).to_equal(true)
```

</details>

#### supports minimum/maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prop = jo3(jp("type", js("integer")), jp("minimum", "0"), jp("maximum", "100"))
expect(prop.contains("minimum")).to_equal(true)
expect(prop.contains("maximum")).to_equal(true)
```

</details>

#### when using boolean schema

#### supports boolean type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prop = jo1(jp("type", js("boolean")))
expect(prop.contains("boolean")).to_equal(true)
```

</details>

#### when using enum schema

#### supports string enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = "[" + js("option1") + "," + js("option2") + "," + js("option3") + "]"
val prop = jo2(jp("type", js("string")), jp("enum", values))
expect(prop.contains("enum")).to_equal(true)
expect(prop.contains("option1")).to_equal(true)
```

</details>

### MCP Elicitation Response

#### when user accepts

#### action is accept in response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = jo2(jp("action", js("accept")), jp("content", jo1(jp("key", js("abc123")))))
val action = extract_json_string(response, "action")
expect(action).to_equal("accept")
```

</details>

#### includes content in accept response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = jo2(jp("action", js("accept")), jp("content", jo1(jp("key", js("abc123")))))
expect(response.contains("content")).to_equal(true)
expect(response.contains("abc123")).to_equal(true)
```

</details>

#### when user declines

#### action is decline in response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = jo1(jp("action", js("decline")))
val action = extract_json_string(response, "action")
expect(action).to_equal("decline")
```

</details>

#### when user cancels

#### action is cancel in response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = jo1(jp("action", js("cancel")))
val action = extract_json_string(response, "action")
expect(action).to_equal("cancel")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_elicitation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Elicitation Create
- MCP Elicitation Schema Types
- MCP Elicitation Response

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
