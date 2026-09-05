# Mcp Elicitation Specification

> Tests covering MCP Elicitation Create, MCP Elicitation Schema Types, MCP Elicitation Response.

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

- uses correct method
   - Expected: req contains `"method":"elicitation/create"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses correct method")
val schema = jo1(jp("type", js("object")))
val req = make_elicitation_request("srv-1", "Please enter your API key", schema)
expect(req.contains("\"method\":\"elicitation/create\"")).to_equal(true)
```

</details>

#### includes message

- includes message
   - Expected: req contains `Please enter your API key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes message")
val schema = jo1(jp("type", js("object")))
val req = make_elicitation_request("srv-1", "Please enter your API key", schema)
expect(req.contains("Please enter your API key")).to_equal(true)
```

</details>

#### includes requestedSchema

- includes requestedSchema
   - Expected: req contains `requestedSchema`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes requestedSchema")
val schema = jo2(jp("type", js("object")), jp("properties", jo1(jp("key", jo1(jp("type", js("string")))))))
val req = make_elicitation_request("srv-1", "Enter key", schema)
expect(req.contains("requestedSchema")).to_equal(true)
```

</details>

#### is a request (has id)

- is a request (has id)
   - Expected: req contains `"id":srv-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a request (has id)")
val schema = jo1(jp("type", js("object")))
val req = make_elicitation_request("srv-1", "Enter", schema)
expect(req.contains("\"id\":srv-1")).to_equal(true)
```

</details>

#### is valid JSON-RPC

- is valid JSON-RPC
   - Expected: req contains `"jsonrpc":"2.0"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is valid JSON-RPC")
val schema = jo1(jp("type", js("object")))
val req = make_elicitation_request("srv-1", "test", schema)
expect(req.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP Elicitation Schema Types

#### when using string schema

#### supports basic string

- supports basic string
   - Expected: req contains `string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports basic string")
val prop = jo1(jp("type", js("string")))
val schema = jo2(jp("type", js("object")), jp("properties", jo1(jp("name", prop))))
val req = make_elicitation_request("1", "Name?", schema)
expect(req.contains("string")).to_equal(true)
```

</details>

#### supports minLength/maxLength constraints

- supports minLength/maxLength constraints
   - Expected: prop contains `minLength`
   - Expected: prop contains `maxLength`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports minLength/maxLength constraints")
val prop = jo3(jp("type", js("string")), jp("minLength", "1"), jp("maxLength", "255"))
expect(prop.contains("minLength")).to_equal(true)
expect(prop.contains("maxLength")).to_equal(true)
```

</details>

#### when using numeric schema

#### supports number type

- supports number type
   - Expected: prop contains `number`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports number type")
val prop = jo1(jp("type", js("number")))
expect(prop.contains("number")).to_equal(true)
```

</details>

#### supports integer type

- supports integer type
   - Expected: prop contains `integer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports integer type")
val prop = jo1(jp("type", js("integer")))
expect(prop.contains("integer")).to_equal(true)
```

</details>

#### supports minimum/maximum

- supports minimum/maximum
   - Expected: prop contains `minimum`
   - Expected: prop contains `maximum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports minimum/maximum")
val prop = jo3(jp("type", js("integer")), jp("minimum", "0"), jp("maximum", "100"))
expect(prop.contains("minimum")).to_equal(true)
expect(prop.contains("maximum")).to_equal(true)
```

</details>

#### when using boolean schema

#### supports boolean type

- supports boolean type
   - Expected: prop contains `boolean`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports boolean type")
val prop = jo1(jp("type", js("boolean")))
expect(prop.contains("boolean")).to_equal(true)
```

</details>

#### when using enum schema

#### supports string enum

- supports string enum
   - Expected: prop contains `enum`
   - Expected: prop contains `option1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports string enum")
val values = "[" + js("option1") + "," + js("option2") + "," + js("option3") + "]"
val prop = jo2(jp("type", js("string")), jp("enum", values))
expect(prop.contains("enum")).to_equal(true)
expect(prop.contains("option1")).to_equal(true)
```

</details>

### MCP Elicitation Response

#### when user accepts

#### action is accept in response

- action is accept in response
   - Expected: action equals `accept`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("action is accept in response")
val response = jo2(jp("action", js("accept")), jp("content", jo1(jp("key", js("abc123")))))
val action = extract_json_string(response, "action")
expect(action).to_equal("accept")
```

</details>

#### includes content in accept response

- includes content in accept response
   - Expected: response contains `content`
   - Expected: response contains `abc123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes content in accept response")
val response = jo2(jp("action", js("accept")), jp("content", jo1(jp("key", js("abc123")))))
expect(response.contains("content")).to_equal(true)
expect(response.contains("abc123")).to_equal(true)
```

</details>

#### when user declines

#### action is decline in response

- action is decline in response
   - Expected: action equals `decline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("action is decline in response")
val response = jo1(jp("action", js("decline")))
val action = extract_json_string(response, "action")
expect(action).to_equal("decline")
```

</details>

#### when user cancels

#### action is cancel in response

- action is cancel in response
   - Expected: action equals `cancel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("action is cancel in response")
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
| Source | `test/unit/app/mcp_unit/mcp_elicitation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Elicitation Create, MCP Elicitation Schema Types, MCP Elicitation Response.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `46b0ff2ba893a3cf7d2c68b179acce6b0b79f9c29cb86e5cd0ebbefb073ba2d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46b0ff2ba893a3cf7d2c68b179acce6b0b79f9c29cb86e5cd0ebbefb073ba2d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46b0ff2ba893a3cf7d2c68b179acce6b0b79f9c29cb86e5cd0ebbefb073ba2d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_elicitation_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_elicitation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_elicitation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_elicitation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_elicitation_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses correct method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_elicitation_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_elicitation_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes requestedSchema' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
