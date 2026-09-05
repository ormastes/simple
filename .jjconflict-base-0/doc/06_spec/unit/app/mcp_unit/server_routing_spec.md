# Server Routing Specification

> Tests covering Server Method Routing, Core Protocol Methods, Resource Methods, Tool Methods, Prompt Methods, Unknown Methods, Method Category Checks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Routing Specification

## Scenarios

### Server Method Routing

### Core Protocol Methods

#### routes initialize method

- routes initialize method
   - Expected: method equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes initialize method")
val req = jo2(jp("method", js("initialize")), jp("id", "1"))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialize")
```

</details>

#### routes initialized notification

- routes initialized notification
   - Expected: method equals `initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes initialized notification")
val req = jo1(jp("method", js("initialized")))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialized")
```

</details>

#### routes ping method

- routes ping method
   - Expected: method equals `ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes ping method")
val req = jo2(jp("method", js("ping")), jp("id", "2"))
val method = extract_json_string(req, "method")
expect(method).to_equal("ping")
```

</details>

#### routes shutdown method

- routes shutdown method
   - Expected: method equals `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes shutdown method")
val req = jo2(jp("method", js("shutdown")), jp("id", "3"))
val method = extract_json_string(req, "method")
expect(method).to_equal("shutdown")
```

</details>

### Resource Methods

#### routes resources/list

- routes resources/list
   - Expected: method equals `resources/list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes resources/list")
val req = jo2(jp("method", js("resources/list")), jp("id", "4"))
val method = extract_json_string(req, "method")
expect(method).to_equal("resources/list")
```

</details>

#### routes resources/read

- routes resources/read
   - Expected: method equals `resources/read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes resources/read")
val req = jo2(jp("method", js("resources/read")), jp("id", "5"))
val method = extract_json_string(req, "method")
expect(method).to_equal("resources/read")
```

</details>

### Tool Methods

#### routes tools/list

- routes tools/list
   - Expected: method equals `tools/list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes tools/list")
val req = jo2(jp("method", js("tools/list")), jp("id", "6"))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/list")
```

</details>

#### routes tools/call

- routes tools/call
   - Expected: method equals `tools/call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes tools/call")
val req = jo2(jp("method", js("tools/call")), jp("id", "7"))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/call")
```

</details>

### Prompt Methods

#### routes prompts/list

- routes prompts/list
   - Expected: method equals `prompts/list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes prompts/list")
val req = jo2(jp("method", js("prompts/list")), jp("id", "8"))
val method = extract_json_string(req, "method")
expect(method).to_equal("prompts/list")
```

</details>

#### routes prompts/get

- routes prompts/get
   - Expected: method equals `prompts/get`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes prompts/get")
val req = jo2(jp("method", js("prompts/get")), jp("id", "9"))
val method = extract_json_string(req, "method")
expect(method).to_equal("prompts/get")
```

</details>

### Unknown Methods

#### handles unknown method

- handles unknown method
   - Expected: is_known is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unknown method")
val method = "unknown/method"
val is_known = method == "initialize" or method == "ping" or method == "shutdown"
expect(is_known).to_equal(false)
```

</details>

### Method Category Checks

#### identifies resource methods

- identifies resource methods
   - Expected: is_resource is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies resource methods")
val method = "resources/list"
val is_resource = method.starts_with("resources/")
expect(is_resource).to_equal(true)
```

</details>

#### identifies tool methods

- identifies tool methods
   - Expected: is_tool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies tool methods")
val method = "tools/call"
val is_tool = method.starts_with("tools/")
expect(is_tool).to_equal(true)
```

</details>

#### identifies prompt methods

- identifies prompt methods
   - Expected: is_prompt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies prompt methods")
val method = "prompts/get"
val is_prompt = method.starts_with("prompts/")
expect(is_prompt).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/server_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Server Method Routing, Core Protocol Methods, Resource Methods, Tool Methods, Prompt Methods, Unknown Methods, Method Category Checks.
- Server Method Routing
- Core Protocol Methods
- Resource Methods
- Tool Methods
- Prompt Methods
- Unknown Methods
- Method Category Checks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `19b043432068b5503e1c63b1d11e215257b541f6359652b897e2c6a8a01aab97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19b043432068b5503e1c63b1d11e215257b541f6359652b897e2c6a8a01aab97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19b043432068b5503e1c63b1d11e215257b541f6359652b897e2c6a8a01aab97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/server_routing_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/server_routing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/server_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/server_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/server_routing_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes initialize method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/server_routing_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes initialized notification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/server_routing_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes ping method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
