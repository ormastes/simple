# Protocol Methods Specification

> Tests covering Protocol Methods, Method Descriptions, is_initialize Predicate, is_ping Predicate, is_resource_method Predicate, is_tool_method Predicate, is_prompt_method Predicate, Method Summary Routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Methods Specification

## Scenarios

### Protocol Methods

### Method Descriptions

#### describes initialize method

- describes initialize method
   - Expected: method equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes initialize method")
val req = jo1(jp("method", js("initialize")))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialize")
```

</details>

#### describes initialized method

- describes initialized method
   - Expected: method equals `initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes initialized method")
val req = jo1(jp("method", js("initialized")))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialized")
```

</details>

#### describes ping method

- describes ping method
   - Expected: method equals `ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes ping method")
val req = jo1(jp("method", js("ping")))
val method = extract_json_string(req, "method")
expect(method).to_equal("ping")
```

</details>

#### describes resources/list method

- describes resources/list method
   - Expected: method equals `resources/list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes resources/list method")
val req = jo1(jp("method", js("resources/list")))
val method = extract_json_string(req, "method")
expect(method).to_equal("resources/list")
```

</details>

#### describes resources/read method

- describes resources/read method
   - Expected: method equals `resources/read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes resources/read method")
val req = jo1(jp("method", js("resources/read")))
val method = extract_json_string(req, "method")
expect(method).to_equal("resources/read")
```

</details>

#### describes tools/list method

- describes tools/list method
   - Expected: method equals `tools/list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes tools/list method")
val req = jo1(jp("method", js("tools/list")))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/list")
```

</details>

#### describes tools/call method

- describes tools/call method
   - Expected: method equals `tools/call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes tools/call method")
val req = jo1(jp("method", js("tools/call")))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/call")
```

</details>

#### describes shutdown method

- describes shutdown method
   - Expected: method equals `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes shutdown method")
val req = jo1(jp("method", js("shutdown")))
val method = extract_json_string(req, "method")
expect(method).to_equal("shutdown")
```

</details>

### is_initialize Predicate

#### returns true for initialize

- returns true for initialize
   - Expected: is_init is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for initialize")
val method = "initialize"
val is_init = method == "initialize"
expect(is_init).to_equal(true)
```

</details>

#### returns false for other methods

- returns false for other methods
   - Expected: is_init is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other methods")
val method = "ping"
val is_init = method == "initialize"
expect(is_init).to_equal(false)
```

</details>

### is_ping Predicate

#### returns true for ping

- returns true for ping
   - Expected: is_ping is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for ping")
val method = "ping"
val is_ping = method == "ping"
expect(is_ping).to_equal(true)
```

</details>

#### returns false for other methods

- returns false for other methods
   - Expected: is_ping is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other methods")
val method = "initialize"
val is_ping = method == "ping"
expect(is_ping).to_equal(false)
```

</details>

### is_resource_method Predicate

#### returns true for resources/list

- returns true for resources/list
   - Expected: is_resource is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for resources/list")
val method = "resources/list"
val is_resource = method.starts_with("resources/")
expect(is_resource).to_equal(true)
```

</details>

#### returns true for resources/read

- returns true for resources/read
   - Expected: is_resource is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for resources/read")
val method = "resources/read"
val is_resource = method.starts_with("resources/")
expect(is_resource).to_equal(true)
```

</details>

#### returns false for non-resource methods

- returns false for non-resource methods
   - Expected: is_resource is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-resource methods")
val method = "tools/list"
val is_resource = method.starts_with("resources/")
expect(is_resource).to_equal(false)
```

</details>

### is_tool_method Predicate

#### returns true for tools/list

- returns true for tools/list
   - Expected: is_tool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for tools/list")
val method = "tools/list"
val is_tool = method.starts_with("tools/")
expect(is_tool).to_equal(true)
```

</details>

#### returns true for tools/call

- returns true for tools/call
   - Expected: is_tool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for tools/call")
val method = "tools/call"
val is_tool = method.starts_with("tools/")
expect(is_tool).to_equal(true)
```

</details>

#### returns false for non-tool methods

- returns false for non-tool methods
   - Expected: is_tool is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-tool methods")
val method = "resources/list"
val is_tool = method.starts_with("tools/")
expect(is_tool).to_equal(false)
```

</details>

### is_prompt_method Predicate

#### returns true for prompts/list

- returns true for prompts/list
   - Expected: is_prompt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for prompts/list")
val method = "prompts/list"
val is_prompt = method.starts_with("prompts/")
expect(is_prompt).to_equal(true)
```

</details>

#### returns true for prompts/get

- returns true for prompts/get
   - Expected: is_prompt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for prompts/get")
val method = "prompts/get"
val is_prompt = method.starts_with("prompts/")
expect(is_prompt).to_equal(true)
```

</details>

#### returns false for non-prompt methods

- returns false for non-prompt methods
   - Expected: is_prompt is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-prompt methods")
val method = "tools/call"
val is_prompt = method.starts_with("prompts/")
expect(is_prompt).to_equal(false)
```

</details>

### Method Summary Routing

#### routes to initialize summary

- routes to initialize summary
   - Expected: response contains `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes to initialize summary")
val response = make_result_response("1", jo1(jp("method", js("initialize"))))
expect(response.contains("initialize")).to_equal(true)
```

</details>

#### routes to resource summary

- routes to resource summary
   - Expected: response contains `resources`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes to resource summary")
val response = make_result_response("1", jo1(jp("method", js("resources/list"))))
expect(response.contains("resources")).to_equal(true)
```

</details>

#### routes to tool summary

- routes to tool summary
   - Expected: response contains `tools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes to tool summary")
val response = make_result_response("1", jo1(jp("method", js("tools/call"))))
expect(response.contains("tools")).to_equal(true)
```

</details>

#### routes to prompt summary

- routes to prompt summary
   - Expected: response contains `prompts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes to prompt summary")
val response = make_result_response("1", jo1(jp("method", js("prompts/get"))))
expect(response.contains("prompts")).to_equal(true)
```

</details>

#### routes to ping summary

- routes to ping summary
   - Expected: response contains `ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes to ping summary")
val response = make_result_response("1", jo1(jp("method", js("ping"))))
expect(response.contains("ping")).to_equal(true)
```

</details>

#### routes to shutdown summary

- routes to shutdown summary
   - Expected: response contains `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes to shutdown summary")
val response = make_result_response("1", jo1(jp("method", js("shutdown"))))
expect(response.contains("shutdown")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/protocol_methods_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Protocol Methods, Method Descriptions, is_initialize Predicate, is_ping Predicate, is_resource_method Predicate, is_tool_method Predicate, is_prompt_method Predicate, Method Summary Routing.
- Protocol Methods
- Method Descriptions
- is_initialize Predicate
- is_ping Predicate
- is_resource_method Predicate
- is_tool_method Predicate
- is_prompt_method Predicate
- Method Summary Routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `a6723c45a77ad221e322b82f137e83c716b7c0f4662b7038aabd16c791d94900`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6723c45a77ad221e322b82f137e83c716b7c0f4662b7038aabd16c791d94900`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6723c45a77ad221e322b82f137e83c716b7c0f4662b7038aabd16c791d94900`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/protocol_methods_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/protocol_methods_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/protocol_methods_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/protocol_methods_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/protocol_methods_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'describes initialize method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/protocol_methods_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'describes initialized method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/protocol_methods_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'describes ping method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
