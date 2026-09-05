# Mcp Resources Prompts Specification

> Tests covering MCP Resource Management, MCP Prompt Management, MCP Resource URI Handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Resources Prompts Specification

## Scenarios

### MCP Resource Management

#### when building resource URIs

#### builds file URI correctly

- builds file URI correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds file URI correctly")
val uri = "file:///path/to/file.spl"
expect(uri).to_start_with("file://")
expect(uri).to_end_with(".spl")
```

</details>

#### builds symbol URI correctly

- builds symbol URI correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds symbol URI correctly")
val uri = "symbol:///MyClass"
expect(uri).to_start_with("symbol://")
```

</details>

#### detects MIME type for resources

- detects MIME type for resources
   - Expected: detect_mime_type("code.spl") equals `text/x-simple`
   - Expected: detect_mime_type("data.json") equals `application/json`
   - Expected: detect_mime_type("doc.md") equals `text/markdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects MIME type for resources")
expect(detect_mime_type("code.spl")).to_equal("text/x-simple")
expect(detect_mime_type("data.json")).to_equal("application/json")
expect(detect_mime_type("doc.md")).to_equal("text/markdown")
```

</details>

#### when building resource list response

#### formats resource as JSON

- formats resource as JSON
   - Expected: resource contains `"uri"`
   - Expected: resource contains `"name"`
   - Expected: resource contains `"mimeType"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats resource as JSON")
val resource = jo3(
    jp("uri", js("file:///test.spl")),
    jp("name", js("test.spl")),
    jp("mimeType", js("text/x-simple"))
)
expect(resource.contains("\"uri\"")).to_equal(true)
expect(resource.contains("\"name\"")).to_equal(true)
expect(resource.contains("\"mimeType\"")).to_equal(true)
```

</details>

#### when handling missing resources

#### builds error response for missing resource

- builds error response for missing resource
   - Expected: response contains `-32602`
   - Expected: response contains `Resource not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds error response for missing resource")
val response = make_error_response("1", -32602, "Resource not found")
expect(response.contains("-32602")).to_equal(true)
expect(response.contains("Resource not found")).to_equal(true)
```

</details>

### MCP Prompt Management

#### when building prompt list

#### formats prompt info as JSON

- formats prompt info as JSON
   - Expected: prompt contains `refactor-rename`
   - Expected: prompt contains `Rename a symbol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats prompt info as JSON")
val prompt = jo2(jp("name", js("refactor-rename")), jp("description", js("Rename a symbol")))
expect(prompt.contains("refactor-rename")).to_equal(true)
expect(prompt.contains("Rename a symbol")).to_equal(true)
```

</details>

#### formats prompt argument as JSON

- formats prompt argument as JSON
   - Expected: arg contains `old_name`
   - Expected: arg contains `"required":true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats prompt argument as JSON")
val arg = jo3(jp("name", js("old_name")), jp("description", js("Current name")), jp("required", "true"))
expect(arg.contains("old_name")).to_equal(true)
expect(arg.contains("\"required\":true")).to_equal(true)
```

</details>

#### when building prompt messages

#### formats user message

- formats user message
   - Expected: msg contains `"role":"user"`
   - Expected: msg contains `Rename foo to bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats user message")
val msg = jo2(jp("role", js("user")), jp("content", js("Rename foo to bar")))
expect(msg.contains("\"role\":\"user\"")).to_equal(true)
expect(msg.contains("Rename foo to bar")).to_equal(true)
```

</details>

### MCP Resource URI Handling

#### when parsing file URIs

#### extracts URI from JSON

- extracts URI from JSON
   - Expected: uri equals `file:///test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts URI from JSON")
val json = jo1(jp("uri", js("file:///test.spl")))
val uri = extract_json_string(json, "uri")
expect(uri).to_equal("file:///test.spl")
```

</details>

#### when building resource content

#### formats resource content response

- formats resource content response
   - Expected: response contains `"contents"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats resource content response")
val content = jo2(jp("uri", js("file:///test.spl")), jp("text", js("fn main(): pass")))
val result = jo1(jp("contents", "[" + content + "]"))
val response = make_result_response("1", result)
expect(response.contains("\"contents\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_resources_prompts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Resource Management, MCP Prompt Management, MCP Resource URI Handling.
- MCP Resource Management
- MCP Prompt Management
- MCP Resource URI Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `d768194ca020b44fe9792822a63cffc03f6f2815ad667b2241c44a07dead30df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d768194ca020b44fe9792822a63cffc03f6f2815ad667b2241c44a07dead30df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d768194ca020b44fe9792822a63cffc03f6f2815ad667b2241c44a07dead30df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_resources_prompts_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_resources_prompts_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_resources_prompts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_resources_prompts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_resources_prompts_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds file URI correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_resources_prompts_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds symbol URI correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_resources_prompts_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects MIME type for resources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
