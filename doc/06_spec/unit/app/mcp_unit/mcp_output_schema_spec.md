# Mcp Output Schema Specification

> Tests covering MCP Output Schema in Tool Definition, MCP Structured Content in Tool Result, MCP Rich Content Types, MCP Content Annotations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Output Schema Specification

## Scenarios

### MCP Output Schema in Tool Definition

#### when tool declares outputSchema

#### includes outputSchema field

- includes outputSchema field
   - Expected: schema contains `outputSchema`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes outputSchema field")
val props = jo1(jp("path", jo1(jp("type", js("string")))))
val required = "[" + js("path") + "]"
val output_schema = jo2(jp("type", js("object")), jp("properties", jo1(jp("lines", jo1(jp("type", js("integer")))))))
val schema = make_tool_schema_with_output("file_info", "Get file info", props, required, output_schema, true, false, true)
expect(schema.contains("outputSchema")).to_equal(true)
```

</details>

#### outputSchema contains type object

- outputSchema contains type object
   - Expected: schema contains `"type":"object"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outputSchema contains type object")
val output_schema = jo1(jp("type", js("object")))
val schema = make_tool_schema_with_output("tool", "desc", LB() + RB(), "[]", output_schema, true, false, true)
expect(schema.contains("\"type\":\"object\"")).to_equal(true)
```

</details>

#### when tool has no outputSchema

#### regular register_tool omits outputSchema

- regular register_tool omits outputSchema
   - Expected: schema does not contain `outputSchema`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("regular register_tool omits outputSchema")
val schema = register_tool("simple_tool", "A tool", ["x"], ["Param"], ["x"], true, false, true)
expect(schema.contains("outputSchema")).to_equal(false)
```

</details>

### MCP Structured Content in Tool Result

#### when tool returns structured content

#### includes content and structuredContent

- includes content and structuredContent
   - Expected: result contains `content`
   - Expected: result contains `structuredContent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes content and structuredContent")
val content = "[" + jo2(jp("type", js("text")), jp("text", js("File has 120 lines"))) + "]"
val structured = jo2(jp("path", js("test.spl")), jp("lines", "120"))
val result = make_tool_result_with_structured("1", content, structured)
expect(result.contains("content")).to_equal(true)
expect(result.contains("structuredContent")).to_equal(true)
```

</details>

#### structured content includes data fields

- structured content includes data fields
   - Expected: result contains `test.spl`
   - Expected: result contains `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("structured content includes data fields")
val structured = jo2(jp("path", js("test.spl")), jp("lines", "120"))
val content = "[" + jo2(jp("type", js("text")), jp("text", js("info"))) + "]"
val result = make_tool_result_with_structured("1", content, structured)
expect(result.contains("test.spl")).to_equal(true)
expect(result.contains("120")).to_equal(true)
```

</details>

### MCP Rich Content Types

#### when returning image content

#### builds image content

- builds image content
   - Expected: img contains `image`
   - Expected: img contains `image/png`
   - Expected: img contains `iVBOR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds image content")
val img = make_image_content("iVBOR...base64", "image/png")
expect(img.contains("image")).to_equal(true)
expect(img.contains("image/png")).to_equal(true)
expect(img.contains("iVBOR")).to_equal(true)
```

</details>

#### when returning audio content

#### builds audio content

- builds audio content
   - Expected: audio contains `audio`
   - Expected: audio contains `audio/wav`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds audio content")
val audio = make_audio_content("UklGR...base64", "audio/wav")
expect(audio.contains("audio")).to_equal(true)
expect(audio.contains("audio/wav")).to_equal(true)
```

</details>

#### when returning resource link

#### builds basic resource link

- builds basic resource link
   - Expected: link contains `resource_link`
   - Expected: link contains `file:///test.spl`
   - Expected: link contains `test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds basic resource link")
val link = make_resource_link_content("file:///test.spl", "test.spl")
expect(link.contains("resource_link")).to_equal(true)
expect(link.contains("file:///test.spl")).to_equal(true)
expect(link.contains("test.spl")).to_equal(true)
```

</details>

#### builds full resource link with optional fields

- builds full resource link with optional fields
   - Expected: link contains `Test File`
   - Expected: link contains `A test file`
   - Expected: link contains `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds full resource link with optional fields")
val link = make_resource_link_content_full("file:///test.spl", "test.spl", "Test File", "A test file", "text/x-simple", 1024)
expect(link.contains("Test File")).to_equal(true)
expect(link.contains("A test file")).to_equal(true)
expect(link.contains("text/x-simple")).to_equal(true)
```

</details>

#### when returning embedded resource

#### builds embedded resource content

- builds embedded resource content
   - Expected: embedded contains `resource`
   - Expected: embedded contains `fn main`
   - Expected: embedded contains `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds embedded resource content")
val embedded = make_embedded_resource_content("file:///test.spl", "fn main(): pass", "text/x-simple")
expect(embedded.contains("resource")).to_equal(true)
expect(embedded.contains("fn main")).to_equal(true)
expect(embedded.contains("text/x-simple")).to_equal(true)
```

</details>

### MCP Content Annotations

#### when adding annotations

#### supports audience annotation

- supports audience annotation
   - Expected: ann contains `audience`
   - Expected: ann contains `user`
   - Expected: ann contains `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports audience annotation")
val ann = make_content_annotations(["user", "assistant"], "0.8", "2026-02-09T12:00:00Z")
expect(ann.contains("audience")).to_equal(true)
expect(ann.contains("user")).to_equal(true)
expect(ann.contains("assistant")).to_equal(true)
```

</details>

#### supports priority annotation

- supports priority annotation
   - Expected: ann contains `priority`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports priority annotation")
val ann = make_content_annotations(["user"], "0.9", "")
expect(ann.contains("priority")).to_equal(true)
```

</details>

#### supports lastModified annotation

- supports lastModified annotation
   - Expected: ann contains `lastModified`
   - Expected: ann contains `2026-02-09`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports lastModified annotation")
val ann = make_content_annotations([], "", "2026-02-09T12:00:00Z")
expect(ann.contains("lastModified")).to_equal(true)
expect(ann.contains("2026-02-09")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_output_schema_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Output Schema in Tool Definition, MCP Structured Content in Tool Result, MCP Rich Content Types, MCP Content Annotations.
- MCP Output Schema in Tool Definition
- MCP Structured Content in Tool Result
- MCP Rich Content Types
- MCP Content Annotations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `f55b18fc78e77bc0c0b3ad087a73fc7777e6aeffa2032978a1bf109fdacbb349`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f55b18fc78e77bc0c0b3ad087a73fc7777e6aeffa2032978a1bf109fdacbb349`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f55b18fc78e77bc0c0b3ad087a73fc7777e6aeffa2032978a1bf109fdacbb349`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_output_schema_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_output_schema_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_output_schema_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_output_schema_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_output_schema_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes outputSchema field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_output_schema_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outputSchema contains type object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_output_schema_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'regular register_tool omits outputSchema' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
