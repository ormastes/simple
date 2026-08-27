# Mcp Content Types Specification

> Tests covering MCP Image Content, MCP Audio Content, MCP Resource Link Content, MCP Embedded Resource Content, MCP Content Annotations, MCP Tool Result.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Content Types Specification

## Scenarios

### MCP Image Content

<details>
<summary>Advanced: builds with data and MIME type</summary>

#### builds with data and MIME type _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds with data and MIME type
   - Expected: content contains `"type":"image"`
   - Expected: content contains `"data":"base64data=="`
   - Expected: content contains `"mimeType":"image/png"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with data and MIME type")
val content = make_image_content("base64data==", "image/png")
expect(content.contains("\"type\":\"image\"")).to_equal(true)
expect(content.contains("\"data\":\"base64data==\"")).to_equal(true)
expect(content.contains("\"mimeType\":\"image/png\"")).to_equal(true)
```

</details>


</details>

### MCP Audio Content

<details>
<summary>Advanced: builds with data and MIME type</summary>

#### builds with data and MIME type _(slow)_

- builds with data and MIME type
   - Expected: content contains `"type":"audio"`
   - Expected: content contains `"mimeType":"audio/wav"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with data and MIME type")
val content = make_audio_content("audiodata==", "audio/wav")
expect(content.contains("\"type\":\"audio\"")).to_equal(true)
expect(content.contains("\"mimeType\":\"audio/wav\"")).to_equal(true)
```

</details>


</details>

### MCP Resource Link Content

<details>
<summary>Advanced: builds with URI and name</summary>

#### builds with URI and name _(slow)_

- builds with URI and name
   - Expected: content contains `"type":"resource_link"`
   - Expected: content contains `"uri":"file:///test.spl"`
   - Expected: content contains `"name":"test.spl"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with URI and name")
val content = make_resource_link_content("file:///test.spl", "test.spl")
expect(content.contains("\"type\":\"resource_link\"")).to_equal(true)
expect(content.contains("\"uri\":\"file:///test.spl\"")).to_equal(true)
expect(content.contains("\"name\":\"test.spl\"")).to_equal(true)
```

</details>


</details>

### MCP Embedded Resource Content

<details>
<summary>Advanced: builds with URI and text content</summary>

#### builds with URI and text content _(slow)_

- builds with URI and text content
   - Expected: content contains `"type":"resource"`
   - Expected: content contains `fn main(): pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with URI and text content")
val content = make_embedded_resource_content("file:///test.spl", "fn main(): pass", "text/x-simple")
expect(content.contains("\"type\":\"resource\"")).to_equal(true)
expect(content.contains("fn main(): pass")).to_equal(true)
```

</details>


</details>

### MCP Content Annotations

<details>
<summary>Advanced: builds with audience and priority</summary>

#### builds with audience and priority _(slow)_

- builds with audience and priority
   - Expected: annot contains `"audience"`
   - Expected: annot contains `"priority":0.8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with audience and priority")
val annot = make_content_annotations(["user"], "0.8", "")
expect(annot.contains("\"audience\"")).to_equal(true)
expect(annot.contains("\"priority\":0.8")).to_equal(true)
```

</details>


</details>

### MCP Tool Result

<details>
<summary>Advanced: wraps text content in proper structure</summary>

#### wraps text content in proper structure _(slow)_

- wraps text content in proper structure
   - Expected: result contains `"content"`
   - Expected: result contains `"type":"text"`
   - Expected: result contains `Hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps text content in proper structure")
val result = make_tool_result("1", "Hello world")
expect(result.contains("\"content\"")).to_equal(true)
expect(result.contains("\"type\":\"text\"")).to_equal(true)
expect(result.contains("Hello world")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_content_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Image Content, MCP Audio Content, MCP Resource Link Content, MCP Embedded Resource Content, MCP Content Annotations, MCP Tool Result.
- MCP Image Content
- MCP Audio Content
- MCP Resource Link Content
- MCP Embedded Resource Content
- MCP Content Annotations
- MCP Tool Result

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
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

- Canonical SPipe generation for source `024d70631e409dd154f4556ddfcf95fe9ef09c8f5cca6e05c42f1c0d3d3921b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `024d70631e409dd154f4556ddfcf95fe9ef09c8f5cca6e05c42f1c0d3d3921b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `024d70631e409dd154f4556ddfcf95fe9ef09c8f5cca6e05c42f1c0d3d3921b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_content_types_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_content_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_content_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_content_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_content_types_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds with data and MIME type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_content_types_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds with data and MIME type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_content_types_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds with URI and name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
