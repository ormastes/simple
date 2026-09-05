# Server Content Blocks Specification

> Tests covering Server Content Blocks, ContentBlock Types, Content Block Serialization, Content Block Lists, Content Block Validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Content Blocks Specification

## Scenarios

### Server Content Blocks

### ContentBlock Types

#### handles Text content block

- handles Text content block
   - Expected: block contains `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Text content block")
val block = jo2(jp("type", js("text")), jp("text", js("hello")))
expect(block.contains("text")).to_equal(true)
```

</details>

#### handles Image content block

- handles Image content block
   - Expected: block contains `image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Image content block")
val block = make_image_content("base64data", "image/png")
expect(block.contains("image")).to_equal(true)
```

</details>

#### handles Resource content block

- handles Resource content block
   - Expected: block contains `resource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Resource content block")
val block = jo2(jp("type", js("resource")), jp("uri", js("file:///test.spl")))
expect(block.contains("resource")).to_equal(true)
```

</details>

### Content Block Serialization

#### serializes text block to JSON

- serializes text block to JSON
   - Expected: block contains `text`
   - Expected: block contains `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes text block to JSON")
val block = jo2(jp("type", js("text")), jp("text", js("content")))
expect(block.contains("text")).to_equal(true)
expect(block.contains("content")).to_equal(true)
```

</details>

#### serializes image block to JSON

- serializes image block to JSON
   - Expected: block contains `ABCD==`
   - Expected: block contains `image/jpeg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes image block to JSON")
val block = make_image_content("ABCD==", "image/jpeg")
expect(block.contains("ABCD==")).to_equal(true)
expect(block.contains("image/jpeg")).to_equal(true)
```

</details>

#### serializes resource block to JSON

- serializes resource block to JSON
   - Expected: block contains `resource`
   - Expected: block contains `file:///test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes resource block to JSON")
val block = jo2(jp("type", js("resource")), jp("uri", js("file:///test.spl")))
expect(block.contains("resource")).to_equal(true)
expect(block.contains("file:///test.spl")).to_equal(true)
```

</details>

### Content Block Lists

#### handles empty content list

- handles empty content list
   - Expected: response contains `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty content list")
val content = LB() + RB()
val response = make_result_response("1", jo1(jp("content", content)))
expect(response.contains("content")).to_equal(true)
```

</details>

#### handles single content block

- handles single content block
   - Expected: content contains `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single content block")
val block = jo1(jp("type", js("text")))
val content = "[" + block + "]"
expect(content.contains("text")).to_equal(true)
```

</details>

#### handles multiple content blocks

- handles multiple content blocks
   - Expected: content contains `text`
   - Expected: content contains `image`
   - Expected: content contains `resource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple content blocks")
val b1 = jo1(jp("type", js("text")))
val b2 = jo1(jp("type", js("image")))
val b3 = jo1(jp("type", js("resource")))
val content = "[" + b1 + "," + b2 + "," + b3 + "]"
expect(content.contains("text")).to_equal(true)
expect(content.contains("image")).to_equal(true)
expect(content.contains("resource")).to_equal(true)
```

</details>

### Content Block Validation

#### validates text block has text field

- validates text block has text field
   - Expected: block contains `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates text block has text field")
val block = jo2(jp("type", js("text")), jp("text", js("hello")))
expect(block.contains("text")).to_equal(true)
```

</details>

#### validates image block has data and mimeType

- validates image block has data and mimeType
   - Expected: block contains `data`
   - Expected: block contains `image/png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates image block has data and mimeType")
val block = make_image_content("data==", "image/png")
expect(block.contains("data")).to_equal(true)
expect(block.contains("image/png")).to_equal(true)
```

</details>

#### validates resource block has uri

- validates resource block has uri
   - Expected: block contains `uri`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates resource block has uri")
val block = jo2(jp("type", js("resource")), jp("uri", js("file:///test.spl")))
expect(block.contains("uri")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/server_content_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Server Content Blocks, ContentBlock Types, Content Block Serialization, Content Block Lists, Content Block Validation.
- Server Content Blocks
- ContentBlock Types
- Content Block Serialization
- Content Block Lists
- Content Block Validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `5fe0bbf3e88a32a5cf03b89a9fc194f2997614e895fca8eccac2690a386d8783`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fe0bbf3e88a32a5cf03b89a9fc194f2997614e895fca8eccac2690a386d8783`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fe0bbf3e88a32a5cf03b89a9fc194f2997614e895fca8eccac2690a386d8783`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/server_content_blocks_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/server_content_blocks_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/server_content_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/server_content_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/server_content_blocks_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles Text content block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/server_content_blocks_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles Image content block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/server_content_blocks_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles Resource content block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
