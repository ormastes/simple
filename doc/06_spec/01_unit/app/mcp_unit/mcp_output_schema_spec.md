# Mcp Output Schema Specification

> <details>

<!-- sdn-diagram:id=mcp_output_schema_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_output_schema_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_output_schema_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_output_schema_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val props = jo1(jp("path", jo1(jp("type", js("string")))))
val required = "[" + js("path") + "]"
val output_schema = jo2(jp("type", js("object")), jp("properties", jo1(jp("lines", jo1(jp("type", js("integer")))))))
val schema = make_tool_schema_with_output("file_info", "Get file info", props, required, output_schema, true, false, true)
expect(schema.contains("outputSchema")).to_equal(true)
```

</details>

#### outputSchema contains type object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output_schema = jo1(jp("type", js("object")))
val schema = make_tool_schema_with_output("tool", "desc", LB() + RB(), "[]", output_schema, true, false, true)
expect(schema.contains("\"type\":\"object\"")).to_equal(true)
```

</details>

#### when tool has no outputSchema

#### regular register_tool omits outputSchema

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = register_tool("simple_tool", "A tool", ["x"], ["Param"], ["x"], true, false, true)
expect(schema.contains("outputSchema")).to_equal(false)
```

</details>

### MCP Structured Content in Tool Result

#### when tool returns structured content

#### includes content and structuredContent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "[" + jo2(jp("type", js("text")), jp("text", js("File has 120 lines"))) + "]"
val structured = jo2(jp("path", js("test.spl")), jp("lines", "120"))
val result = make_tool_result_with_structured("1", content, structured)
expect(result.contains("content")).to_equal(true)
expect(result.contains("structuredContent")).to_equal(true)
```

</details>

#### structured content includes data fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = make_image_content("iVBOR...base64", "image/png")
expect(img.contains("image")).to_equal(true)
expect(img.contains("image/png")).to_equal(true)
expect(img.contains("iVBOR")).to_equal(true)
```

</details>

#### when returning audio content

#### builds audio content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val audio = make_audio_content("UklGR...base64", "audio/wav")
expect(audio.contains("audio")).to_equal(true)
expect(audio.contains("audio/wav")).to_equal(true)
```

</details>

#### when returning resource link

#### builds basic resource link

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val link = make_resource_link_content("file:///test.spl", "test.spl")
expect(link.contains("resource_link")).to_equal(true)
expect(link.contains("file:///test.spl")).to_equal(true)
expect(link.contains("test.spl")).to_equal(true)
```

</details>

#### builds full resource link with optional fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val link = make_resource_link_content_full("file:///test.spl", "test.spl", "Test File", "A test file", "text/x-simple", 1024)
expect(link.contains("Test File")).to_equal(true)
expect(link.contains("A test file")).to_equal(true)
expect(link.contains("text/x-simple")).to_equal(true)
```

</details>

#### when returning embedded resource

#### builds embedded resource content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedded = make_embedded_resource_content("file:///test.spl", "fn main(): pass", "text/x-simple")
expect(embedded.contains("resource")).to_equal(true)
expect(embedded.contains("fn main")).to_equal(true)
expect(embedded.contains("text/x-simple")).to_equal(true)
```

</details>

### MCP Content Annotations

#### when adding annotations

#### supports audience annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ann = make_content_annotations(["user", "assistant"], "0.8", "2026-02-09T12:00:00Z")
expect(ann.contains("audience")).to_equal(true)
expect(ann.contains("user")).to_equal(true)
expect(ann.contains("assistant")).to_equal(true)
```

</details>

#### supports priority annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ann = make_content_annotations(["user"], "0.9", "")
expect(ann.contains("priority")).to_equal(true)
```

</details>

#### supports lastModified annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/mcp_unit/mcp_output_schema_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
