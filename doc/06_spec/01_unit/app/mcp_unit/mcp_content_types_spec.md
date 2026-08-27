# Mcp Content Types Specification

> <details>

<!-- sdn-diagram:id=mcp_content_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_content_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_content_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_content_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/mcp_unit/mcp_content_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
