# Server Content Blocks Specification

> <details>

<!-- sdn-diagram:id=server_content_blocks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_content_blocks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_content_blocks_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_content_blocks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = jo2(jp("type", js("text")), jp("text", js("hello")))
expect(block.contains("text")).to_equal(true)
```

</details>

#### handles Image content block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_image_content("base64data", "image/png")
expect(block.contains("image")).to_equal(true)
```

</details>

#### handles Resource content block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = jo2(jp("type", js("resource")), jp("uri", js("file:///test.spl")))
expect(block.contains("resource")).to_equal(true)
```

</details>

### Content Block Serialization

#### serializes text block to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = jo2(jp("type", js("text")), jp("text", js("content")))
expect(block.contains("text")).to_equal(true)
expect(block.contains("content")).to_equal(true)
```

</details>

#### serializes image block to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_image_content("ABCD==", "image/jpeg")
expect(block.contains("ABCD==")).to_equal(true)
expect(block.contains("image/jpeg")).to_equal(true)
```

</details>

#### serializes resource block to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = jo2(jp("type", js("resource")), jp("uri", js("file:///test.spl")))
expect(block.contains("resource")).to_equal(true)
expect(block.contains("file:///test.spl")).to_equal(true)
```

</details>

### Content Block Lists

#### handles empty content list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = LB() + RB()
val response = make_result_response("1", jo1(jp("content", content)))
expect(response.contains("content")).to_equal(true)
```

</details>

#### handles single content block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = jo1(jp("type", js("text")))
val content = "[" + block + "]"
expect(content.contains("text")).to_equal(true)
```

</details>

#### handles multiple content blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = jo2(jp("type", js("text")), jp("text", js("hello")))
expect(block.contains("text")).to_equal(true)
```

</details>

#### validates image block has data and mimeType

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_image_content("data==", "image/png")
expect(block.contains("data")).to_equal(true)
expect(block.contains("image/png")).to_equal(true)
```

</details>

#### validates resource block has uri

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = jo2(jp("type", js("resource")), jp("uri", js("file:///test.spl")))
expect(block.contains("uri")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/server_content_blocks_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
