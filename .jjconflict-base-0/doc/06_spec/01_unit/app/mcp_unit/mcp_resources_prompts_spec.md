# Mcp Resources Prompts Specification

> <details>

<!-- sdn-diagram:id=mcp_resources_prompts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_resources_prompts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_resources_prompts_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_resources_prompts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "file:///path/to/file.spl"
expect(uri).to_start_with("file://")
expect(uri).to_end_with(".spl")
```

</details>

#### builds symbol URI correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "symbol:///MyClass"
expect(uri).to_start_with("symbol://")
```

</details>

#### detects MIME type for resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("code.spl")).to_equal("text/x-simple")
expect(detect_mime_type("data.json")).to_equal("application/json")
expect(detect_mime_type("doc.md")).to_equal("text/markdown")
```

</details>

#### when building resource list response

#### formats resource as JSON

1. jp
2. jp
3. jp
   - Expected: resource contains `"uri"`
   - Expected: resource contains `"name"`
   - Expected: resource contains `"mimeType"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32602, "Resource not found")
expect(response.contains("-32602")).to_equal(true)
expect(response.contains("Resource not found")).to_equal(true)
```

</details>

### MCP Prompt Management

#### when building prompt list

#### formats prompt info as JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prompt = jo2(jp("name", js("refactor-rename")), jp("description", js("Rename a symbol")))
expect(prompt.contains("refactor-rename")).to_equal(true)
expect(prompt.contains("Rename a symbol")).to_equal(true)
```

</details>

#### formats prompt argument as JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = jo3(jp("name", js("old_name")), jp("description", js("Current name")), jp("required", "true"))
expect(arg.contains("old_name")).to_equal(true)
expect(arg.contains("\"required\":true")).to_equal(true)
```

</details>

#### when building prompt messages

#### formats user message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = jo2(jp("role", js("user")), jp("content", js("Rename foo to bar")))
expect(msg.contains("\"role\":\"user\"")).to_equal(true)
expect(msg.contains("Rename foo to bar")).to_equal(true)
```

</details>

### MCP Resource URI Handling

#### when parsing file URIs

#### extracts URI from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("uri", js("file:///test.spl")))
val uri = extract_json_string(json, "uri")
expect(uri).to_equal("file:///test.spl")
```

</details>

#### when building resource content

#### formats resource content response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/mcp_unit/mcp_resources_prompts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
