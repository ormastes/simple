# Mcp E2e Specification

> <details>

<!-- sdn-diagram:id=mcp_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp E2e Specification

## Scenarios

### MCP E2E - extract_json_string round trip

#### extracts string from built JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("method", js("initialize")), jp("id", "1"))
val method = extract_json_string(json, "method")
expect(method).to_equal("initialize")
```

</details>

#### extracts nested string from built JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("name", js("read_code")))
val json = jo2(jp("method", js("tools/call")), jp("params", params))
val name = extract_nested_string(json, "params", "name")
expect(name).to_equal("read_code")
```

</details>

#### handles missing keys gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("method", js("test")))
val missing = extract_json_string(json, "nonexistent")
expect(missing).to_equal("")
```

</details>

### MCP E2E - extract_json_value

#### extracts numeric value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("id", "42"), jp("method", js("test")))
expect(extract_json_value(json, "id")).to_equal("42")
```

</details>

#### extracts boolean value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("flag", "true"))
expect(extract_json_value(json, "flag")).to_equal("true")
```

</details>

#### returns null for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("a", "1"))
expect(extract_json_value(json, "missing")).to_equal("null")
```

</details>

### MCP E2E - escape_json

#### escapes strings with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("line1{NL}line2")
expect(escaped.contains(NL)).to_equal(false)
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("")).to_equal("")
```

</details>

#### preserves normal characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("hello")).to_equal("hello")
```

</details>

### MCP E2E - make_result_response

#### creates valid JSON-RPC response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", js("ok"))
expect(response.contains("jsonrpc")).to_equal(true)
expect(response.contains("2.0")).to_equal(true)
expect(response.contains("result")).to_equal(true)
```

</details>

#### includes specified id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("42", js("done"))
expect(response.contains("42")).to_equal(true)
```

</details>

### MCP E2E - make_error_response

#### creates error response with code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32600, "Invalid request")
expect(response.contains("-32600")).to_equal(true)
expect(response.contains("Invalid request")).to_equal(true)
```

</details>

#### includes error object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32601, "Method not found")
expect(response.contains("error")).to_equal(true)
```

</details>

### MCP E2E - make_tool_result

#### creates tool result with content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_tool_result("1", "Hello world")
expect(result.contains("content")).to_equal(true)
expect(result.contains("text")).to_equal(true)
```

</details>

#### includes jsonrpc version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_tool_result("1", "test")
expect(result.contains("2.0")).to_equal(true)
```

</details>

### MCP E2E - log level ordering

#### debug is lowest priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_level = log_level_to_int("debug")
val info_level = log_level_to_int("info")
expect(debug_level < info_level).to_equal(true)
```

</details>

#### emergency is highest priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val emergency_level = log_level_to_int("emergency")
val error_level = log_level_to_int("error")
expect(emergency_level > error_level).to_equal(true)
```

</details>

#### all levels are ordered

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = log_level_to_int("debug")
val i = log_level_to_int("info")
val n = log_level_to_int("notice")
val w = log_level_to_int("warning")
val e = log_level_to_int("error")
val c = log_level_to_int("critical")
val a = log_level_to_int("alert")
val em = log_level_to_int("emergency")
expect(d < i).to_equal(true)
expect(i < n).to_equal(true)
expect(n < w).to_equal(true)
expect(w < e).to_equal(true)
expect(e < c).to_equal(true)
expect(c < a).to_equal(true)
expect(a < em).to_equal(true)
```

</details>

### MCP E2E - make_log_notification

#### includes method field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "Server started", "mcp")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>

#### includes log level

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("warning", "Low memory", "mcp")
expect(notif.contains("warning")).to_equal(true)
```

</details>

#### includes logger name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_log_notification("info", "Test", "mcp.tools")
expect(notif.contains("mcp.tools")).to_equal(true)
```

</details>

### MCP E2E - detect_mime_type

#### detects Simple language files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("test.spl")).to_equal("text/x-simple")
```

</details>

#### detects JSON files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("config.json")).to_equal("application/json")
```

</details>

#### detects markdown files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("README.md")).to_equal("text/markdown")
```

</details>

#### detects PNG images

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("logo.png")).to_equal("image/png")
```

</details>

#### defaults to text/plain for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("file.xyz")).to_equal("text/plain")
```

</details>

### MCP E2E - detect_file_content_type

#### detects image files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_file_content_type("photo.jpg")).to_equal("image")
```

</details>

#### detects audio files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_file_content_type("song.mp3")).to_equal("audio")
```

</details>

#### detects text files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_file_content_type("code.spl")).to_equal("text")
```

</details>

### MCP E2E - make_image_content

#### creates image content object

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = make_image_content("base64data", "image/png")
expect(content.contains("image")).to_equal(true)
expect(content.contains("base64data")).to_equal(true)
expect(content.contains("image/png")).to_equal(true)
```

</details>

### MCP E2E - make_resource_link_content

#### creates resource link with uri and name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = make_resource_link_content("file:///test.spl", "test.spl")
expect(content.contains("resource_link")).to_equal(true)
expect(content.contains("test.spl")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP E2E - extract_json_string round trip
- MCP E2E - extract_json_value
- MCP E2E - escape_json
- MCP E2E - make_result_response
- MCP E2E - make_error_response
- MCP E2E - make_tool_result
- MCP E2E - log level ordering
- MCP E2E - make_log_notification
- MCP E2E - detect_mime_type
- MCP E2E - detect_file_content_type
- MCP E2E - make_image_content
- MCP E2E - make_resource_link_content

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
