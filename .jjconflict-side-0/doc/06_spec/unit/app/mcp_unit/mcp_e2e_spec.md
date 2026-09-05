# Mcp E2e Specification

> Tests covering MCP E2E - extract_json_string round trip, MCP E2E - extract_json_value, MCP E2E - escape_json, MCP E2E - make_result_response, MCP E2E - make_error_response, MCP E2E - make_tool_result, MCP E2E - log level ordering, MCP E2E - make_log_notification, MCP E2E - detect_mime_type, MCP E2E - detect_file_content_type, MCP E2E - make_image_content, MCP E2E - make_resource_link_content.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp E2e Specification

## Scenarios

### MCP E2E - extract_json_string round trip

#### extracts string from built JSON

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts string from built JSON
   - Expected: method equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts string from built JSON")
val json = jo2(jp("method", js("initialize")), jp("id", "1"))
val method = extract_json_string(json, "method")
expect(method).to_equal("initialize")
```

</details>

#### extracts nested string from built JSON

- extracts nested string from built JSON
   - Expected: name equals `read_code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts nested string from built JSON")
val params = jo1(jp("name", js("read_code")))
val json = jo2(jp("method", js("tools/call")), jp("params", params))
val name = extract_nested_string(json, "params", "name")
expect(name).to_equal("read_code")
```

</details>

#### handles missing keys gracefully

- handles missing keys gracefully
   - Expected: missing equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing keys gracefully")
val json = jo1(jp("method", js("test")))
val missing = extract_json_string(json, "nonexistent")
expect(missing).to_equal("")
```

</details>

### MCP E2E - extract_json_value

#### extracts numeric value

- extracts numeric value
   - Expected: extract_json_value(json, "id") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts numeric value")
val json = jo2(jp("id", "42"), jp("method", js("test")))
expect(extract_json_value(json, "id")).to_equal("42")
```

</details>

#### extracts boolean value

- extracts boolean value
   - Expected: extract_json_value(json, "flag") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts boolean value")
val json = jo1(jp("flag", "true"))
expect(extract_json_value(json, "flag")).to_equal("true")
```

</details>

#### returns null for missing key

- returns null for missing key
   - Expected: extract_json_value(json, "missing") equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns null for missing key")
val json = jo1(jp("a", "1"))
expect(extract_json_value(json, "missing")).to_equal("null")
```

</details>

### MCP E2E - escape_json

#### escapes strings with special characters

- escapes strings with special characters
   - Expected: escaped does not contain `NL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes strings with special characters")
val escaped = escape_json("line1{NL}line2")
expect(escaped.contains(NL)).to_equal(false)
```

</details>

#### handles empty string

- handles empty string
   - Expected: escape_json("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
expect(escape_json("")).to_equal("")
```

</details>

#### preserves normal characters

- preserves normal characters
   - Expected: escape_json("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves normal characters")
expect(escape_json("hello")).to_equal("hello")
```

</details>

### MCP E2E - make_result_response

#### creates valid JSON-RPC response

- creates valid JSON-RPC response
   - Expected: response contains `jsonrpc`
   - Expected: response contains `2.0`
   - Expected: response contains `result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates valid JSON-RPC response")
val response = make_result_response("1", js("ok"))
expect(response.contains("jsonrpc")).to_equal(true)
expect(response.contains("2.0")).to_equal(true)
expect(response.contains("result")).to_equal(true)
```

</details>

#### includes specified id

- includes specified id
   - Expected: response contains `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes specified id")
val response = make_result_response("42", js("done"))
expect(response.contains("42")).to_equal(true)
```

</details>

### MCP E2E - make_error_response

#### creates error response with code

- creates error response with code
   - Expected: response contains `-32600`
   - Expected: response contains `Invalid request`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error response with code")
val response = make_error_response("1", -32600, "Invalid request")
expect(response.contains("-32600")).to_equal(true)
expect(response.contains("Invalid request")).to_equal(true)
```

</details>

#### includes error object

- includes error object
   - Expected: response contains `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes error object")
val response = make_error_response("1", -32601, "Method not found")
expect(response.contains("error")).to_equal(true)
```

</details>

### MCP E2E - make_tool_result

#### creates tool result with content

- creates tool result with content
   - Expected: result contains `content`
   - Expected: result contains `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates tool result with content")
val result = make_tool_result("1", "Hello world")
expect(result.contains("content")).to_equal(true)
expect(result.contains("text")).to_equal(true)
```

</details>

#### includes jsonrpc version

- includes jsonrpc version
   - Expected: result contains `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes jsonrpc version")
val result = make_tool_result("1", "test")
expect(result.contains("2.0")).to_equal(true)
```

</details>

### MCP E2E - log level ordering

#### debug is lowest priority

- debug is lowest priority
   - Expected: debug_level < info_level is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug is lowest priority")
val debug_level = log_level_to_int("debug")
val info_level = log_level_to_int("info")
expect(debug_level < info_level).to_equal(true)
```

</details>

#### emergency is highest priority

- emergency is highest priority
   - Expected: emergency_level > error_level is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emergency is highest priority")
val emergency_level = log_level_to_int("emergency")
val error_level = log_level_to_int("error")
expect(emergency_level > error_level).to_equal(true)
```

</details>

#### all levels are ordered

- all levels are ordered
   - Expected: d < i is true
   - Expected: i < n is true
   - Expected: n < w is true
   - Expected: w < e is true
   - Expected: e < c is true
   - Expected: c < a is true
   - Expected: a < em is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all levels are ordered")
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

- includes method field
   - Expected: notif contains `notifications/message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes method field")
val notif = make_log_notification("info", "Server started", "mcp")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>

#### includes log level

- includes log level
   - Expected: notif contains `warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes log level")
val notif = make_log_notification("warning", "Low memory", "mcp")
expect(notif.contains("warning")).to_equal(true)
```

</details>

#### includes logger name

- includes logger name
   - Expected: notif contains `mcp.tools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes logger name")
val notif = make_log_notification("info", "Test", "mcp.tools")
expect(notif.contains("mcp.tools")).to_equal(true)
```

</details>

### MCP E2E - detect_mime_type

#### detects Simple language files

- detects Simple language files
   - Expected: detect_mime_type("test.spl") equals `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects Simple language files")
expect(detect_mime_type("test.spl")).to_equal("text/x-simple")
```

</details>

#### detects JSON files

- detects JSON files
   - Expected: detect_mime_type("config.json") equals `application/json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects JSON files")
expect(detect_mime_type("config.json")).to_equal("application/json")
```

</details>

#### detects markdown files

- detects markdown files
   - Expected: detect_mime_type("README.md") equals `text/markdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects markdown files")
expect(detect_mime_type("README.md")).to_equal("text/markdown")
```

</details>

#### detects PNG images

- detects PNG images
   - Expected: detect_mime_type("logo.png") equals `image/png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects PNG images")
expect(detect_mime_type("logo.png")).to_equal("image/png")
```

</details>

#### defaults to text/plain for unknown

- defaults to text/plain for unknown
   - Expected: detect_mime_type("file.xyz") equals `text/plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to text/plain for unknown")
expect(detect_mime_type("file.xyz")).to_equal("text/plain")
```

</details>

### MCP E2E - detect_file_content_type

#### detects image files

- detects image files
   - Expected: detect_file_content_type("photo.jpg") equals `image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects image files")
expect(detect_file_content_type("photo.jpg")).to_equal("image")
```

</details>

#### detects audio files

- detects audio files
   - Expected: detect_file_content_type("song.mp3") equals `audio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects audio files")
expect(detect_file_content_type("song.mp3")).to_equal("audio")
```

</details>

#### detects text files

- detects text files
   - Expected: detect_file_content_type("code.spl") equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects text files")
expect(detect_file_content_type("code.spl")).to_equal("text")
```

</details>

### MCP E2E - make_image_content

#### creates image content object

- creates image content object
   - Expected: content contains `image`
   - Expected: content contains `base64data`
   - Expected: content contains `image/png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates image content object")
val content = make_image_content("base64data", "image/png")
expect(content.contains("image")).to_equal(true)
expect(content.contains("base64data")).to_equal(true)
expect(content.contains("image/png")).to_equal(true)
```

</details>

### MCP E2E - make_resource_link_content

#### creates resource link with uri and name

- creates resource link with uri and name
   - Expected: content contains `resource_link`
   - Expected: content contains `test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates resource link with uri and name")
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
| Source | `test/unit/app/mcp_unit/mcp_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP E2E - extract_json_string round trip, MCP E2E - extract_json_value, MCP E2E - escape_json, MCP E2E - make_result_response, MCP E2E - make_error_response, MCP E2E - make_tool_result, MCP E2E - log level ordering, MCP E2E - make_log_notification, MCP E2E - detect_mime_type, MCP E2E - detect_file_content_type, MCP E2E - make_image_content, MCP E2E - make_resource_link_content.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `901883baadfbed4d91fcad2ceb84d2b3c09a3eb7da813a775a4be9665f3fb864`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `901883baadfbed4d91fcad2ceb84d2b3c09a3eb7da813a775a4be9665f3fb864`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `901883baadfbed4d91fcad2ceb84d2b3c09a3eb7da813a775a4be9665f3fb864`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_e2e_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_e2e_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_e2e_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts string from built JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_e2e_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts nested string from built JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_e2e_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles missing keys gracefully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
