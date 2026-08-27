# Mcp Jsonrpc Specification

> Tests covering JSON-RPC Protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Jsonrpc Specification

## Scenarios

### JSON-RPC Protocol

#### initialize handshake

#### responds to initialize request

- responds to initialize request
   - Expected: resp contains `"jsonrpc"`
   - Expected: resp contains `"protocolVersion"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("responds to initialize request")
val req = make_req_params("1", "initialize", jo1(""))
val resp = handle_jsonrpc(req)
expect(resp.contains("\"jsonrpc\"")).to_equal(true)
expect(resp.contains("\"protocolVersion\"")).to_equal(true)
```

</details>

#### returns empty for initialized notification

- returns empty for initialized notification
   - Expected: resp equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for initialized notification")
val req = jo3(jp("jsonrpc", js("2.0")), jp("method", js("initialized")), jp("id", "null"))
val resp = handle_jsonrpc(req)
expect(resp).to_equal("")
```

</details>

#### shutdown

#### responds to shutdown with null result

- responds to shutdown with null result
   - Expected: resp contains `"result":null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("responds to shutdown with null result")
val req = make_req("5", "shutdown")
val resp = handle_jsonrpc(req)
expect(resp.contains("\"result\":null")).to_equal(true)
```

</details>

#### ping

#### responds to ping with empty result

- responds to ping with empty result
   - Expected: resp contains `"result"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("responds to ping with empty result")
val req = make_req("42", "ping")
val resp = handle_jsonrpc(req)
expect(resp.contains("\"result\"")).to_equal(true)
```

</details>

#### tools/list

#### returns list of available tools

- returns list of available tools
   - Expected: resp contains `"read_code"`
   - Expected: resp contains `"list_files"`
   - Expected: resp contains `"search_code"`
   - Expected: resp contains `"file_info"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns list of available tools")
val req = make_req("2", "tools/list")
val resp = handle_jsonrpc(req)
expect(resp.contains("\"read_code\"")).to_equal(true)
expect(resp.contains("\"list_files\"")).to_equal(true)
expect(resp.contains("\"search_code\"")).to_equal(true)
expect(resp.contains("\"file_info\"")).to_equal(true)
```

</details>

#### tools/call

#### calls read_code tool

- calls read_code tool
   - Expected: resp contains `"content"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls read_code tool")
val req = make_tool_call_req("3", "read_code", jo1(jp("path", js("test.spl"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("\"content\"")).to_equal(true)
```

</details>

#### calls file_info tool

- calls file_info tool
   - Expected: resp contains `"content"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls file_info tool")
val req = make_tool_call_req("4", "file_info", jo1(jp("path", js("test.spl"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("\"content\"")).to_equal(true)
```

</details>

#### returns error for unknown tool

- returns error for unknown tool
   - Expected: resp contains `"error"`
   - Expected: resp contains `-32602`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown tool")
val req = make_tool_call_req("7", "nonexistent", jo1(""))
val resp = handle_jsonrpc(req)
expect(resp.contains("\"error\"")).to_equal(true)
expect(resp.contains("-32602")).to_equal(true)
```

</details>

#### calls ui_access_snapshot tool

- calls ui_access_snapshot tool
   - Expected: resp contains `UI access snapshot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_snapshot tool")
val req = make_tool_call_req("8", "ui_access_snapshot", jo1(""))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access snapshot")).to_equal(true)
```

</details>

#### calls ui_access_surface tool

- calls ui_access_surface tool
   - Expected: resp contains `UI access surface: main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_surface tool")
val req = make_tool_call_req("9", "ui_access_surface", jo1(jp("surface_id", js("main"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access surface: main")).to_equal(true)
```

</details>

#### calls ui_access_find tool

- calls ui_access_find tool
   - Expected: resp contains `UI access find: button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_find tool")
val req = make_tool_call_req("10", "ui_access_find", jo1(jp("kind", js("button"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access find: button")).to_equal(true)
```

</details>

#### calls ui_access_act tool

- calls ui_access_act tool
   - Expected: resp contains `UI access act: click`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_act tool")
val req = make_tool_call_req("11", "ui_access_act", jo1(jp("action", js("click"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access act: click")).to_equal(true)
```

</details>

#### calls ui_access_history tool

- calls ui_access_history tool
   - Expected: resp contains `UI access history: 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_history tool")
val req = make_tool_call_req("12", "ui_access_history", jo1(jp("count", js("5"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access history: 5")).to_equal(true)
```

</details>

#### calls ui_access_observe tool

- calls ui_access_observe tool
   - Expected: resp contains `UI access observe: main#submit_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_observe tool")
val req = make_tool_call_req("13", "ui_access_observe", jo1(jp("canonical_id", js("main#submit_btn"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access observe: main#submit_btn")).to_equal(true)
```

</details>

#### calls ui_access_state tool

- calls ui_access_state tool
   - Expected: resp contains `UI access state: focused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_state tool")
val req = make_tool_call_req("14", "ui_access_state", jo1(jp("state_key", js("focused"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access state: focused")).to_equal(true)
```

</details>

#### calls ui_access_query tool

- calls ui_access_query tool
   - Expected: resp contains `UI access query: button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_query tool")
val req = make_tool_call_req("15", "ui_access_query", jo1(jp("kind", js("button"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access query: button")).to_equal(true)
```

</details>

#### calls ui_access_ensure tool

- calls ui_access_ensure tool
   - Expected: resp contains `UI access ensure: exists`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_ensure tool")
val req = make_tool_call_req("16", "ui_access_ensure", jo1(jp("expectation", js("exists"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access ensure: exists")).to_equal(true)
```

</details>

#### calls ui_access_value tool

- calls ui_access_value tool
   - Expected: resp contains `UI access value: main#name_input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_value tool")
val req = make_tool_call_req("17", "ui_access_value", jo1(jp("canonical_id", js("main#name_input"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access value: main#name_input")).to_equal(true)
```

</details>

#### calls ui_access_adapter_snapshot tool

- calls ui_access_adapter_snapshot tool
   - Expected: resp contains `UI access adapter snapshot: main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_adapter_snapshot tool")
val req = make_tool_call_req("18", "ui_access_adapter_snapshot", jo1(jp("surface_id", js("main"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access adapter snapshot: main")).to_equal(true)
```

</details>

#### calls ui_access_visual_probe tool

- calls ui_access_visual_probe tool
   - Expected: resp contains `UI access visual probe: main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls ui_access_visual_probe tool")
val req = make_tool_call_req("19", "ui_access_visual_probe", jo1(jp("surface_id", js("main"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access visual probe: main")).to_equal(true)
```

</details>

#### error handling

#### returns method not found for unknown method

- returns method not found for unknown method
   - Expected: resp contains `"error"`
   - Expected: resp contains `-32601`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns method not found for unknown method")
val req = make_req("10", "unknown/method")
val resp = handle_jsonrpc(req)
expect(resp.contains("\"error\"")).to_equal(true)
expect(resp.contains("-32601")).to_equal(true)
```

</details>

#### response format

#### all responses contain jsonrpc version

- all responses contain jsonrpc version
   - Expected: init_resp contains `"jsonrpc"`
   - Expected: tools_resp contains `"jsonrpc"`
   - Expected: shutdown_resp contains `"jsonrpc"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all responses contain jsonrpc version")
val init_resp = handle_jsonrpc(make_req("1", "initialize"))
val tools_resp = handle_jsonrpc(make_req("2", "tools/list"))
val shutdown_resp = handle_jsonrpc(make_req("3", "shutdown"))
expect(init_resp.contains("\"jsonrpc\"")).to_equal(true)
expect(tools_resp.contains("\"jsonrpc\"")).to_equal(true)
expect(shutdown_resp.contains("\"jsonrpc\"")).to_equal(true)
```

</details>

#### error responses have code and message

- error responses have code and message
   - Expected: resp contains `"code":`
   - Expected: resp contains `"message":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error responses have code and message")
val resp = handle_jsonrpc(make_req("1", "bad"))
expect(resp.contains("\"code\":")).to_equal(true)
expect(resp.contains("\"message\":")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_jsonrpc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JSON-RPC Protocol.
- JSON-RPC Protocol

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `3e7de78aece8ddebc3df96aae6c734512bffbf620463c6b4e89c654a0df99250`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e7de78aece8ddebc3df96aae6c734512bffbf620463c6b4e89c654a0df99250`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e7de78aece8ddebc3df96aae6c734512bffbf620463c6b4e89c654a0df99250`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_jsonrpc_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_jsonrpc_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_jsonrpc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_jsonrpc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_jsonrpc_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'responds to initialize request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_jsonrpc_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty for initialized notification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_jsonrpc_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'responds to shutdown with null result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
