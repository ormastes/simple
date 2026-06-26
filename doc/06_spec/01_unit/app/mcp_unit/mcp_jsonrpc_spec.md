# Mcp Jsonrpc Specification

> <details>

<!-- sdn-diagram:id=mcp_jsonrpc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_jsonrpc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_jsonrpc_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_jsonrpc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_req_params("1", "initialize", jo1(""))
val resp = handle_jsonrpc(req)
expect(resp.contains("\"jsonrpc\"")).to_equal(true)
expect(resp.contains("\"protocolVersion\"")).to_equal(true)
```

</details>

#### returns empty for initialized notification

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo3(jp("jsonrpc", js("2.0")), jp("method", js("initialized")), jp("id", "null"))
val resp = handle_jsonrpc(req)
expect(resp).to_equal("")
```

</details>

#### shutdown

#### responds to shutdown with null result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_req("5", "shutdown")
val resp = handle_jsonrpc(req)
expect(resp.contains("\"result\":null")).to_equal(true)
```

</details>

#### ping

#### responds to ping with empty result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_req("42", "ping")
val resp = handle_jsonrpc(req)
expect(resp.contains("\"result\"")).to_equal(true)
```

</details>

#### tools/list

#### returns list of available tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("3", "read_code", jo1(jp("path", js("test.spl"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("\"content\"")).to_equal(true)
```

</details>

#### calls file_info tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("4", "file_info", jo1(jp("path", js("test.spl"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("\"content\"")).to_equal(true)
```

</details>

#### returns error for unknown tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("7", "nonexistent", jo1(""))
val resp = handle_jsonrpc(req)
expect(resp.contains("\"error\"")).to_equal(true)
expect(resp.contains("-32602")).to_equal(true)
```

</details>

#### calls ui_access_snapshot tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("8", "ui_access_snapshot", jo1(""))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access snapshot")).to_equal(true)
```

</details>

#### calls ui_access_surface tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("9", "ui_access_surface", jo1(jp("surface_id", js("main"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access surface: main")).to_equal(true)
```

</details>

#### calls ui_access_find tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("10", "ui_access_find", jo1(jp("kind", js("button"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access find: button")).to_equal(true)
```

</details>

#### calls ui_access_act tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("11", "ui_access_act", jo1(jp("action", js("click"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access act: click")).to_equal(true)
```

</details>

#### calls ui_access_history tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("12", "ui_access_history", jo1(jp("count", js("5"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access history: 5")).to_equal(true)
```

</details>

#### calls ui_access_observe tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("13", "ui_access_observe", jo1(jp("canonical_id", js("main#submit_btn"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access observe: main#submit_btn")).to_equal(true)
```

</details>

#### calls ui_access_state tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("14", "ui_access_state", jo1(jp("state_key", js("focused"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access state: focused")).to_equal(true)
```

</details>

#### calls ui_access_query tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("15", "ui_access_query", jo1(jp("kind", js("button"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access query: button")).to_equal(true)
```

</details>

#### calls ui_access_ensure tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("16", "ui_access_ensure", jo1(jp("expectation", js("exists"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access ensure: exists")).to_equal(true)
```

</details>

#### calls ui_access_value tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("17", "ui_access_value", jo1(jp("canonical_id", js("main#name_input"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access value: main#name_input")).to_equal(true)
```

</details>

#### calls ui_access_adapter_snapshot tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("18", "ui_access_adapter_snapshot", jo1(jp("surface_id", js("main"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access adapter snapshot: main")).to_equal(true)
```

</details>

#### calls ui_access_visual_probe tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_tool_call_req("19", "ui_access_visual_probe", jo1(jp("surface_id", js("main"))))
val resp = handle_jsonrpc(req)
expect(resp.contains("UI access visual probe: main")).to_equal(true)
```

</details>

#### error handling

#### returns method not found for unknown method

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = make_req("10", "unknown/method")
val resp = handle_jsonrpc(req)
expect(resp.contains("\"error\"")).to_equal(true)
expect(resp.contains("-32601")).to_equal(true)
```

</details>

#### response format

#### all responses contain jsonrpc version

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init_resp = handle_jsonrpc(make_req("1", "initialize"))
val tools_resp = handle_jsonrpc(make_req("2", "tools/list"))
val shutdown_resp = handle_jsonrpc(make_req("3", "shutdown"))
expect(init_resp.contains("\"jsonrpc\"")).to_equal(true)
expect(tools_resp.contains("\"jsonrpc\"")).to_equal(true)
expect(shutdown_resp.contains("\"jsonrpc\"")).to_equal(true)
```

</details>

#### error responses have code and message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/mcp_unit/mcp_jsonrpc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
