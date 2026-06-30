# MCP UI Access Tools Specification

> Validates the ui_access MCP tool family: ui_access_snapshot, ui_access_surface, ui_access_find, ui_access_act, ui_access_history, ui_access_observe, ui_access_state, ui_access_query, ui_access_ensure, ui_access_value, ui_access_adapter_snapshot, ui_access_visual_probe.

<!-- sdn-diagram:id=ui_access_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_tools_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP UI Access Tools Specification

Validates the ui_access MCP tool family: ui_access_snapshot, ui_access_surface, ui_access_find, ui_access_act, ui_access_history, ui_access_observe, ui_access_state, ui_access_query, ui_access_ensure, ui_access_value, ui_access_adapter_snapshot, ui_access_visual_probe.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3031-3035 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/mcp_unit/ui_access_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the ui_access MCP tool family:
ui_access_snapshot, ui_access_surface, ui_access_find, ui_access_act,
ui_access_history, ui_access_observe, ui_access_state, ui_access_query,
ui_access_ensure, ui_access_value, ui_access_adapter_snapshot,
ui_access_visual_probe.

The spec checks the tool vocabulary, tool-list exposure, and tools/call routing
behaviour using a local JSON-RPC mock.

## Scenarios

### ui_access tool family

#### tool vocabulary

#### contains twelve ui_access tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = [
    "ui_access_snapshot",
    "ui_access_surface",
    "ui_access_find",
    "ui_access_act",
    "ui_access_history",
    "ui_access_observe",
    "ui_access_state",
    "ui_access_query",
    "ui_access_ensure",
    "ui_access_value",
    "ui_access_adapter_snapshot",
    "ui_access_visual_probe"
]
expect(tools.len()).to_equal(12)
```

</details>

#### all ui_access tools use the canonical prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = [
    "ui_access_snapshot",
    "ui_access_surface",
    "ui_access_find",
    "ui_access_act",
    "ui_access_history",
    "ui_access_observe",
    "ui_access_state",
    "ui_access_query",
    "ui_access_ensure",
    "ui_access_value",
    "ui_access_adapter_snapshot",
    "ui_access_visual_probe"
]
for tool in tools:
    expect(tool.starts_with("ui_access_")).to_equal(true)
```

</details>

#### tools/list

#### advertises all ui_access tool names

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_req("1", "tools/list"))
expect(resp.contains("\"ui_access_snapshot\"")).to_equal(true)
expect(resp.contains("\"ui_access_surface\"")).to_equal(true)
expect(resp.contains("\"ui_access_find\"")).to_equal(true)
expect(resp.contains("\"ui_access_act\"")).to_equal(true)
expect(resp.contains("\"ui_access_history\"")).to_equal(true)
expect(resp.contains("\"ui_access_observe\"")).to_equal(true)
expect(resp.contains("\"ui_access_state\"")).to_equal(true)
expect(resp.contains("\"ui_access_query\"")).to_equal(true)
expect(resp.contains("\"ui_access_ensure\"")).to_equal(true)
expect(resp.contains("\"ui_access_value\"")).to_equal(true)
expect(resp.contains("\"ui_access_adapter_snapshot\"")).to_equal(true)
expect(resp.contains("\"ui_access_visual_probe\"")).to_equal(true)
```

</details>

#### tools/call

#### routes ui_access_snapshot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("2", "ui_access_snapshot", jo1("")))
expect(resp.contains("snapshot: ui_access_snapshot")).to_equal(true)
```

</details>

#### routes ui_access_surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("3", "ui_access_surface", jo1(jp("surface_id", js("main")))))
expect(resp.contains("surface: main")).to_equal(true)
```

</details>

#### routes ui_access_find

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("4", "ui_access_find", jo1(jp("kind", js("button")))))
expect(resp.contains("find: button")).to_equal(true)
```

</details>

#### routes ui_access_act

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("5", "ui_access_act", jo1(jp("action", js("click")))))
expect(resp.contains("act: click")).to_equal(true)
```

</details>

#### routes ui_access_history

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("6", "ui_access_history", jo1(jp("count", js("5")))))
expect(resp.contains("history: 5")).to_equal(true)
```

</details>

#### routes ui_access_observe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("7", "ui_access_observe", jo1(jp("canonical_id", js("main#submit_btn")))))
expect(resp.contains("observe: main#submit_btn")).to_equal(true)
```

</details>

#### routes ui_access_state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("8", "ui_access_state", jo1(jp("state_key", js("focused")))))
expect(resp.contains("state: focused")).to_equal(true)
```

</details>

#### routes ui_access_query

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("9", "ui_access_query", jo1(jp("kind", js("button")))))
expect(resp.contains("query: button")).to_equal(true)
```

</details>

#### routes ui_access_ensure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("10", "ui_access_ensure", jo1(jp("expectation", js("exists")))))
expect(resp.contains("ensure: exists")).to_equal(true)
```

</details>

#### routes ui_access_value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("11", "ui_access_value", jo1(jp("canonical_id", js("main#name_input")))))
expect(resp.contains("value: main#name_input")).to_equal(true)
```

</details>

#### routes ui_access_adapter_snapshot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("12", "ui_access_adapter_snapshot", jo1(jp("surface_id", js("main")))))
expect(resp.contains("adapter_snapshot: main")).to_equal(true)
```

</details>

#### routes ui_access_visual_probe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_jsonrpc(make_tool_call_req("13", "ui_access_visual_probe", jo1(jp("surface_id", js("main")))))
expect(resp.contains("visual_probe: main")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
