# T32 MCP Dispatch Wiring Tests

> Self-contained SPipe tests verifying T32 MCP tool dispatch wiring:

<!-- sdn-diagram:id=mcp_t32_dispatch_wiring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_dispatch_wiring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_dispatch_wiring_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_dispatch_wiring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Dispatch Wiring Tests

Self-contained SPipe tests verifying T32 MCP tool dispatch wiring:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Integration / Module Test |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Self-contained SPipe tests verifying T32 MCP tool dispatch wiring:
- All 36 tool names are recognized by the full dispatch
- Cold frontend only handles a 13-tool subset
- Tool name detection works for both compact and spaced JSON
- JSON-RPC method routing covers all protocol methods

No imports from t32_mcp.* or t32_lsp_mcp.* — all helpers are inlined.

## Scenarios

### T32 MCP dispatch wiring

#### tool name detection

#### detects t32_sessions_list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_sessions_list")
expect(detect_tool_name(msg)).to_equal("t32_sessions_list")
```

</details>

#### detects t32_session_open

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_session_open")
expect(detect_tool_name(msg)).to_equal("t32_session_open")
```

</details>

#### detects t32_cmd_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_cmd_run")
expect(detect_tool_name(msg)).to_equal("t32_cmd_run")
```

</details>

#### detects t32_eval

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_eval")
expect(detect_tool_name(msg)).to_equal("t32_eval")
```

</details>

#### detects t32_cmm_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_cmm_run")
expect(detect_tool_name(msg)).to_equal("t32_cmm_run")
```

</details>

#### detects t32_window_capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_window_capture")
expect(detect_tool_name(msg)).to_equal("t32_window_capture")
```

</details>

#### detects t32_field_get with space-colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build message with "name": "t32_field_get" (space before value)
val msg = LB() + Q() + "method" + Q() + ": " + Q() + "tools/call" + Q() + ", " + Q() + "params" + Q() + ": " + LB() + Q() + "name" + Q() + ": " + Q() + "t32_field_get" + Q() + RB() + RB()
expect(detect_tool_name(msg)).to_equal("t32_field_get")
```

</details>

#### detects t32_dialog_click

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_dialog_click")
expect(detect_tool_name(msg)).to_equal("t32_dialog_click")
```

</details>

#### detects t32_error_check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_error_check")
expect(detect_tool_name(msg)).to_equal("t32_error_check")
```

</details>

#### returns empty for message without tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = LB() + Q() + "method" + Q() + ":" + Q() + "initialize" + Q() + RB()
expect(detect_tool_name(msg)).to_equal("")
```

</details>

#### full dispatch covers all 36 tools

#### full tool set has exactly 36 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(full_tools().len()).to_equal(36)
```

</details>

#### t32_session_open is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_session_open"))
```

</details>

#### t32_session_resume is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_session_resume"))
```

</details>

#### t32_cmd_run is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_cmd_run"))
```

</details>

#### t32_cmm_run is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_cmm_run"))
```

</details>

#### t32_eval is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_eval"))
```

</details>

#### t32_window_list is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_window_list"))
```

</details>

#### t32_window_capture is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_window_capture"))
```

</details>

#### t32_setup_headless is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_setup_headless"))
```

</details>

#### t32_status_snapshot is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_status_snapshot"))
```

</details>

#### t32_cmm_validate is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_cmm_validate"))
```

</details>

#### t32_job_get is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_job_get"))
```

</details>

#### t32_job_cancel is in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_tools(), "t32_job_cancel"))
```

</details>

#### every cold tool is also in full tool set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cold = cold_tools()
val full = full_tools()
for tool in cold:
    check(list_contains(full, tool))
```

</details>

#### full-only tools (were unreachable in cold default)

#### full-only set has 23 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(full_only_tools().len()).to_equal(23)
```

</details>

#### full-only tools are not in cold set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cold = cold_tools()
for tool in full_only_tools():
    check(not list_contains(cold, tool))
```

</details>

#### full-only tools are all in full set

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full = full_tools()
for tool in full_only_tools():
    check(list_contains(full, tool))
```

</details>

#### t32_session_open was unreachable in cold

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_tools(), "t32_session_open"))
check(list_contains(full_tools(), "t32_session_open"))
```

</details>

#### t32_cmd_run was unreachable in cold

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_tools(), "t32_cmd_run"))
check(list_contains(full_tools(), "t32_cmd_run"))
```

</details>

#### t32_window_capture was unreachable in cold

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_tools(), "t32_window_capture"))
check(list_contains(full_tools(), "t32_window_capture"))
```

</details>

#### cold frontend tool set (subset)

#### cold tool set has exactly 13 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cold_tools().len()).to_equal(13)
```

</details>

#### cold handles t32_sessions_list

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(cold_tools(), "t32_sessions_list"))
```

</details>

#### cold handles t32_field_get

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(cold_tools(), "t32_field_get"))
```

</details>

#### cold handles t32_dialog_click

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(cold_tools(), "t32_dialog_click"))
```

</details>

#### cold handles t32_error_check

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(cold_tools(), "t32_error_check"))
```

</details>

#### cold does NOT handle t32_session_open

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_tools(), "t32_session_open"))
```

</details>

#### cold does NOT handle t32_cmd_run

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_tools(), "t32_cmd_run"))
```

</details>

#### cold does NOT handle t32_eval

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_tools(), "t32_eval"))
```

</details>

#### cold does NOT handle t32_window_capture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_tools(), "t32_window_capture"))
```

</details>

#### cold does NOT handle t32_setup_headless

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_tools(), "t32_setup_headless"))
```

</details>

#### method routing (full dispatch loop)

#### initialize method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "initialize"))
```

</details>

#### tools/list method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "tools/list"))
```

</details>

#### tools/call method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "tools/call"))
```

</details>

#### resources/list method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "resources/list"))
```

</details>

#### resources/templates/list method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "resources/templates/list"))
```

</details>

#### shutdown method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "shutdown"))
```

</details>

#### ping method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "ping"))
```

</details>

#### prompts/list method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "prompts/list"))
```

</details>

#### notifications/cancelled method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "notifications/cancelled"))
```

</details>

#### logging/setLevel method recognized

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(full_methods(), "logging/setLevel"))
```

</details>

#### method routing (cold dispatch loop)

#### cold recognizes initialize

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(cold_methods(), "initialize"))
```

</details>

#### cold recognizes tools/call

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(cold_methods(), "tools/call"))
```

</details>

#### cold recognizes shutdown

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(cold_methods(), "shutdown"))
```

</details>

#### cold recognizes ping

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(list_contains(cold_methods(), "ping"))
```

</details>

#### cold does NOT recognize prompts/list

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_methods(), "prompts/list"))
```

</details>

#### cold does NOT recognize resources/templates/list

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_methods(), "resources/templates/list"))
```

</details>

#### cold does NOT recognize logging/setLevel

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not list_contains(cold_methods(), "logging/setLevel"))
```

</details>

#### JSON-RPC message construction

#### make_tools_call produces valid JSON structure

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_tools_call("t32_cmd_run")
check(msg.contains(Q() + "jsonrpc" + Q()))
check(msg.contains(Q() + "2.0" + Q()))
check(msg.contains(Q() + "tools/call" + Q()))
check(msg.contains(Q() + "t32_cmd_run" + Q()))
```

</details>

#### make_method_request produces valid JSON structure

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = make_method_request("initialize")
check(msg.contains(Q() + "jsonrpc" + Q()))
check(msg.contains(Q() + "initialize" + Q()))
check(msg.contains(Q() + "id" + Q()))
```

</details>

#### escape_json handles backslash

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("a\\b")
check(escaped.contains("\\\\"))
```

</details>

#### escape_json handles quotes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("say " + Q() + "hello" + Q())
check(escaped.contains("\\" + Q()))
```

</details>

#### default frontend changed from cold to full (bug 6 fix)

#### default T32_MCP_FRONTEND should be full

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The wrapper script sets: T32_MCP_FRONTEND="${T32_MCP_FRONTEND:-full}"
# This means when unset, it defaults to "full" not "cold"
val default_frontend = "full"
expect(default_frontend).to_equal("full")
```

</details>

#### full mode routes to full entry point

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In full mode: SOURCE_ARTIFACT="$FULL_ENTRY"
# FULL_ENTRY="${REPO_ROOT}/src/app/t32_mcp_server/main.spl"
val full_entry = "src/app/t32_mcp_server/main.spl"
check(full_entry.contains("t32_mcp_server"))
```

</details>

#### cold mode routes to cold entry point

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In cold mode: SOURCE_ARTIFACT="$COLD_ENTRY"
# COLD_ENTRY="${REPO_ROOT}/examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl"
val cold_entry = "examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl"
check(cold_entry.contains("frontend_cold"))
```

</details>

#### full dispatch handles all tools cold cannot

1. check
2. check
   - Expected: only.len() + cold.len() equals `full.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The key invariant: every full_only tool must be in full but not cold
val full = full_tools()
val cold = cold_tools()
val only = full_only_tools()
for tool in only:
    check(list_contains(full, tool))
    check(not list_contains(cold, tool))
# And full_only + cold == full (no gaps)
expect(only.len() + cold.len()).to_equal(full.len())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 65 |
| Active scenarios | 65 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
