# Mcp T32 Dispatch Wiring Specification

> Tests covering T32 MCP dispatch wiring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Dispatch Wiring Specification

## Scenarios

### T32 MCP dispatch wiring

#### tool name detection

#### detects t32_sessions_list

- detects t32_sessions_list
   - Expected: detect_tool_name(msg) equals `t32_sessions_list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_sessions_list")
val msg = make_tools_call("t32_sessions_list")
expect(detect_tool_name(msg)).to_equal("t32_sessions_list")
```

</details>

#### detects t32_session_open

- detects t32_session_open
   - Expected: detect_tool_name(msg) equals `t32_session_open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_session_open")
val msg = make_tools_call("t32_session_open")
expect(detect_tool_name(msg)).to_equal("t32_session_open")
```

</details>

#### detects t32_cmd_run

- detects t32_cmd_run
   - Expected: detect_tool_name(msg) equals `t32_cmd_run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_cmd_run")
val msg = make_tools_call("t32_cmd_run")
expect(detect_tool_name(msg)).to_equal("t32_cmd_run")
```

</details>

#### detects t32_eval

- detects t32_eval
   - Expected: detect_tool_name(msg) equals `t32_eval`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_eval")
val msg = make_tools_call("t32_eval")
expect(detect_tool_name(msg)).to_equal("t32_eval")
```

</details>

#### detects t32_cmm_run

- detects t32_cmm_run
   - Expected: detect_tool_name(msg) equals `t32_cmm_run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_cmm_run")
val msg = make_tools_call("t32_cmm_run")
expect(detect_tool_name(msg)).to_equal("t32_cmm_run")
```

</details>

#### detects t32_window_capture

- detects t32_window_capture
   - Expected: detect_tool_name(msg) equals `t32_window_capture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_window_capture")
val msg = make_tools_call("t32_window_capture")
expect(detect_tool_name(msg)).to_equal("t32_window_capture")
```

</details>

#### detects t32_field_get with space-colon

- detects t32_field_get with space-colon
   - Expected: detect_tool_name(msg) equals `t32_field_get`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_field_get with space-colon")
# Build message with "name": "t32_field_get" (space before value)
val msg = LB() + Q() + "method" + Q() + ": " + Q() + "tools/call" + Q() + ", " + Q() + "params" + Q() + ": " + LB() + Q() + "name" + Q() + ": " + Q() + "t32_field_get" + Q() + RB() + RB()
expect(detect_tool_name(msg)).to_equal("t32_field_get")
```

</details>

#### detects t32_dialog_click

- detects t32_dialog_click
   - Expected: detect_tool_name(msg) equals `t32_dialog_click`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_dialog_click")
val msg = make_tools_call("t32_dialog_click")
expect(detect_tool_name(msg)).to_equal("t32_dialog_click")
```

</details>

#### detects t32_error_check

- detects t32_error_check
   - Expected: detect_tool_name(msg) equals `t32_error_check`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects t32_error_check")
val msg = make_tools_call("t32_error_check")
expect(detect_tool_name(msg)).to_equal("t32_error_check")
```

</details>

#### returns empty for message without tool name

- returns empty for message without tool name
   - Expected: detect_tool_name(msg) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for message without tool name")
val msg = LB() + Q() + "method" + Q() + ":" + Q() + "initialize" + Q() + RB()
expect(detect_tool_name(msg)).to_equal("")
```

</details>

#### full dispatch covers all 36 tools

#### full tool set has exactly 36 entries

- full tool set has exactly 36 entries
   - Expected: full_tools().len() equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full tool set has exactly 36 entries")
expect(full_tools().len()).to_equal(36)
```

</details>

#### t32_session_open is in full tool set

- t32_session_open is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_session_open is in full tool set")
check(list_contains(full_tools(), "t32_session_open"))
```

</details>

#### t32_session_resume is in full tool set

- t32_session_resume is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_session_resume is in full tool set")
check(list_contains(full_tools(), "t32_session_resume"))
```

</details>

#### t32_cmd_run is in full tool set

- t32_cmd_run is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_cmd_run is in full tool set")
check(list_contains(full_tools(), "t32_cmd_run"))
```

</details>

#### t32_cmm_run is in full tool set

- t32_cmm_run is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_cmm_run is in full tool set")
check(list_contains(full_tools(), "t32_cmm_run"))
```

</details>

#### t32_eval is in full tool set

- t32_eval is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_eval is in full tool set")
check(list_contains(full_tools(), "t32_eval"))
```

</details>

#### t32_window_list is in full tool set

- t32_window_list is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_window_list is in full tool set")
check(list_contains(full_tools(), "t32_window_list"))
```

</details>

#### t32_window_capture is in full tool set

- t32_window_capture is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_window_capture is in full tool set")
check(list_contains(full_tools(), "t32_window_capture"))
```

</details>

#### t32_setup_headless is in full tool set

- t32_setup_headless is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_setup_headless is in full tool set")
check(list_contains(full_tools(), "t32_setup_headless"))
```

</details>

#### t32_status_snapshot is in full tool set

- t32_status_snapshot is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_status_snapshot is in full tool set")
check(list_contains(full_tools(), "t32_status_snapshot"))
```

</details>

#### t32_cmm_validate is in full tool set

- t32_cmm_validate is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_cmm_validate is in full tool set")
check(list_contains(full_tools(), "t32_cmm_validate"))
```

</details>

#### t32_job_get is in full tool set

- t32_job_get is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_job_get is in full tool set")
check(list_contains(full_tools(), "t32_job_get"))
```

</details>

#### t32_job_cancel is in full tool set

- t32_job_cancel is in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_job_cancel is in full tool set")
check(list_contains(full_tools(), "t32_job_cancel"))
```

</details>

#### every cold tool is also in full tool set

- every cold tool is also in full tool set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every cold tool is also in full tool set")
val cold = cold_tools()
val full = full_tools()
for tool in cold:
    check(list_contains(full, tool))
```

</details>

#### full-only tools (were unreachable in cold default)

#### full-only set has 23 entries

- full-only set has 23 entries
   - Expected: full_only_tools().len() equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full-only set has 23 entries")
expect(full_only_tools().len()).to_equal(23)
```

</details>

#### full-only tools are not in cold set

- full-only tools are not in cold set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full-only tools are not in cold set")
val cold = cold_tools()
for tool in full_only_tools():
    check(not list_contains(cold, tool))
```

</details>

#### full-only tools are all in full set

- full-only tools are all in full set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full-only tools are all in full set")
val full = full_tools()
for tool in full_only_tools():
    check(list_contains(full, tool))
```

</details>

#### t32_session_open was unreachable in cold

- t32_session_open was unreachable in cold


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_session_open was unreachable in cold")
check(not list_contains(cold_tools(), "t32_session_open"))
check(list_contains(full_tools(), "t32_session_open"))
```

</details>

#### t32_cmd_run was unreachable in cold

- t32_cmd_run was unreachable in cold


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_cmd_run was unreachable in cold")
check(not list_contains(cold_tools(), "t32_cmd_run"))
check(list_contains(full_tools(), "t32_cmd_run"))
```

</details>

#### t32_window_capture was unreachable in cold

- t32_window_capture was unreachable in cold


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_window_capture was unreachable in cold")
check(not list_contains(cold_tools(), "t32_window_capture"))
check(list_contains(full_tools(), "t32_window_capture"))
```

</details>

#### cold frontend tool set (subset)

#### cold tool set has exactly 13 entries

- cold tool set has exactly 13 entries
   - Expected: cold_tools().len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold tool set has exactly 13 entries")
expect(cold_tools().len()).to_equal(13)
```

</details>

#### cold handles t32_sessions_list

- cold handles t32_sessions_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold handles t32_sessions_list")
check(list_contains(cold_tools(), "t32_sessions_list"))
```

</details>

#### cold handles t32_field_get

- cold handles t32_field_get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold handles t32_field_get")
check(list_contains(cold_tools(), "t32_field_get"))
```

</details>

#### cold handles t32_dialog_click

- cold handles t32_dialog_click


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold handles t32_dialog_click")
check(list_contains(cold_tools(), "t32_dialog_click"))
```

</details>

#### cold handles t32_error_check

- cold handles t32_error_check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold handles t32_error_check")
check(list_contains(cold_tools(), "t32_error_check"))
```

</details>

#### cold does NOT handle t32_session_open

- cold does NOT handle t32_session_open


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold does NOT handle t32_session_open")
check(not list_contains(cold_tools(), "t32_session_open"))
```

</details>

#### cold does NOT handle t32_cmd_run

- cold does NOT handle t32_cmd_run


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold does NOT handle t32_cmd_run")
check(not list_contains(cold_tools(), "t32_cmd_run"))
```

</details>

#### cold does NOT handle t32_eval

- cold does NOT handle t32_eval


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold does NOT handle t32_eval")
check(not list_contains(cold_tools(), "t32_eval"))
```

</details>

#### cold does NOT handle t32_window_capture

- cold does NOT handle t32_window_capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold does NOT handle t32_window_capture")
check(not list_contains(cold_tools(), "t32_window_capture"))
```

</details>

#### cold does NOT handle t32_setup_headless

- cold does NOT handle t32_setup_headless


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold does NOT handle t32_setup_headless")
check(not list_contains(cold_tools(), "t32_setup_headless"))
```

</details>

#### method routing (full dispatch loop)

#### initialize method recognized

- initialize method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initialize method recognized")
check(list_contains(full_methods(), "initialize"))
```

</details>

#### tools/list method recognized

- tools/list method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tools/list method recognized")
check(list_contains(full_methods(), "tools/list"))
```

</details>

#### tools/call method recognized

- tools/call method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tools/call method recognized")
check(list_contains(full_methods(), "tools/call"))
```

</details>

#### resources/list method recognized

- resources/list method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resources/list method recognized")
check(list_contains(full_methods(), "resources/list"))
```

</details>

#### resources/templates/list method recognized

- resources/templates/list method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resources/templates/list method recognized")
check(list_contains(full_methods(), "resources/templates/list"))
```

</details>

#### shutdown method recognized

- shutdown method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shutdown method recognized")
check(list_contains(full_methods(), "shutdown"))
```

</details>

#### ping method recognized

- ping method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ping method recognized")
check(list_contains(full_methods(), "ping"))
```

</details>

#### prompts/list method recognized

- prompts/list method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prompts/list method recognized")
check(list_contains(full_methods(), "prompts/list"))
```

</details>

#### notifications/cancelled method recognized

- notifications/cancelled method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("notifications/cancelled method recognized")
check(list_contains(full_methods(), "notifications/cancelled"))
```

</details>

#### logging/setLevel method recognized

- logging/setLevel method recognized


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logging/setLevel method recognized")
check(list_contains(full_methods(), "logging/setLevel"))
```

</details>

#### method routing (cold dispatch loop)

#### cold recognizes initialize

- cold recognizes initialize


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold recognizes initialize")
check(list_contains(cold_methods(), "initialize"))
```

</details>

#### cold recognizes tools/call

- cold recognizes tools/call


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold recognizes tools/call")
check(list_contains(cold_methods(), "tools/call"))
```

</details>

#### cold recognizes shutdown

- cold recognizes shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold recognizes shutdown")
check(list_contains(cold_methods(), "shutdown"))
```

</details>

#### cold recognizes ping

- cold recognizes ping


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold recognizes ping")
check(list_contains(cold_methods(), "ping"))
```

</details>

#### cold does NOT recognize prompts/list

- cold does NOT recognize prompts/list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold does NOT recognize prompts/list")
check(not list_contains(cold_methods(), "prompts/list"))
```

</details>

#### cold does NOT recognize resources/templates/list

- cold does NOT recognize resources/templates/list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold does NOT recognize resources/templates/list")
check(not list_contains(cold_methods(), "resources/templates/list"))
```

</details>

#### cold does NOT recognize logging/setLevel

- cold does NOT recognize logging/setLevel


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold does NOT recognize logging/setLevel")
check(not list_contains(cold_methods(), "logging/setLevel"))
```

</details>

#### JSON-RPC message construction

#### make_tools_call produces valid JSON structure

- make_tools_call produces valid JSON structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("make_tools_call produces valid JSON structure")
val msg = make_tools_call("t32_cmd_run")
check(msg.contains(Q() + "jsonrpc" + Q()))
check(msg.contains(Q() + "2.0" + Q()))
check(msg.contains(Q() + "tools/call" + Q()))
check(msg.contains(Q() + "t32_cmd_run" + Q()))
```

</details>

#### make_method_request produces valid JSON structure

- make_method_request produces valid JSON structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("make_method_request produces valid JSON structure")
val msg = make_method_request("initialize")
check(msg.contains(Q() + "jsonrpc" + Q()))
check(msg.contains(Q() + "initialize" + Q()))
check(msg.contains(Q() + "id" + Q()))
```

</details>

#### escape_json handles backslash

- escape_json handles backslash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escape_json handles backslash")
val escaped = escape_json("a\\b")
check(escaped.contains("\\\\"))
```

</details>

#### escape_json handles quotes

- escape_json handles quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escape_json handles quotes")
val escaped = escape_json("say " + Q() + "hello" + Q())
check(escaped.contains("\\" + Q()))
```

</details>

#### default frontend changed from cold to full (bug 6 fix)

#### default T32_MCP_FRONTEND should be full

- default T32_MCP_FRONTEND should be full
   - Expected: default_frontend equals `full`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default T32_MCP_FRONTEND should be full")
# The wrapper script sets: T32_MCP_FRONTEND="${T32_MCP_FRONTEND:-full}"
# This means when unset, it defaults to "full" not "cold"
val default_frontend = "full"
expect(default_frontend).to_equal("full")
```

</details>

#### full mode routes to full entry point

- full mode routes to full entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full mode routes to full entry point")
# In full mode: SOURCE_ARTIFACT="$FULL_ENTRY"
# FULL_ENTRY="${REPO_ROOT}/src/app/t32_mcp_server/main.spl"
val full_entry = "src/app/t32_mcp_server/main.spl"
check(full_entry.contains("t32_mcp_server"))
```

</details>

#### cold mode routes to cold entry point

- cold mode routes to cold entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold mode routes to cold entry point")
# In cold mode: SOURCE_ARTIFACT="$COLD_ENTRY"
# COLD_ENTRY="${REPO_ROOT}/examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl"
val cold_entry = "examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl"
check(cold_entry.contains("frontend_cold"))
```

</details>

#### full dispatch handles all tools cold cannot

- full dispatch handles all tools cold cannot
   - Expected: only.len() + cold.len() equals `full.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full dispatch handles all tools cold cannot")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 MCP dispatch wiring.
- T32 MCP dispatch wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 65 |
| Active scenarios | 65 |
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

- Canonical SPipe generation for source `407e0d12696c1df479fc3d0d697f4015296e5db331c10529a625b222aaf2e5b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `407e0d12696c1df479fc3d0d697f4015296e5db331c10529a625b222aaf2e5b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `407e0d12696c1df479fc3d0d697f4015296e5db331c10529a625b222aaf2e5b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.spl:290:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects t32_sessions_list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.spl:296:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects t32_session_open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_dispatch_wiring_spec.spl:302:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects t32_cmd_run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
