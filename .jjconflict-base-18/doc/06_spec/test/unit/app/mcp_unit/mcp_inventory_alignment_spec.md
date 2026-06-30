# MCP Inventory Alignment Specification

> Validates that every MCP tool advertised in `tools/list` has a corresponding dispatch handler, every dispatch handler has a schema, and the tool count matches the expected total (81).

<!-- sdn-diagram:id=mcp_inventory_alignment_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_inventory_alignment_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_inventory_alignment_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_inventory_alignment_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Inventory Alignment Specification

Validates that every MCP tool advertised in `tools/list` has a corresponding dispatch handler, every dispatch handler has a schema, and the tool count matches the expected total (81).

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
| Source | `test/unit/app/mcp_unit/mcp_inventory_alignment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that every MCP tool advertised in `tools/list` has a corresponding
dispatch handler, every dispatch handler has a schema, and the tool count
matches the expected total (81).

Source files:
- Schema: `src/app/mcp/main_lazy_protocol.spl` (`make_tools_list()`)
- Dispatch: `src/app/mcp/main.spl` (`dispatch_tool()`)

## Key Concepts

| Concept | Description |
|---------|-------------|
| Tool schema | JSON schema registered in `make_tools_list()` via `make_tool_schema()` |
| Dispatch handler | `if/elif tool_name ==` branch in `dispatch_tool()` |
| Orphan schema | Schema exists but no dispatch handler |
| Orphan handler | Dispatch handler exists but no schema |

## Related Specifications

- [MCP Protocol Spec](mcp_protocol_spec.spl)
- [MCP Tools Spec](mcp_tools_spec.spl)

## Scenarios

### MCP Tool Count

#### when counting registered tools

#### schema list has exactly 81 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All 81 tool names from make_tools_list() in main_lazy_protocol.spl
val schema_tools = [
    # Debug session tools (19)
    "debug_create_session", "debug_list_sessions",
    "debug_close_session", "debug_set_breakpoint",
    "debug_remove_breakpoint", "debug_continue", "debug_step",
    "debug_get_variables", "debug_stack_trace",
    "debug_evaluate", "debug_set_function_breakpoint",
    "debug_enable_breakpoint", "debug_get_source",
    "debug_watch", "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint", "debug_terminate",
    # Hardware debug tools (6)
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor",
    # Debug log tools (6)
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status",
    # Diagnostic tools (8)
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run",
    # VCS tools (7)
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    # API tool (1)
    "simple_api",
    # UI access tools (12)
    "ui_access_snapshot", "ui_access_surface",
    "ui_access_find", "ui_access_act",
    "ui_access_history", "ui_access_observe",
    "ui_access_state", "ui_access_query", "ui_access_ensure",
    "ui_access_value", "ui_access_adapter_snapshot",
    "ui_access_visual_probe",
    # CLI tools (6)
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    # Analysis tools (5)
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    # Task tools (3)
    "task_status", "task_cancel", "task_list",
    # Query tools (3)
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    # Test daemon tools (4)
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
expect(schema_tools.len()).to_equal(81)
```

</details>

#### dispatch handler has exactly 81 tool branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All 81 tool names from dispatch_tool() in main.spl
val dispatch_tools = [
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "ui_access_snapshot", "ui_access_surface",
    "ui_access_find", "ui_access_act",
    "ui_access_history", "ui_access_observe",
    "ui_access_state", "ui_access_query", "ui_access_ensure",
    "ui_access_value", "ui_access_adapter_snapshot",
    "ui_access_visual_probe",
    "debug_create_session", "debug_list_sessions",
    "debug_close_session", "debug_set_breakpoint",
    "debug_remove_breakpoint", "debug_continue", "debug_step",
    "debug_get_variables", "debug_stack_trace",
    "debug_evaluate", "debug_set_function_breakpoint",
    "debug_enable_breakpoint", "debug_get_source",
    "debug_watch", "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint", "debug_terminate",
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor",
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "task_status", "task_cancel", "task_list",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
expect(dispatch_tools.len()).to_equal(81)
```

</details>

### MCP Schema-Dispatch Alignment

#### when checking schema-to-dispatch alignment

#### every schema tool has a dispatch handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 82 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema_tools = [
    "debug_create_session", "debug_list_sessions",
    "debug_close_session", "debug_set_breakpoint",
    "debug_remove_breakpoint", "debug_continue", "debug_step",
    "debug_get_variables", "debug_stack_trace",
    "debug_evaluate", "debug_set_function_breakpoint",
    "debug_enable_breakpoint", "debug_get_source",
    "debug_watch", "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint", "debug_terminate",
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor",
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status",
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "ui_access_snapshot", "ui_access_surface",
    "ui_access_find", "ui_access_act",
    "ui_access_history", "ui_access_observe",
    "ui_access_state", "ui_access_query", "ui_access_ensure",
    "ui_access_value", "ui_access_adapter_snapshot",
    "ui_access_visual_probe",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "task_status", "task_cancel", "task_list",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
val dispatch_tools = [
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "ui_access_snapshot", "ui_access_surface",
    "ui_access_find", "ui_access_act",
    "ui_access_history", "ui_access_observe",
    "ui_access_state", "ui_access_query", "ui_access_ensure",
    "ui_access_value", "ui_access_adapter_snapshot",
    "ui_access_visual_probe",
    "debug_create_session", "debug_list_sessions",
    "debug_close_session", "debug_set_breakpoint",
    "debug_remove_breakpoint", "debug_continue", "debug_step",
    "debug_get_variables", "debug_stack_trace",
    "debug_evaluate", "debug_set_function_breakpoint",
    "debug_enable_breakpoint", "debug_get_source",
    "debug_watch", "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint", "debug_terminate",
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor",
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "task_status", "task_cancel", "task_list",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
for tool in schema_tools:
    expect(dispatch_tools.contains(tool)).to_equal(true)
```

</details>

#### every dispatch handler has a schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch_tools = [
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "debug_create_session", "debug_list_sessions",
    "debug_close_session", "debug_set_breakpoint",
    "debug_remove_breakpoint", "debug_continue", "debug_step",
    "debug_get_variables", "debug_stack_trace",
    "debug_evaluate", "debug_set_function_breakpoint",
    "debug_enable_breakpoint", "debug_get_source",
    "debug_watch", "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint", "debug_terminate",
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor",
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "task_status", "task_cancel", "task_list",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
val schema_tools = [
    "debug_create_session", "debug_list_sessions",
    "debug_close_session", "debug_set_breakpoint",
    "debug_remove_breakpoint", "debug_continue", "debug_step",
    "debug_get_variables", "debug_stack_trace",
    "debug_evaluate", "debug_set_function_breakpoint",
    "debug_enable_breakpoint", "debug_get_source",
    "debug_watch", "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint", "debug_terminate",
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor",
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status",
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "ui_access_snapshot", "ui_access_surface",
    "ui_access_find", "ui_access_act",
    "ui_access_history", "ui_access_observe",
    "ui_access_state", "ui_access_query", "ui_access_ensure",
    "ui_access_value", "ui_access_adapter_snapshot",
    "ui_access_visual_probe",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "task_status", "task_cancel", "task_list",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
for tool in dispatch_tools:
    expect(schema_tools.contains(tool)).to_equal(true)
```

</details>

### MCP Tool Family Completeness

#### when checking debug session family

#### has all 19 debug session tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_session_tools = [
    "debug_create_session", "debug_list_sessions",
    "debug_close_session", "debug_set_breakpoint",
    "debug_remove_breakpoint", "debug_continue", "debug_step",
    "debug_get_variables", "debug_stack_trace",
    "debug_evaluate", "debug_set_function_breakpoint",
    "debug_enable_breakpoint", "debug_get_source",
    "debug_watch", "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint", "debug_terminate"
]
expect(debug_session_tools.len()).to_equal(19)
```

</details>

#### when checking hardware debug family

#### has all 6 hardware debug tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hw_debug_tools = [
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor"
]
expect(hw_debug_tools.len()).to_equal(6)
```

</details>

#### when checking debug log family

#### has all 6 debug log tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_tools = [
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status"
]
expect(log_tools.len()).to_equal(6)
```

</details>

#### when checking diagnostic family

#### has all 8 diagnostic tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diag_tools = [
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run"
]
expect(diag_tools.len()).to_equal(8)
```

</details>

#### when checking VCS family

#### has all 8 VCS tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vcs_tools = [
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull"
]
expect(vcs_tools.len()).to_equal(8)
```

</details>

#### when checking CLI tools family

#### has all 6 CLI tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(cli_tools.len()).to_equal(6)
```

</details>

#### when checking analysis family

#### has all 5 analysis tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val analysis_tools = [
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search"
]
expect(analysis_tools.len()).to_equal(5)
```

</details>

#### when checking task family

#### has all 3 task tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task_tools = ["task_status", "task_cancel", "task_list"]
expect(task_tools.len()).to_equal(3)
```

</details>

#### when checking query family

#### has all 3 query tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query_tools = [
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema"
]
expect(query_tools.len()).to_equal(3)
```

</details>

#### when checking test daemon family

#### has all 4 test daemon tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val daemon_tools = [
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
expect(daemon_tools.len()).to_equal(4)
```

</details>

#### when checking API family

#### has the API tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val api_tools = ["simple_api"]
expect(api_tools.len()).to_equal(1)
```

</details>

#### when validating family totals

#### all families sum to 81

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 19 + 6 + 6 + 8 + 8 + 12 + 6 + 5 + 3 + 3 + 4 + 1
# 19 debug + 6 hw + 6 log + 8 diag + 8 vcs + 12 ui-access +
# 6 cli + 5 analysis + 3 task + 3 query + 4 daemon + 1 api = 81
expect(total).to_equal(81)
```

</details>

### MCP Protocol Method Coverage

#### when checking protocol method count

#### handles all 18 protocol method aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val protocol_methods = [
    "initialize",
    "initialized",
    "notifications/initialized",
    "shutdown",
    "tools/list",
    "tools/call",
    "resources/list",
    "resources/templates/list",
    "resources/read",
    "prompts/list",
    "prompts/get",
    "completion/complete",
    "completions/complete",
    "logging/setLevel",
    "roots/list",
    "ping",
    "notifications/cancelled",
    "notifications/roots/list_changed"
]
# Note: initialized and notifications/initialized share a branch,
# as do completion/complete and completions/complete,
# and notifications/cancelled and notifications/roots/list_changed.
expect(protocol_methods.len()).to_equal(18)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
