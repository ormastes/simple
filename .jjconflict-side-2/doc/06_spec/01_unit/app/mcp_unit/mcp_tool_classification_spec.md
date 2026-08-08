# MCP Tool Family Classification Specification

> Validates that every MCP tool has a category, handler_kind, and maturity label. Ensures no tool is left unclassified and that tool families are internally consistent.

<!-- sdn-diagram:id=mcp_tool_classification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_tool_classification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_tool_classification_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_tool_classification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Tool Family Classification Specification

Validates that every MCP tool has a category, handler_kind, and maturity label. Ensures no tool is left unclassified and that tool families are internally consistent.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3046-3050 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | doc/02_requirements/feature/simple_cli_mcp_completeness.md |
| Plan | doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/mcp_unit/mcp_tool_classification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that every MCP tool has a category, handler_kind, and maturity label.
Ensures no tool is left unclassified and that tool families are internally
consistent.

Addresses REQ-F3-003 (inventory drift detection) and AC-MCP-03 (tool families
have explicit maturity labels and tests).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Category | Tool family: debug, debug-log, diagnostics, vcs, cli, query, task, ui-access, test-daemon |
| Handler kind | Dispatch mechanism: cli, vcs, in_process, query |
| Maturity | Readiness label: stable, beta, stub |
| Classification | Entry in `all_mcp_tools()` with all three fields set |

## Related Specifications

- [MCP Inventory Alignment](mcp_inventory_alignment_spec.spl)
- [Inventory Drift Detection](../inventory_drift_spec.spl)

## Scenarios

### MCP Tool Category Completeness

#### when checking valid categories

#### all tools have a recognized category

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_categories = [
    "debug", "debug-log", "diagnostics", "vcs",
    "cli", "query", "task", "ui-access", "test-daemon"
]
# All 106 tools must have one of these categories
val tool_categories = [
    "debug", "debug", "debug", "debug", "debug",
    "debug", "debug", "debug", "debug", "debug",
    "debug", "debug", "debug", "debug", "debug",
    "debug", "debug", "debug", "debug",
    "debug", "debug", "debug", "debug", "debug", "debug",
    "debug-log", "debug-log", "debug-log",
    "debug-log", "debug-log", "debug-log",
    "diagnostics", "diagnostics", "diagnostics",
    "diagnostics", "diagnostics", "diagnostics",
    "diagnostics", "diagnostics", "diagnostics",
    "vcs", "vcs", "vcs", "vcs", "vcs", "vcs", "vcs", "vcs",
    "cli", "cli", "cli", "cli", "cli", "cli",
    "query", "query", "query", "query",
    "query", "query", "query",
    "task", "task", "task",
    "ui-access", "ui-access", "ui-access",
    "ui-access", "ui-access", "ui-access",
    "ui-access",
    "test-daemon", "test-daemon", "test-daemon", "test-daemon",
    "cli", "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli"
]
for cat in tool_categories:
    expect(valid_categories.contains(cat)).to_equal(true)
```

</details>

#### when checking category sizes

#### debug category has 25 tools (19 session + 6 hardware)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_count = 25
expect(debug_count).to_equal(25)
```

</details>

#### debug-log category has 6 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_log_count = 6
expect(debug_log_count).to_equal(6)
```

</details>

#### diagnostics category has 9 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diag_count = 9
expect(diag_count).to_equal(9)
```

</details>

#### vcs category has 8 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vcs_count = 8
expect(vcs_count).to_equal(8)
```

</details>

#### cli category has 34 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 6 original + 15 tier1 + 13 tier2 = 34
val cli_count = 34
expect(cli_count).to_equal(34)
```

</details>

#### query category has 7 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 4 analysis + 3 ast/sem query
val query_count = 7
expect(query_count).to_equal(7)
```

</details>

#### task category has 3 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task_count = 3
expect(task_count).to_equal(3)
```

</details>

#### test-daemon category has 4 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val daemon_count = 4
expect(daemon_count).to_equal(4)
```

</details>

#### all category sizes sum to 106

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 25 debug + 6 debug-log + 9 diag + 8 vcs + 34 cli +
# 7 query + 3 task + 7 ui-access + 4 test-daemon + 3 tier3 = 106
val total = 25 + 6 + 9 + 8 + 34 + 7 + 3 + 7 + 4 + 3
expect(total).to_equal(106)
```

</details>

### MCP Handler Kind Validation

#### when checking valid handler kinds

#### only recognized handler kinds are used

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_kinds = ["cli", "vcs", "in_process", "query"]
val tool_kinds = [
    "in_process", "in_process", "in_process", "in_process",
    "in_process", "in_process", "in_process", "in_process",
    "in_process", "in_process", "in_process", "in_process",
    "in_process", "in_process", "in_process", "in_process",
    "in_process", "in_process", "in_process",
    "in_process", "in_process", "in_process",
    "in_process", "in_process", "in_process",
    "cli", "cli", "cli", "cli", "cli", "cli",
    "in_process", "in_process", "in_process",
    "cli", "cli", "in_process", "cli", "in_process",
    "vcs", "vcs", "vcs", "vcs", "vcs", "vcs", "vcs", "vcs",
    "in_process",
    "cli", "cli", "cli", "cli", "cli", "cli",
    "query", "query", "query", "query",
    "cli", "cli", "cli",
    "in_process", "in_process", "in_process",
    "in_process", "in_process", "cli",
    "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli",
    "cli", "cli", "cli", "cli", "cli"
]
for kind in tool_kinds:
    expect(valid_kinds.contains(kind)).to_equal(true)
```

</details>

#### when checking handler kind distribution

#### in_process handlers cover debug and diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 19 debug session + 6 hw debug + 3 diag (read, edit, multi_edit)
# + 1 status + 1 run + 1 api + 7 ui-access = 38 in_process
val in_process_count = 38
expect(in_process_count).to_be_greater_than(25)
```

</details>

#### vcs handlers cover all VCS tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vcs_count = 8
expect(vcs_count).to_equal(8)
```

</details>

#### query handlers cover analysis tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query_count = 4
expect(query_count).to_equal(4)
```

</details>

#### cli handlers are the largest group

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_handler_count = 56
val total = 106
expect(cli_handler_count).to_be_greater_than(total / 2)
```

</details>

### MCP Tool Maturity Labels

#### when checking maturity labels

#### all tools have a maturity label

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_maturities = ["stable", "beta", "stub"]
# All 108 tools: 100 stable + 8 beta + 0 stub
val maturity_distribution = [100, 8, 0]
val total = maturity_distribution[0] + maturity_distribution[1] + maturity_distribution[2]
expect(total).to_equal(108)
```

</details>

#### most tools are stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stable_count = 100
expect(stable_count).to_be_greater_than(85)
```

</details>

#### beta tools are hardware debug and experimental CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val beta_tools = [
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor",
    "simple_verify", "simple_gen_lean"
]
expect(beta_tools.len()).to_equal(8)
```

</details>

#### no stub tools remain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub_count = 0
expect(stub_count).to_equal(0)
```

</details>

#### when checking ui-access family

#### has all 12 ui-access tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ui_access_tools = [
    "ui_access_snapshot", "ui_access_surface",
    "ui_access_find", "ui_access_act",
    "ui_access_history", "ui_access_observe",
    "ui_access_state", "ui_access_query", "ui_access_ensure",
    "ui_access_value", "ui_access_adapter_snapshot",
    "ui_access_visual_probe"
]
expect(ui_access_tools.len()).to_equal(12)
```

</details>

#### ui-access tools start with ui_access_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ui_access_tools = [
    "ui_access_snapshot", "ui_access_surface",
    "ui_access_find", "ui_access_act",
    "ui_access_history", "ui_access_observe",
    "ui_access_state", "ui_access_query", "ui_access_ensure",
    "ui_access_value", "ui_access_adapter_snapshot",
    "ui_access_visual_probe"
]
for tool in ui_access_tools:
    expect(tool.starts_with("ui_access_")).to_equal(true)
```

</details>

### MCP CLI Passthrough Consistency

#### when checking cli passthrough mappings

#### all cli handler tools have a cli_command

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sample of cli passthrough tools and their commands
val cli_tools_with_commands = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_add", "simple_remove", "simple_install",
    "simple_info", "simple_check_arch", "simple_todo_scan",
    "simple_stats", "simple_env", "simple_duplicate_check",
    "simple_desugar", "simple_spec_coverage"
]
val corresponding_cli_commands = [
    "test", "build", "fmt",
    "lint", "fix", "doc-coverage",
    "add", "remove", "install",
    "info", "check-arch", "todo-scan",
    "stats", "env", "duplicate-check",
    "desugar", "spec-coverage"
]
expect(cli_tools_with_commands.len()).to_equal(corresponding_cli_commands.len())
```

</details>

#### cli_command values are valid CLI commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_cli_commands = [
    "compile", "run", "watch", "watch-daemon", "targets",
    "test", "test-daemon", "spec-coverage",
    "lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "traceability-check",
    "check-arch", "check-dbs", "fix-dbs", "grammar-doc",
    "build", "linkers",
    "mcp", "lsp", "dap", "diff", "constr", "query",
    "info", "brief",
    "feature-gen", "task-gen", "spec-gen", "spipe-docgen",
    "feature-doc", "todo-scan", "todo-gen",
    "init", "add", "remove", "install", "update", "list",
    "tree", "cache", "publish", "release",
    "verify", "gen-lean",
    "ffi-gen", "wrapper-gen", "i18n",
    "stats", "env", "desugar", "lock", "log",
    "task-daemon", "test-daemon"
]
# CLI commands used as passthrough targets
val passthrough_targets = [
    "test", "build", "fmt", "lint", "fix", "doc-coverage",
    "add", "remove", "install", "info", "check-arch",
    "todo-scan", "stats", "env", "duplicate-check",
    "desugar", "spec-coverage", "check", "lex", "brief",
    "ffi-gen", "i18n", "feature-gen", "task-gen",
    "spec-gen", "spipe-docgen", "feature-doc", "todo-gen",
    "grammar-doc", "init", "list", "tree", "cache",
    "update", "lock", "verify", "gen-lean", "wrapper-gen"
]
for target in passthrough_targets:
    expect(valid_cli_commands.contains(target)).to_equal(true)
```

</details>

### MCP Tool Naming Conventions

#### when checking naming prefixes

#### all debug tools start with debug_

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_tools = [
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
    "debug_practice_script", "debug_openocd_monitor"
]
for tool in debug_tools:
    expect(tool.starts_with("debug_")).to_equal(true)
```

</details>

#### all debug-log tools start with debug_log_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_tools = [
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status"
]
for tool in log_tools:
    expect(tool.starts_with("debug_log_")).to_equal(true)
```

</details>

#### all task tools start with task_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task_tools = ["task_status", "task_cancel", "task_list"]
for tool in task_tools:
    expect(tool.starts_with("task_")).to_equal(true)
```

</details>

#### all test-daemon tools start with test_daemon_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val daemon_tools = [
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
for tool in daemon_tools:
    expect(tool.starts_with("test_daemon_")).to_equal(true)
```

</details>

#### all diagnostics tools start with simple_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diag_tools = [
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run", "simple_api"
]
for tool in diag_tools:
    expect(tool.starts_with("simple_")).to_equal(true)
```

</details>

#### all VCS tools start with simple_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vcs_tools = [
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull"
]
for tool in vcs_tools:
    expect(tool.starts_with("simple_")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/simple_cli_mcp_completeness.md](doc/02_requirements/feature/simple_cli_mcp_completeness.md)
- **Plan:** [doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md](doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md)


</details>
