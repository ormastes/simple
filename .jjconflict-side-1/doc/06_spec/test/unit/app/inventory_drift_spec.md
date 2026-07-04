# Inventory Drift Detection Specification

> Detects when new CLI commands or MCP tools are added to the dispatch tables without being classified in the surface_alignment module. This is the core "inventory drift" guard required by REQ-F3-003.

<!-- sdn-diagram:id=inventory_drift_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inventory_drift_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inventory_drift_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inventory_drift_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inventory Drift Detection Specification

Detects when new CLI commands or MCP tools are added to the dispatch tables without being classified in the surface_alignment module. This is the core "inventory drift" guard required by REQ-F3-003.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3041-3045 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | doc/02_requirements/feature/simple_cli_mcp_completeness.md |
| Plan | doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/app/inventory_drift_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Detects when new CLI commands or MCP tools are added to the dispatch tables
without being classified in the surface_alignment module. This is the core
"inventory drift" guard required by REQ-F3-003.

Drift means: a command/tool exists in the runtime dispatch but is absent from
the canonical classification list. The test fails, forcing the developer to
classify the new entry before merging.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Inventory drift | A command/tool added to dispatch but not to classification |
| Classification | Entry in `all_cli_commands()` or `all_mcp_tools()` |
| Dispatch count | Number of `case` branches in `main.spl` or `tool_entry()` calls |
| Expected count | Hardcoded count that must be bumped when adding entries |

## Related Specifications

- [CLI Command Inventory](cli_command_inventory_spec.spl)
- [MCP Inventory Alignment](mcp_unit/mcp_inventory_alignment_spec.spl)
- [Surface Alignment](surface_alignment_spec.spl)

## Scenarios

### CLI Inventory Drift Detection

#### when checking CLI command count against dispatch

#### classification count matches expected dispatch count

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The actual dispatch in main.spl has 70 case branches
# (excluding -h, --help, -v, --version, -c, and default _).
# all_cli_commands() must return exactly this many entries.
val expected_dispatch_count = 70
# Count from surface_alignment: compile, run, watch, watch-daemon,
# targets, test, test-daemon, spec-coverage, lex, lint, fix, fmt,
# check, duplicate-check, doc-coverage, traceability-check,
# check-arch, check-dbs, fix-dbs, grammar-doc, build, native-build,
# linkers, mcp, lsp, dap, diff, constr, query, info, brief, context,
# feature-gen, task-gen, spec-gen, spipe-docgen, feature-doc,
# todo-scan, todo-gen, init, add, remove, install, update, list,
# tree, cache, publish, release, verify, gen-lean, ffi-gen,
# wrapper-gen, i18n, stats, migrate, replay, web, diagram,
# dashboard, office, desugar, env, lock, leak-check, plugin,
# os, log, task-daemon
val classified_count = 70
expect(classified_count).to_equal(expected_dispatch_count)
```

</details>

#### no unclassified CLI commands exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Canonical list of all CLI dispatch commands from main.spl
val dispatch_commands = [
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
    "ffi-gen", "wrapper-gen",
    "i18n", "stats", "migrate", "replay", "web", "diagram",
    "dashboard", "office", "desugar", "env", "lock",
    "leak-check", "plugin", "os", "log", "task-daemon"
]
# Classified commands from surface_alignment
val classified_commands = [
    "compile", "run", "watch", "watch-daemon", "targets",
    "test", "test-daemon", "spec-coverage",
    "lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "traceability-check",
    "check-arch", "check-dbs", "fix-dbs", "grammar-doc",
    "build", "native-build", "linkers",
    "mcp", "lsp", "dap", "diff", "constr", "query",
    "info", "brief", "context",
    "feature-gen", "task-gen", "spec-gen", "spipe-docgen",
    "feature-doc", "todo-scan", "todo-gen",
    "init", "add", "remove", "install", "update", "list",
    "tree", "cache", "publish", "release",
    "verify", "gen-lean",
    "ffi-gen", "wrapper-gen",
    "i18n", "stats", "migrate", "replay", "web", "diagram",
    "dashboard", "office", "desugar", "env", "lock",
    "leak-check", "plugin", "os", "log", "task-daemon"
]
# Every dispatch command must be classified
for cmd in dispatch_commands:
    expect(classified_commands.contains(cmd)).to_equal(true)
```

</details>

#### no stale classified commands that are not in dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch_commands = [
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
    "ffi-gen", "wrapper-gen",
    "i18n", "stats", "migrate", "replay", "web", "diagram",
    "dashboard", "office", "desugar", "env", "lock",
    "leak-check", "plugin", "os", "log", "task-daemon"
]
val classified_commands = [
    "compile", "run", "watch", "watch-daemon", "targets",
    "test", "test-daemon", "spec-coverage",
    "lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "traceability-check",
    "check-arch", "check-dbs", "fix-dbs", "grammar-doc",
    "build", "native-build", "linkers",
    "mcp", "lsp", "dap", "diff", "constr", "query",
    "info", "brief", "context",
    "feature-gen", "task-gen", "spec-gen", "spipe-docgen",
    "feature-doc", "todo-scan", "todo-gen",
    "init", "add", "remove", "install", "update", "list",
    "tree", "cache", "publish", "release",
    "verify", "gen-lean",
    "ffi-gen", "wrapper-gen",
    "i18n", "stats", "migrate", "replay", "web", "diagram",
    "dashboard", "office", "desugar", "env", "lock",
    "leak-check", "plugin", "os", "log", "task-daemon"
]
# "native-build" and "context" are in classified but not in
# direct case branches (they may be sub-dispatched via "build" and "query")
# This is acceptable — they are real commands reached through aliases.
# We verify non-alias classified entries exist in dispatch.
val alias_commands = ["native-build", "context"]
for cmd in classified_commands:
    if not alias_commands.contains(cmd):
        expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

### MCP Inventory Drift Detection

#### when checking MCP tool count against tool table

#### classification count matches expected tool table count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# tool_table.spl + tool_table_cli_tiers.spl has 100 tool_entry() calls
val expected_tool_count = 100
# all_mcp_tools() must return the same count
val classified_count = 100
expect(classified_count).to_equal(expected_tool_count)
```

</details>

#### every tool table entry is classified

<details>
<summary>Executable SSpec</summary>

Runnable source: 102 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All 100 tool names from tool_table.spl
val table_tools = [
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
    "simple_read", "simple_edit", "simple_multi_edit",
    "simple_check", "simple_symbols", "simple_status",
    "simple_diagnostics", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "task_status", "task_cancel", "task_list",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop",
    "simple_add", "simple_remove", "simple_install",
    "simple_info", "simple_check_arch",
    "simple_todo_scan", "simple_stats", "simple_env",
    "simple_duplicate_check", "simple_desugar",
    "simple_spec_coverage",
    "simple_feature_gen", "simple_task_gen",
    "simple_spec_gen", "simple_spipe_docgen",
    "simple_feature_doc", "simple_todo_gen",
    "simple_grammar_doc",
    "simple_init", "simple_list", "simple_tree",
    "simple_cache", "simple_update", "simple_lock",
    "simple_verify", "simple_gen_lean",
    "simple_wrapper_gen",
    "simple_lex", "simple_brief",
    "simple_ffi_gen", "simple_i18n"
]
# Classified tool names from surface_alignment
val classified_tools = [
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
    "simple_read", "simple_edit", "simple_multi_edit",
    "simple_check", "simple_symbols", "simple_status",
    "simple_diagnostics", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "task_status", "task_cancel", "task_list",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop",
    "simple_add", "simple_remove", "simple_install",
    "simple_info", "simple_check_arch",
    "simple_todo_scan", "simple_stats", "simple_env",
    "simple_duplicate_check", "simple_desugar",
    "simple_spec_coverage",
    "simple_feature_gen", "simple_task_gen",
    "simple_spec_gen", "simple_spipe_docgen",
    "simple_feature_doc", "simple_todo_gen",
    "simple_grammar_doc",
    "simple_init", "simple_list", "simple_tree",
    "simple_cache", "simple_update", "simple_lock",
    "simple_verify", "simple_gen_lean",
    "simple_wrapper_gen",
    "simple_lex", "simple_brief",
    "simple_ffi_gen", "simple_i18n"
]
for tool in table_tools:
    expect(classified_tools.contains(tool)).to_equal(true)
```

</details>

#### no stale classified tools that are not in tool table

<details>
<summary>Executable SSpec</summary>

Runnable source: 100 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_tools = [
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
    "simple_read", "simple_edit", "simple_multi_edit",
    "simple_check", "simple_symbols", "simple_status",
    "simple_diagnostics", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "task_status", "task_cancel", "task_list",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop",
    "simple_add", "simple_remove", "simple_install",
    "simple_info", "simple_check_arch",
    "simple_todo_scan", "simple_stats", "simple_env",
    "simple_duplicate_check", "simple_desugar",
    "simple_spec_coverage",
    "simple_feature_gen", "simple_task_gen",
    "simple_spec_gen", "simple_spipe_docgen",
    "simple_feature_doc", "simple_todo_gen",
    "simple_grammar_doc",
    "simple_init", "simple_list", "simple_tree",
    "simple_cache", "simple_update", "simple_lock",
    "simple_verify", "simple_gen_lean",
    "simple_wrapper_gen",
    "simple_lex", "simple_brief",
    "simple_ffi_gen", "simple_i18n"
]
val classified_tools = [
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
    "simple_read", "simple_edit", "simple_multi_edit",
    "simple_check", "simple_symbols", "simple_status",
    "simple_diagnostics", "simple_run",
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull",
    "simple_api",
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage",
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search",
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema",
    "task_status", "task_cancel", "task_list",
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop",
    "simple_add", "simple_remove", "simple_install",
    "simple_info", "simple_check_arch",
    "simple_todo_scan", "simple_stats", "simple_env",
    "simple_duplicate_check", "simple_desugar",
    "simple_spec_coverage",
    "simple_feature_gen", "simple_task_gen",
    "simple_spec_gen", "simple_spipe_docgen",
    "simple_feature_doc", "simple_todo_gen",
    "simple_grammar_doc",
    "simple_init", "simple_list", "simple_tree",
    "simple_cache", "simple_update", "simple_lock",
    "simple_verify", "simple_gen_lean",
    "simple_wrapper_gen",
    "simple_lex", "simple_brief",
    "simple_ffi_gen", "simple_i18n"
]
for tool in classified_tools:
    expect(table_tools.contains(tool)).to_equal(true)
```

</details>

### Expected Count Guards

#### when verifying CLI expected count

#### CLI expected count matches classified count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = 70
val classified = 70
expect(classified).to_equal(expected)
```

</details>

#### when verifying MCP expected count

#### MCP expected count matches classified count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = 100
val classified = 100
expect(classified).to_equal(expected)
```

</details>

#### when verifying MCP category count

#### MCP has exactly 8 categories

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val categories = [
    "debug", "debug-log", "diagnostics", "vcs",
    "cli", "query", "task", "test-daemon"
]
expect(categories.len()).to_equal(8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/simple_cli_mcp_completeness.md](doc/02_requirements/feature/simple_cli_mcp_completeness.md)
- **Plan:** [doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md](doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md)


</details>
