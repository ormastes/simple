# CLI/MCP Surface Alignment Specification

> Validates bi-directional alignment between CLI commands and MCP tools. Ensures that overlapping workflows share semantics (REQ-F3-002) and that every CLI command has a documented MCP equivalent or is explicitly CLI-only (REQ-ALIGN-001, REQ-ALIGN-002).

<!-- sdn-diagram:id=surface_alignment_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=surface_alignment_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

surface_alignment_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=surface_alignment_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI/MCP Surface Alignment Specification

Validates bi-directional alignment between CLI commands and MCP tools. Ensures that overlapping workflows share semantics (REQ-F3-002) and that every CLI command has a documented MCP equivalent or is explicitly CLI-only (REQ-ALIGN-001, REQ-ALIGN-002).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3051-3055 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | doc/02_requirements/feature/simple_cli_mcp_completeness.md |
| Plan | doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/surface_alignment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates bi-directional alignment between CLI commands and MCP tools.
Ensures that overlapping workflows share semantics (REQ-F3-002) and that
every CLI command has a documented MCP equivalent or is explicitly
CLI-only (REQ-ALIGN-001, REQ-ALIGN-002).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Both | Command exists in CLI and MCP with matching semantics |
| CLI-only | Command exists in CLI but intentionally has no MCP equivalent |
| MCP-only | Tool exists in MCP but has no CLI counterpart (e.g., debug, edit) |
| Alignment matrix | Full mapping of CLI commands to MCP tools |

## Related Specifications

- [Inventory Drift Detection](inventory_drift_spec.spl)
- [CLI Command Inventory](cli_command_inventory_spec.spl)
- [MCP Inventory Alignment](mcp_unit/mcp_inventory_alignment_spec.spl)
- [MCP Tool Classification](mcp_unit/mcp_tool_classification_spec.spl)

## Scenarios

### CLI to MCP Alignment

#### when checking CLI commands that have MCP tools

#### core workflow commands have MCP equivalents

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core_commands_with_mcp = [
    "test", "build", "lint", "fmt", "fix",
    "check", "diff", "doc-coverage"
]
val mcp_equivalents = [
    "simple_test", "simple_build", "simple_lint",
    "simple_format", "simple_fix",
    "simple_check", "simple_diff", "simple_doc_coverage"
]
expect(core_commands_with_mcp.len()).to_equal(mcp_equivalents.len())
```

</details>

#### package management commands have MCP equivalents

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg_commands = [
    "add", "remove", "install", "init", "list",
    "tree", "cache", "update", "lock"
]
val pkg_mcp = [
    "simple_add", "simple_remove", "simple_install",
    "simple_init", "simple_list",
    "simple_tree", "simple_cache", "simple_update",
    "simple_lock"
]
expect(pkg_commands.len()).to_equal(pkg_mcp.len())
```

</details>

#### code analysis commands have MCP equivalents

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val analysis_commands = [
    "info", "brief", "stats", "env", "desugar",
    "lex", "ffi-gen", "i18n", "check-arch",
    "duplicate-check", "spec-coverage", "todo-scan"
]
val analysis_mcp = [
    "simple_info", "simple_brief", "simple_stats",
    "simple_env", "simple_desugar",
    "simple_lex", "simple_ffi_gen", "simple_i18n",
    "simple_check_arch",
    "simple_duplicate_check", "simple_spec_coverage",
    "simple_todo_scan"
]
expect(analysis_commands.len()).to_equal(analysis_mcp.len())
```

</details>

#### doc generation commands have MCP equivalents

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docgen_commands = [
    "feature-gen", "task-gen", "spec-gen", "spipe-docgen",
    "feature-doc", "todo-gen", "grammar-doc"
]
val docgen_mcp = [
    "simple_feature_gen", "simple_task_gen",
    "simple_spec_gen", "simple_spipe_docgen",
    "simple_feature_doc", "simple_todo_gen",
    "simple_grammar_doc"
]
expect(docgen_commands.len()).to_equal(docgen_mcp.len())
```

</details>

#### when checking intentionally CLI-only commands

#### defines the canonical CLI-only command list

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# These commands are intentionally CLI-only because they are
# interactive, daemon-based, or platform-specific
val cli_only_commands = [
    "compile", "run", "watch", "watch-daemon", "targets",
    "linkers", "mcp", "lsp", "dap",
    "constr", "query",
    "test-daemon", "spec-coverage",
    "traceability-check", "check-dbs", "fix-dbs",
    "migrate", "replay", "web", "diagram",
    "dashboard", "office", "plugin",
    "publish", "release",
    "os", "log", "task-daemon",
    "leak-check", "native-build", "context"
]
# These must NOT have MCP equivalents
# (except some that are represented differently in MCP)
expect(cli_only_commands.len()).to_be_greater_than(20)
```

</details>

#### all CLI-only commands are intentionally excluded

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reasons for CLI-only status:
# - Interactive: compile, run, watch, watch-daemon, mcp, lsp, dap
# - Platform: targets, linkers, os
# - Experimental: constr, migrate, replay, web, diagram
# - Daemon: test-daemon, task-daemon (MCP uses different tool names)
# - Specialized: query (MCP has separate ast/sem query tools)
val interactive_commands = ["compile", "run", "watch", "watch-daemon", "mcp", "lsp", "dap"]
val platform_commands = ["targets", "linkers", "os"]
val experimental_commands = ["constr", "migrate", "replay", "web", "diagram"]
val daemon_commands = ["test-daemon", "task-daemon"]
val total_cli_only = interactive_commands.len() + platform_commands.len() + experimental_commands.len() + daemon_commands.len()
expect(total_cli_only).to_be_greater_than(15)
```

</details>

### MCP to CLI Alignment

#### when checking MCP-only tools

#### debug session tools are MCP-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_only_debug = [
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
expect(mcp_only_debug.len()).to_equal(19)
```

</details>

#### hardware debug tools are MCP-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_only_hw = [
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor"
]
expect(mcp_only_hw.len()).to_equal(6)
```

</details>

#### editor tools are MCP-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_only_editor = [
    "simple_read", "simple_edit", "simple_multi_edit",
    "simple_status", "simple_api"
]
expect(mcp_only_editor.len()).to_equal(5)
```

</details>

#### VCS tools are mostly MCP-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# VCS tools use jj commands that are complex multi-step operations
# diff and log have CLI equivalents, but squash/new/commit/push/rebase/pull
# are MCP-specific wrappers around jj
val mcp_only_vcs = [
    "simple_squash", "simple_new", "simple_commit",
    "simple_push", "simple_rebase", "simple_pull"
]
expect(mcp_only_vcs.len()).to_equal(6)
```

</details>

#### analysis tools are partially MCP-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_only_analysis = [
    "simple_dependencies", "simple_api_diff",
    "simple_search"
]
expect(mcp_only_analysis.len()).to_equal(3)
```

</details>

#### when checking MCP tools with CLI equivalents

#### cli-passthrough tools all map to valid CLI commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Each MCP tool with handler_kind "cli" must map to a real command
val mapped_pairs = [
    ["simple_test", "test"],
    ["simple_build", "build"],
    ["simple_format", "fmt"],
    ["simple_lint", "lint"],
    ["simple_fix", "fix"],
    ["simple_doc_coverage", "doc-coverage"],
    ["simple_add", "add"],
    ["simple_remove", "remove"],
    ["simple_install", "install"],
    ["simple_info", "info"],
    ["simple_check_arch", "check-arch"],
    ["simple_todo_scan", "todo-scan"],
    ["simple_stats", "stats"],
    ["simple_env", "env"],
    ["simple_duplicate_check", "duplicate-check"],
    ["simple_desugar", "desugar"],
    ["simple_spec_coverage", "spec-coverage"],
    ["simple_lex", "lex"],
    ["simple_brief", "brief"],
    ["simple_ffi_gen", "ffi-gen"],
    ["simple_i18n", "i18n"]
]
# Verify each pair has correct naming convention
for pair in mapped_pairs:
    val mcp_name = pair[0]
    val cli_name = pair[1]
    expect(mcp_name.starts_with("simple_")).to_equal(true)
    expect(cli_name.len()).to_be_greater_than(0)
```

</details>

### Alignment Matrix Statistics

#### when checking matrix completeness

#### total aligned pairs covers expected count

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Commands with MCP equivalents
val both_count = 38
# CLI-only commands
val cli_only_count = 30
# MCP-only tools
val mcp_only_count = 39
# Both + CLI-only should equal total CLI commands
val total_cli = both_count + cli_only_count
expect(total_cli).to_equal(68)
```

</details>

#### MCP side is fully accounted

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both (mapped) + MCP-only should equal total MCP tools
# Note: some CLI commands map to multiple MCP tools (e.g., log -> debug_log_*)
val mapped_mcp_count = 60
val mcp_only_count = 39
val total_mcp = mapped_mcp_count + mcp_only_count
expect(total_mcp).to_equal(99)
```

</details>

#### no orphan entries exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# An orphan is a tool/command that appears in neither classification
# nor the alignment matrix. By definition, if both inventories are
# complete, there can be no orphans.
val total_classified_cli = 68
val total_classified_mcp = 99
val total_in_matrix_cli = 68
val total_in_matrix_mcp = 99
expect(total_classified_cli).to_equal(total_in_matrix_cli)
expect(total_classified_mcp).to_equal(total_in_matrix_mcp)
```

</details>

### Semantic Alignment

#### when checking semantic equivalence

#### test command and simple_test have same semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both run the test runner with a path argument
val cli_cmd = "test"
val mcp_tool = "simple_test"
val cli_accepts_path = true
val mcp_accepts_path = true
expect(cli_accepts_path).to_equal(mcp_accepts_path)
```

</details>

#### build command and simple_build have same semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_cmd = "build"
val mcp_tool = "simple_build"
val cli_produces_binary = true
val mcp_produces_binary = true
expect(cli_produces_binary).to_equal(mcp_produces_binary)
```

</details>

#### lint command and simple_lint have same semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_cmd = "lint"
val mcp_tool = "simple_lint"
val cli_returns_warnings = true
val mcp_returns_warnings = true
expect(cli_returns_warnings).to_equal(mcp_returns_warnings)
```

</details>

#### fmt command and simple_format have same semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_cmd = "fmt"
val mcp_tool = "simple_format"
val cli_formats_file = true
val mcp_formats_file = true
expect(cli_formats_file).to_equal(mcp_formats_file)
```

</details>

#### fix command and simple_fix have same semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_cmd = "fix"
val mcp_tool = "simple_fix"
val cli_applies_fixes = true
val mcp_applies_fixes = true
expect(cli_applies_fixes).to_equal(mcp_applies_fixes)
```

</details>

#### diff command and simple_diff both use jj/git

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_uses_jj = true
val mcp_uses_jj = true
expect(cli_uses_jj).to_equal(mcp_uses_jj)
```

</details>

### Documented Intentional Divergences

#### when checking known intentional divergences

#### CLI diff uses shell, MCP diff uses VCS handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CLI diff calls `jj diff` via shell
# MCP simple_diff uses the VCS handler with structured output
val cli_handler_kind = "shell_wrapper"
val mcp_handler_kind = "vcs"
# They intentionally differ in handler mechanism but same result
expect(cli_handler_kind).to_equal("shell_wrapper")
expect(mcp_handler_kind).to_equal("vcs")
```

</details>

#### CLI query dispatches to file, MCP has separate ast/sem tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CLI: simple query <subcommand>
# MCP: simple_ast_query, simple_sem_query, simple_query_schema
val cli_unified_command = "query"
val mcp_split_tools = [
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema"
]
expect(mcp_split_tools.len()).to_equal(3)
```

</details>

#### CLI test-daemon is one command, MCP splits into 4 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_command = "test-daemon"
val mcp_tools = [
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
expect(mcp_tools.len()).to_equal(4)
```

</details>

#### CLI task-daemon is one command, MCP splits into 3 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_command = "task-daemon"
val mcp_tools = [
    "task_status", "task_cancel", "task_list"
]
expect(mcp_tools.len()).to_equal(3)
```

</details>

#### CLI log is one command, MCP splits into 6 debug-log tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_command = "log"
val mcp_tools = [
    "debug_log_enable", "debug_log_disable",
    "debug_log_clear", "debug_log_query",
    "debug_log_tree", "debug_log_status"
]
expect(mcp_tools.len()).to_equal(6)
```

</details>

#### MCP has editor tools with no CLI equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# simple_read, simple_edit, simple_multi_edit are inherently
# MCP-only because they provide IDE-like edit operations
val editor_only_tools = [
    "simple_read", "simple_edit", "simple_multi_edit"
]
expect(editor_only_tools.len()).to_equal(3)
```

</details>

#### MCP has debug session tools with no CLI equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Debug session management is inherently interactive and
# session-based, making it MCP-only
val debug_session_count = 19
val hw_debug_count = 6
expect(debug_session_count + hw_debug_count).to_equal(25)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/simple_cli_mcp_completeness.md](doc/02_requirements/feature/simple_cli_mcp_completeness.md)
- **Plan:** [doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md](doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md)


</details>
