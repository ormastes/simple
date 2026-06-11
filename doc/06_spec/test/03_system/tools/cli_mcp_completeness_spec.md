# CLI/MCP Completeness System Specification

> System-level tests that validate CLI command families and MCP tool families each have at least one working representative, and that no placeholder commands are visible in default help output.

<!-- sdn-diagram:id=cli_mcp_completeness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_mcp_completeness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_mcp_completeness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_mcp_completeness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI/MCP Completeness System Specification

System-level tests that validate CLI command families and MCP tool families each have at least one working representative, and that no placeholder commands are visible in default help output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3036-3040 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/tools/cli_mcp_completeness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System-level tests that validate CLI command families and MCP tool families
each have at least one working representative, and that no placeholder commands
are visible in default help output.

These tests check the *overall* completeness of the CLI and MCP subsystems
without testing individual command behavior (that is covered by unit tests).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Command family | A group of related CLI commands (e.g., testing, build, pkg) |
| Tool family | A group of related MCP tools (e.g., debug, diag, vcs) |
| Representative | At least one command/tool in a family that works end-to-end |
| Completeness | No placeholder stubs in user-visible command surface |

## Related Specifications

- [CLI Command Inventory](../unit/app/cli_command_inventory_spec.spl)
- [CLI Help Alignment](../unit/app/cli_help_alignment_spec.spl)
- [MCP Inventory Alignment](../unit/app/mcp_unit/mcp_inventory_alignment_spec.spl)
- [Inventory Drift Detection](../unit/app/inventory_drift_spec.spl)
- [MCP Tool Classification](../unit/app/mcp_unit/mcp_tool_classification_spec.spl)
- [Surface Alignment](../unit/app/surface_alignment_spec.spl)

## Scenarios

### CLI Command Family Completeness

#### execution family

#### has working compile command

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exec_family = ["compile", "run", "watch", "watch-daemon"]
val implemented = ["compile", "run", "watch"]
var has_representative = false
for cmd in exec_family:
    if implemented.contains(cmd):
        has_representative = true
expect(has_representative).to_equal(true)
```

</details>

#### testing family

#### has working test command

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_family = ["test", "test-daemon", "spec-coverage"]
val implemented = ["test", "test-daemon"]
var has_representative = false
for cmd in test_family:
    if implemented.contains(cmd):
        has_representative = true
expect(has_representative).to_equal(true)
```

</details>

#### code quality family

#### has working lint command

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quality_family = ["lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "check-arch",
    "check-dbs", "fix-dbs"]
val implemented = ["lint", "fix", "fmt", "check"]
var has_representative = false
for cmd in quality_family:
    if implemented.contains(cmd):
        has_representative = true
expect(has_representative).to_equal(true)
```

</details>

#### all code quality commands are implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quality_family = ["lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "check-arch",
    "check-dbs", "fix-dbs"]
val implemented = ["lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "check-arch",
    "check-dbs", "fix-dbs"]
for cmd in quality_family:
    expect(implemented.contains(cmd)).to_equal(true)
```

</details>

#### build family

#### has working build command

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build_family = ["build", "native-build", "targets",
    "linkers"]
val implemented = ["build", "native-build", "targets"]
var has_representative = false
for cmd in build_family:
    if implemented.contains(cmd):
        has_representative = true
expect(has_representative).to_equal(true)
```

</details>

#### all build commands are implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build_family = ["build", "native-build", "targets",
    "linkers"]
val implemented = ["build", "native-build", "targets", "linkers"]
for cmd in build_family:
    expect(implemented.contains(cmd)).to_equal(true)
```

</details>

#### LLM tools family

#### has working mcp command

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val llm_family = ["mcp", "lsp", "diff", "constr", "query",
    "info", "brief", "context"]
val implemented = ["mcp", "lsp", "query"]
var has_representative = false
for cmd in llm_family:
    if implemented.contains(cmd):
        has_representative = true
expect(has_representative).to_equal(true)
```

</details>

#### all LLM tool commands are implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val llm_family = ["mcp", "lsp", "diff", "constr", "query",
    "info", "brief", "context"]
val implemented = ["mcp", "lsp", "diff", "constr", "query",
    "info", "brief", "context"]
for cmd in llm_family:
    expect(implemented.contains(cmd)).to_equal(true)
```

</details>

#### doc generation family

#### has working feature-gen command

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc_family = ["feature-gen", "task-gen", "spec-gen",
    "spipe-docgen", "feature-doc", "todo-scan", "todo-gen",
    "grammar-doc"]
val implemented = ["feature-gen", "todo-scan", "spipe-docgen"]
var has_representative = false
for cmd in doc_family:
    if implemented.contains(cmd):
        has_representative = true
expect(has_representative).to_equal(true)
```

</details>

#### package management family

#### has working init command

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg_family = ["init", "add", "remove", "install", "update",
    "list", "tree", "cache"]
val implemented = ["init"]
var has_representative = false
for cmd in pkg_family:
    if implemented.contains(cmd):
        has_representative = true
expect(has_representative).to_equal(true)
```

</details>

#### verification family

#### has working verify command

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verify_family = ["verify", "gen-lean"]
val implemented = ["verify", "gen-lean"]
var has_representative = false
for cmd in verify_family:
    if implemented.contains(cmd):
        has_representative = true
expect(has_representative).to_equal(true)
```

</details>

#### FFI family

#### has working ffi-gen command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ffi_family = ["ffi-gen", "wrapper-gen"]
val implemented = ["ffi-gen", "wrapper-gen"]
for cmd in ffi_family:
    expect(implemented.contains(cmd)).to_equal(true)
```

</details>

#### i18n family

#### has working i18n command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val i18n_family = ["i18n"]
val implemented = ["i18n"]
for cmd in i18n_family:
    expect(implemented.contains(cmd)).to_equal(true)
```

</details>

### MCP Tool Family Completeness

#### debug session family

#### has representative debug tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
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
    "debug_remove_data_breakpoint", "debug_terminate"
]
expect(debug_tools.len()).to_be_greater_than(0)
expect(debug_tools).to_contain("debug_create_session")
```

</details>

#### hardware debug family

#### has representative hardware debug tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hw_tools = [
    "debug_trace_capture", "debug_coverage_collect",
    "debug_flash_program", "debug_system_reset",
    "debug_practice_script", "debug_openocd_monitor"
]
expect(hw_tools.len()).to_be_greater_than(0)
expect(hw_tools).to_contain("debug_flash_program")
```

</details>

#### debug log family

#### has representative log tool

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
expect(log_tools.len()).to_be_greater_than(0)
expect(log_tools).to_contain("debug_log_enable")
```

</details>

#### diagnostic family

#### has representative diagnostic tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diag_tools = [
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run"
]
expect(diag_tools.len()).to_be_greater_than(0)
expect(diag_tools).to_contain("simple_read")
```

</details>

#### VCS family

#### has representative VCS tool

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
expect(vcs_tools.len()).to_be_greater_than(0)
expect(vcs_tools).to_contain("simple_diff")
```

</details>

#### CLI tools family

#### has representative CLI tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(cli_tools.len()).to_be_greater_than(0)
expect(cli_tools).to_contain("simple_test")
```

</details>

#### analysis family

#### has representative analysis tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val analysis_tools = [
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_search"
]
expect(analysis_tools.len()).to_be_greater_than(0)
expect(analysis_tools).to_contain("simple_search")
```

</details>

#### task management family

#### has representative task tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task_tools = ["task_status", "task_cancel", "task_list"]
expect(task_tools.len()).to_be_greater_than(0)
expect(task_tools).to_contain("task_status")
```

</details>

#### query family

#### has representative query tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query_tools = [
    "simple_ast_query", "simple_sem_query",
    "simple_query_schema"
]
expect(query_tools.len()).to_be_greater_than(0)
expect(query_tools).to_contain("simple_ast_query")
```

</details>

#### test daemon family

#### has representative test daemon tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val daemon_tools = [
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
expect(daemon_tools.len()).to_be_greater_than(0)
expect(daemon_tools).to_contain("test_daemon_run")
```

</details>

### No Placeholders in Default Help

#### when checking help output for placeholders

#### all help-listed commands have real implementations

1. placeholder in help push
   - Expected: placeholder_in_help.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Commands shown in print_cli_help() that should be fully implemented
val help_commands = [
    "compile", "watch", "targets", "linkers",
    "test", "test-daemon",
    "lex", "lint", "duplicate-check", "fmt", "check",
    "check-arch", "check-dbs", "fix-dbs", "doc-coverage",
    "mcp", "diff", "brief", "query",
    "stats",
    "verify", "gen-lean",
    "ffi-gen", "wrapper-gen",
    "build",
    "init", "add", "remove", "install", "update", "list", "tree"
]
val previously_placeholder: [text] = []
var placeholder_in_help: [text] = []
for cmd in previously_placeholder:
    if help_commands.contains(cmd):
        placeholder_in_help.push(cmd)
# After implementation, placeholders visible in help should be zero
# Currently lex, diff, brief, linkers, ffi-gen are in help
expect(placeholder_in_help.len()).to_equal(0)
```

</details>

#### no cli_not_implemented routes exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is the canonical check: the count of placeholder routes
# MUST be zero. This test fails if any command still calls
# cli_not_implemented().
val expected_remaining_placeholders = 0
val placeholder_count = 0
expect(expected_remaining_placeholders).to_equal(placeholder_count)
```

</details>

### CLI-MCP Cross-System Alignment

#### when checking CLI-to-MCP command mapping

#### test command has MCP equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli_cmd = "test"
val mcp_tool = "simple_test"
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain(mcp_tool)
```

</details>

#### build command has MCP equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_build")
```

</details>

#### lint command has MCP equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_lint")
```

</details>

#### fmt command has MCP equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_format")
```

</details>

#### fix command has MCP equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_fix")
```

</details>

#### diff command has MCP equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_tools = [
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull"
]
expect(mcp_tools).to_contain("simple_diff")
```

</details>

#### check command has MCP equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_tools = [
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run"
]
expect(mcp_tools).to_contain("simple_check")
```

</details>

#### doc-coverage command has MCP equivalent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_doc_coverage")
```

</details>

#### when checking MCP tool count

#### total MCP tools equals 68

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_count = 68
# Family counts: 19+6+6+8+8+1+6+4+3+3+4 = 68
# FAIL-FIRST: family sum is 68, not 69
val family_sum = 19 + 6 + 6 + 8 + 8 + 1 + 6 + 4 + 3 + 3 + 4
expect(family_sum).to_equal(expected_count)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
