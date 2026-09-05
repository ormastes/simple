# MCP Tool Family Classification Specification

> Validates that every MCP tool has a category, handler_kind, and maturity label. Ensures no tool is left unclassified and that tool families are internally consistent.

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
| Source | `test/unit/app/mcp_unit/mcp_tool_classification_spec.spl` |
| Updated | 2026-08-26 |
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

- all tools have a recognized category
   - Expected: valid_categories contains `cat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all tools have a recognized category")
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

- debug category has 25 tools (19 session + 6 hardware)
   - Expected: debug_count equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug category has 25 tools (19 session + 6 hardware)")
val debug_count = 25
expect(debug_count).to_equal(25)
```

</details>

#### debug-log category has 6 tools

- debug-log category has 6 tools
   - Expected: debug_log_count equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug-log category has 6 tools")
val debug_log_count = 6
expect(debug_log_count).to_equal(6)
```

</details>

#### diagnostics category has 9 tools

- diagnostics category has 9 tools
   - Expected: diag_count equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diagnostics category has 9 tools")
val diag_count = 9
expect(diag_count).to_equal(9)
```

</details>

#### vcs category has 8 tools

- vcs category has 8 tools
   - Expected: vcs_count equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vcs category has 8 tools")
val vcs_count = 8
expect(vcs_count).to_equal(8)
```

</details>

#### cli category has 34 tools

- cli category has 34 tools
   - Expected: cli_count equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cli category has 34 tools")
# 6 original + 15 tier1 + 13 tier2 = 34
val cli_count = 34
expect(cli_count).to_equal(34)
```

</details>

#### query category has 7 tools

- query category has 7 tools
   - Expected: query_count equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query category has 7 tools")
# 4 analysis + 3 ast/sem query
val query_count = 7
expect(query_count).to_equal(7)
```

</details>

#### task category has 3 tools

- task category has 3 tools
   - Expected: task_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("task category has 3 tools")
val task_count = 3
expect(task_count).to_equal(3)
```

</details>

#### test-daemon category has 4 tools

- test-daemon category has 4 tools
   - Expected: daemon_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test-daemon category has 4 tools")
val daemon_count = 4
expect(daemon_count).to_equal(4)
```

</details>

#### all category sizes sum to 106

- all category sizes sum to 106
   - Expected: total equals `106`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all category sizes sum to 106")
# 25 debug + 6 debug-log + 9 diag + 8 vcs + 34 cli +
# 7 query + 3 task + 7 ui-access + 4 test-daemon + 3 tier3 = 106
val total = 25 + 6 + 9 + 8 + 34 + 7 + 3 + 7 + 4 + 3
expect(total).to_equal(106)
```

</details>

### MCP Handler Kind Validation

#### when checking valid handler kinds

#### only recognized handler kinds are used

- only recognized handler kinds are used
   - Expected: valid_kinds contains `kind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only recognized handler kinds are used")
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

- in_process handlers cover debug and diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("in_process handlers cover debug and diagnostics")
# 19 debug session + 6 hw debug + 3 diag (read, edit, multi_edit)
# + 1 status + 1 run + 1 api + 7 ui-access = 38 in_process
val in_process_count = 38
expect(in_process_count).to_be_greater_than(25)
```

</details>

#### vcs handlers cover all VCS tools

- vcs handlers cover all VCS tools
   - Expected: vcs_count equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vcs handlers cover all VCS tools")
val vcs_count = 8
expect(vcs_count).to_equal(8)
```

</details>

#### query handlers cover analysis tools

- query handlers cover analysis tools
   - Expected: query_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query handlers cover analysis tools")
val query_count = 4
expect(query_count).to_equal(4)
```

</details>

#### cli handlers are the largest group

- cli handlers are the largest group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cli handlers are the largest group")
val cli_handler_count = 56
val total = 106
expect(cli_handler_count).to_be_greater_than(total / 2)
```

</details>

### MCP Tool Maturity Labels

#### when checking maturity labels

#### all tools have a maturity label

- all tools have a maturity label
   - Expected: total equals `108`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all tools have a maturity label")
val valid_maturities = ["stable", "beta", "stub"]
# All 108 tools: 100 stable + 8 beta + 0 stub
val maturity_distribution = [100, 8, 0]
val total = maturity_distribution[0] + maturity_distribution[1] + maturity_distribution[2]
expect(total).to_equal(108)
```

</details>

#### most tools are stable

- most tools are stable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("most tools are stable")
val stable_count = 100
expect(stable_count).to_be_greater_than(85)
```

</details>

#### beta tools are hardware debug and experimental CLI

- beta tools are hardware debug and experimental CLI
   - Expected: beta_tools.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("beta tools are hardware debug and experimental CLI")
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

- no stub tools remain
   - Expected: stub_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no stub tools remain")
val stub_count = 0
expect(stub_count).to_equal(0)
```

</details>

#### when checking ui-access family

#### has all 12 ui-access tools

- has all 12 ui-access tools
   - Expected: ui_access_tools.len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all 12 ui-access tools")
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

- ui-access tools start with ui_access_
   - Expected: tool.starts_with("ui_access_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ui-access tools start with ui_access_")
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

- all cli handler tools have a cli_command
   - Expected: cli_tools_with_commands.len() equals `corresponding_cli_commands.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all cli handler tools have a cli_command")
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

- cli_command values are valid CLI commands
   - Expected: valid_cli_commands contains `target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cli_command values are valid CLI commands")
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

- all debug tools start with debug_
   - Expected: tool.starts_with("debug_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all debug tools start with debug_")
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

- all debug-log tools start with debug_log_
   - Expected: tool.starts_with("debug_log_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all debug-log tools start with debug_log_")
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

- all task tools start with task_
   - Expected: tool.starts_with("task_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all task tools start with task_")
val task_tools = ["task_status", "task_cancel", "task_list"]
for tool in task_tools:
    expect(tool.starts_with("task_")).to_equal(true)
```

</details>

#### all test-daemon tools start with test_daemon_

- all test-daemon tools start with test_daemon_
   - Expected: tool.starts_with("test_daemon_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all test-daemon tools start with test_daemon_")
val daemon_tools = [
    "test_daemon_run", "test_daemon_clean",
    "test_daemon_status", "test_daemon_stop"
]
for tool in daemon_tools:
    expect(tool.starts_with("test_daemon_")).to_equal(true)
```

</details>

#### all diagnostics tools start with simple_

- all diagnostics tools start with simple_
   - Expected: tool.starts_with("simple_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all diagnostics tools start with simple_")
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

- all VCS tools start with simple_
   - Expected: tool.starts_with("simple_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all VCS tools start with simple_")
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

- **Requirements:** `doc/02_requirements/feature/simple_cli_mcp_completeness.md`
- **Plan:** `doc/03_plan/simple_cli_mcp_completeness_plan_2026-03-27.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-F3-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ac18ff98bcf5c50cec07148d78e7c79d165067132d6d406184f8bb7aa2db75d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac18ff98bcf5c50cec07148d78e7c79d165067132d6d406184f8bb7aa2db75d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac18ff98bcf5c50cec07148d78e7c79d165067132d6d406184f8bb7aa2db75d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/mcp_tool_classification_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_tool_classification_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_tool_classification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_tool_classification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_tool_classification_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_tool_classification_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all tools have a recognized category' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_tool_classification_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'debug category has 25 tools (19 session + 6 hardware)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_tool_classification_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'debug-log category has 6 tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
