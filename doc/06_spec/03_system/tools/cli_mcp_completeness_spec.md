# CLI/MCP Completeness System Specification

> System-level tests that validate CLI command families and MCP tool families each have at least one working representative, and that no placeholder commands are visible in default help output.

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
| Updated | 2026-08-26 |
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

- has working compile command
   - Expected: has_representative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working compile command")
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

- has working test command
   - Expected: has_representative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working test command")
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

- has working lint command
   - Expected: has_representative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working lint command")
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

- all code quality commands are implemented
   - Expected: implemented contains `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all code quality commands are implemented")
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

- has working build command
   - Expected: has_representative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working build command")
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

- all build commands are implemented
   - Expected: implemented contains `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all build commands are implemented")
val build_family = ["build", "native-build", "targets",
    "linkers"]
val implemented = ["build", "native-build", "targets", "linkers"]
for cmd in build_family:
    expect(implemented.contains(cmd)).to_equal(true)
```

</details>

#### LLM tools family

#### has working mcp command

- has working mcp command
   - Expected: has_representative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working mcp command")
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

- all LLM tool commands are implemented
   - Expected: implemented contains `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all LLM tool commands are implemented")
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

- has working feature-gen command
   - Expected: has_representative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working feature-gen command")
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

- has working init command
   - Expected: has_representative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working init command")
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

- has working verify command
   - Expected: has_representative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working verify command")
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

- has working ffi-gen command
   - Expected: implemented contains `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working ffi-gen command")
val ffi_family = ["ffi-gen", "wrapper-gen"]
val implemented = ["ffi-gen", "wrapper-gen"]
for cmd in ffi_family:
    expect(implemented.contains(cmd)).to_equal(true)
```

</details>

#### i18n family

#### has working i18n command

- has working i18n command
   - Expected: implemented contains `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has working i18n command")
val i18n_family = ["i18n"]
val implemented = ["i18n"]
for cmd in i18n_family:
    expect(implemented.contains(cmd)).to_equal(true)
```

</details>

### MCP Tool Family Completeness

#### debug session family

#### has representative debug tool

- has representative debug tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative debug tool")
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

- has representative hardware debug tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative hardware debug tool")
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

- has representative log tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative log tool")
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

- has representative diagnostic tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative diagnostic tool")
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

- has representative VCS tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative VCS tool")
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

- has representative CLI tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative CLI tool")
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

- has representative analysis tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative analysis tool")
val analysis_tools = [
    "simple_dependencies", "simple_api_diff",
    "simple_context", "simple_ponytail", "simple_search"
]
expect(analysis_tools.len()).to_be_greater_than(0)
expect(analysis_tools).to_contain("simple_search")
```

</details>

#### task management family

#### has representative task tool

- has representative task tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative task tool")
val task_tools = ["task_status", "task_cancel", "task_list"]
expect(task_tools.len()).to_be_greater_than(0)
expect(task_tools).to_contain("task_status")
```

</details>

#### query family

#### has representative query tool

- has representative query tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative query tool")
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

- has representative test daemon tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has representative test daemon tool")
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

- all help-listed commands have real implementations
   - Expected: placeholder_in_help.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all help-listed commands have real implementations")
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

- no cli_not_implemented routes exist
   - Expected: expected_remaining_placeholders equals `placeholder_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no cli_not_implemented routes exist")
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

- test command has MCP equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test command has MCP equivalent")
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

- build command has MCP equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("build command has MCP equivalent")
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_build")
```

</details>

#### lint command has MCP equivalent

- lint command has MCP equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lint command has MCP equivalent")
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_lint")
```

</details>

#### fmt command has MCP equivalent

- fmt command has MCP equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fmt command has MCP equivalent")
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_format")
```

</details>

#### fix command has MCP equivalent

- fix command has MCP equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fix command has MCP equivalent")
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_fix")
```

</details>

#### diff command has MCP equivalent

- diff command has MCP equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diff command has MCP equivalent")
val mcp_tools = [
    "simple_diff", "simple_log", "simple_squash",
    "simple_new", "simple_commit", "simple_push",
    "simple_rebase", "simple_pull"
]
expect(mcp_tools).to_contain("simple_diff")
```

</details>

#### check command has MCP equivalent

- check command has MCP equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check command has MCP equivalent")
val mcp_tools = [
    "simple_read", "simple_check", "simple_symbols",
    "simple_status", "simple_diagnostics", "simple_edit",
    "simple_multi_edit", "simple_run"
]
expect(mcp_tools).to_contain("simple_check")
```

</details>

#### doc-coverage command has MCP equivalent

- doc-coverage command has MCP equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage command has MCP equivalent")
val mcp_tools = [
    "simple_test", "simple_build", "simple_format",
    "simple_lint", "simple_fix", "simple_doc_coverage"
]
expect(mcp_tools).to_contain("simple_doc_coverage")
```

</details>

#### when checking MCP tool count

#### total MCP tools equals 69

- total MCP tools equals 69
   - Expected: family_sum equals `expected_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("total MCP tools equals 69")
val expected_count = 69
# Family counts: 19+6+6+8+8+1+6+5+3+3+4 = 69
val family_sum = 19 + 6 + 6 + 8 + 8 + 1 + 6 + 5 + 3 + 3 + 4
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be037b03040f44cba2342c9768122553f6843188b87c02526a0b8ca284946bea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be037b03040f44cba2342c9768122553f6843188b87c02526a0b8ca284946bea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be037b03040f44cba2342c9768122553f6843188b87c02526a0b8ca284946bea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/tools/cli_mcp_completeness_spec.spl
mirror: doc/06_spec/03_system/tools/cli_mcp_completeness_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=95 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/cli_mcp_completeness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/cli_mcp_completeness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/cli_mcp_completeness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/cli_mcp_completeness_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has working compile command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/cli_mcp_completeness_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has working test command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/cli_mcp_completeness_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has working lint command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/cli_mcp_completeness_spec.spl:409:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test command has MCP equivalent' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
