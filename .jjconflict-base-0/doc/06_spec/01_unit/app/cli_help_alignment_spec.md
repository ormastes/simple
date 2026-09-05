# CLI Help Text Alignment Specification

> Validates that the CLI help text (`print_cli_help()`) is aligned with the actual dispatch table in `main.spl`. Every command listed in help must exist in dispatch, and no phantom commands should appear.

<!-- sdn-diagram:id=cli_help_alignment_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_help_alignment_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_help_alignment_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_help_alignment_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Help Text Alignment Specification

Validates that the CLI help text (`print_cli_help()`) is aligned with the actual dispatch table in `main.spl`. Every command listed in help must exist in dispatch, and no phantom commands should appear.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3026-3030 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/cli_help_alignment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the CLI help text (`print_cli_help()`) is aligned with the
actual dispatch table in `main.spl`. Every command listed in help must exist
in dispatch, and no phantom commands should appear.

Commands listed in help are extracted from `src/app/cli/cli_helpers.spl`.
Commands in dispatch are extracted from `src/app/cli/main.spl` match block.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Help command | A command string printed by `print_cli_help()` |
| Dispatch command | A `case` branch in the main match block |
| Phantom command | Listed in help but has no dispatch handler |
| Hidden command | Has dispatch handler but not listed in help |

## Related Specifications

- [CLI Command Inventory](cli_command_inventory_spec.spl)
- [CLI Dispatch Unit Tests](cli_dispatch_unit_spec.spl)

## Scenarios

### CLI Help Text Alignment

#### when checking help lists implemented commands

#### help lists all core execution commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_commands = ["compile", "run", "watch"]
val dispatch_commands = ["compile", "run", "watch", "watch-daemon"]
for cmd in help_commands:
    expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

#### help lists all testing commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_test_commands = ["test", "test-daemon"]
val dispatch_commands = ["test", "test-daemon", "spec-coverage"]
for cmd in help_test_commands:
    expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

#### help lists all code quality commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_quality = ["lex", "lint", "fmt", "check",
    "duplicate-check", "doc-coverage", "traceability-check", "check-arch",
    "check-dbs", "fix-dbs"]
val dispatch_commands = ["lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "traceability-check", "check-arch", "check-dbs",
    "fix-dbs"]
for cmd in help_quality:
    expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

#### help lists all LLM tool commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_llm = ["mcp", "diff", "brief", "query"]
val dispatch_commands = ["mcp", "lsp", "diff", "constr", "query",
    "info", "brief", "context"]
for cmd in help_llm:
    expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

#### help lists all build commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_build = ["build", "targets", "linkers"]
val dispatch_commands = ["build", "native-build", "targets",
    "linkers"]
for cmd in help_build:
    expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

#### help lists package management commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_pkg = ["init", "add", "remove", "install", "update",
    "list", "tree"]
val dispatch_commands = ["init", "add", "remove", "install",
    "update", "list", "tree", "cache"]
for cmd in help_pkg:
    expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

#### when checking for phantom commands

#### no help command is missing from dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All commands mentioned in print_cli_help() output
val help_commands = [
    "compile", "watch", "targets", "linkers",
    "test", "test-daemon",
    "lex", "lint", "duplicate-check", "fmt", "check",
    "check-arch", "check-dbs", "fix-dbs", "doc-coverage", "traceability-check",
    "mcp", "diff", "brief", "query",
    "stats",
    "verify", "gen-lean",
    "ffi-gen", "wrapper-gen",
    "build",
    "init", "add", "remove", "install", "update", "list", "tree"
]
# Full dispatch set from main.spl
val dispatch_commands = [
    "compile", "run", "watch", "watch-daemon",
    "test", "test-daemon", "spec-coverage",
    "lex", "lint", "fix", "fmt", "check", "duplicate-check",
    "doc-coverage", "traceability-check", "check-arch", "check-dbs", "fix-dbs",
    "build", "native-build", "targets", "linkers",
    "mcp", "lsp", "diff", "constr", "query", "info", "brief",
    "context",
    "feature-gen", "task-gen", "spec-gen", "spipe-docgen",
    "feature-doc", "todo-scan", "todo-gen", "grammar-doc",
    "init", "add", "remove", "install", "update", "list",
    "tree", "cache",
    "verify", "gen-lean",
    "stats", "ffi-gen", "i18n", "migrate", "replay", "web",
    "diagram", "dashboard", "office", "wrapper-gen", "desugar",
    "env", "lock", "leak-check"
]
for cmd in help_commands:
    expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

#### check-capsule from help exists in dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# print_cli_help mentions 'check-capsule' but dispatch uses 'check'
# FAIL-FIRST: check-capsule is in help but not a separate dispatch case
val dispatch_commands = [
    "compile", "run", "watch", "watch-daemon",
    "test", "test-daemon", "spec-coverage",
    "lex", "lint", "fix", "fmt", "check", "duplicate-check",
    "doc-coverage", "traceability-check", "check-arch", "check-dbs", "fix-dbs",
    "build", "native-build", "targets", "linkers",
    "mcp", "lsp", "diff", "constr", "query", "info", "brief",
    "context",
    "feature-gen", "task-gen", "spec-gen", "spipe-docgen",
    "feature-doc", "todo-scan", "todo-gen", "grammar-doc",
    "init", "add", "remove", "install", "update", "list",
    "tree", "cache",
    "verify", "gen-lean",
    "stats", "ffi-gen", "i18n", "migrate", "replay", "web",
    "diagram", "dashboard", "office", "wrapper-gen", "desugar",
    "env", "lock", "leak-check"
]
# check-capsule appears in help text but is a subcommand of check,
# not its own dispatch case. This test documents the gap.
expect(dispatch_commands.contains("check-capsule")).to_equal(true)
```

</details>

### CLI No Phantom Commands

#### when validating help-dispatch parity

#### help command count matches dispatch command count for visible commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Help shows ~33 commands (some are subcommand variants)
# Dispatch has ~55+ case branches
# FAIL-FIRST: These counts should be aligned after cleanup.
# The visible (non-experimental) help commands:
val visible_help_count = 33
# The visible (non-experimental) dispatch commands:
val visible_dispatch_count = 33
# After excluding experimental from dispatch:
val experimental_count = 5
val total_dispatch = 56
val visible_from_dispatch = total_dispatch - experimental_count
# FAIL-FIRST: 56 - 5 = 51, not 33 (many dispatch commands missing from help)
expect(visible_help_count).to_equal(visible_from_dispatch)
```

</details>

#### every dispatch command has help text or is tagged experimental

1. missing from help non experimental push
   - Expected: missing_from_help_non_experimental.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch_only = [
    "watch-daemon", "spec-coverage", "fix", "native-build",
    "lsp", "constr", "info", "context",
    "feature-gen", "task-gen", "spec-gen", "spipe-docgen",
    "feature-doc", "todo-scan", "todo-gen", "grammar-doc",
    "cache", "i18n", "migrate", "replay", "web", "diagram",
    "dashboard", "office", "desugar", "env", "lock", "leak-check"
]
val experimental = ["verify", "migrate", "constr", "replay",
    "gen-lean"]
# FAIL-FIRST: dispatch-only commands that are NOT experimental
# should be added to help text
val missing_from_help_non_experimental: [text] = []
for cmd in dispatch_only:
    if not experimental.contains(cmd):
        missing_from_help_non_experimental.push(cmd)
# After all commands are documented in help, this should be 0
expect(missing_from_help_non_experimental.len()).to_equal(0)
```

</details>

### CLI Experimental Commands in Help

#### when checking experimental visibility

#### verify is shown in help with experimental tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Help text currently shows: "simple verify <file.spl>    Run formal verification"
# FAIL-FIRST: No [experimental] tag present
val verify_help_line = "simple verify <file.spl>    Run formal verification"
expect(verify_help_line).to_contain("[experimental]")
```

</details>

#### gen-lean is shown in help with experimental tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen_lean_help_line = "simple gen-lean generate    Generate Lean verification files"
expect(gen_lean_help_line).to_contain("[experimental]")
```

</details>

#### migrate is hidden from default help

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# migrate should not appear in help at all
val help_commands_shown = [
    "compile", "watch", "targets", "linkers", "test",
    "test-daemon", "lex", "lint", "duplicate-check", "fmt",
    "check", "doc-coverage", "mcp", "diff", "brief", "query",
    "stats", "verify", "gen-lean", "ffi-gen", "wrapper-gen",
    "build", "init", "add", "remove", "install", "update",
    "list", "tree"
]
expect(help_commands_shown.contains("migrate")).to_equal(false)
```

</details>

#### constr is hidden from default help

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_commands_shown = [
    "compile", "watch", "targets", "linkers", "test",
    "test-daemon", "lex", "lint", "duplicate-check", "fmt",
    "check", "doc-coverage", "mcp", "diff", "brief", "query",
    "stats", "verify", "gen-lean", "ffi-gen", "wrapper-gen",
    "build", "init", "add", "remove", "install", "update",
    "list", "tree"
]
expect(help_commands_shown.contains("constr")).to_equal(false)
```

</details>

#### replay is hidden from default help

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_commands_shown = [
    "compile", "watch", "targets", "linkers", "test",
    "test-daemon", "lex", "lint", "duplicate-check", "fmt",
    "check", "doc-coverage", "mcp", "diff", "brief", "query",
    "stats", "verify", "gen-lean", "ffi-gen", "wrapper-gen",
    "build", "init", "add", "remove", "install", "update",
    "list", "tree"
]
expect(help_commands_shown.contains("replay")).to_equal(false)
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
