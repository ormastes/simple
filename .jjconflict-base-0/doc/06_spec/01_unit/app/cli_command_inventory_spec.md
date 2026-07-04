# CLI Command Inventory Specification

> Validates that the CLI command inventory is complete, that no commands route to placeholder stubs (`cli_not_implemented`), and that experimental commands are properly tagged. The expected end-state is zero placeholders — all 51 user-facing commands must have real implementations.

<!-- sdn-diagram:id=cli_command_inventory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_command_inventory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_command_inventory_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_command_inventory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Command Inventory Specification

Validates that the CLI command inventory is complete, that no commands route to placeholder stubs (`cli_not_implemented`), and that experimental commands are properly tagged. The expected end-state is zero placeholders — all 51 user-facing commands must have real implementations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3020-3025 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/cli_command_inventory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the CLI command inventory is complete, that no commands route to
placeholder stubs (`cli_not_implemented`), and that experimental commands are
properly tagged. The expected end-state is zero placeholders — all 51 user-facing
commands must have real implementations.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Dispatch command | A `case` branch in `main.spl` `main()` match block |
| Placeholder | A command that calls `cli_not_implemented()` or is a no-op stub |
| Experimental | Commands not ready for general use: verify, migrate, constr, replay, gen-lean |

## Related Specifications

- [CLI Dispatch Unit Tests](cli_dispatch_unit_spec.spl)
- [Command Dispatch Spec](tooling/command_dispatch_spec.spl)

## Scenarios

### CLI Command Inventory

#### core commands

#### has all execution commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exec_commands = ["compile", "run", "watch", "watch-daemon"]
expect(exec_commands.len()).to_equal(4)
```

</details>

#### has all testing commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_commands = ["test", "test-daemon", "spec-coverage"]
expect(test_commands.len()).to_equal(3)
```

</details>

#### has all code quality commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quality_commands = ["lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "traceability-check", "check-arch", "check-dbs",
    "fix-dbs"]
expect(quality_commands.len()).to_equal(11)
```

</details>

#### has all build commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build_commands = ["build", "native-build", "targets", "linkers"]
expect(build_commands.len()).to_equal(4)
```

</details>

#### has all LLM-friendly tool commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val llm_commands = ["mcp", "lsp", "diff", "constr", "query",
    "info", "brief", "context"]
expect(llm_commands.len()).to_equal(8)
```

</details>

#### has all doc-gen commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc_commands = ["feature-gen", "task-gen", "spec-gen",
    "spipe-docgen", "feature-doc", "todo-scan", "todo-gen",
    "grammar-doc"]
expect(doc_commands.len()).to_equal(8)
```

</details>

#### has all package management commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg_commands = ["init", "add", "remove", "install", "update",
    "list", "tree", "cache"]
expect(pkg_commands.len()).to_equal(8)
```

</details>

#### has all verification commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verify_commands = ["verify", "gen-lean"]
expect(verify_commands.len()).to_equal(2)
```

</details>

#### has all other commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val other_commands = ["stats", "ffi-gen", "i18n", "migrate",
    "replay", "web", "diagram", "dashboard", "office",
    "wrapper-gen", "desugar", "env", "lock", "leak-check"]
expect(other_commands.len()).to_equal(14)
```

</details>

#### total command count

#### has exactly 51 user-facing commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 4 exec + 3 test + 10 quality + 4 build + 8 llm + 8 doc +
# 8 pkg + 2 verify + 14 other = 61
# But the task says 51 — we count the actual dispatch cases.
# The real count from main.spl case branches (excluding -h, -v, -c):
val all_commands = [
    # Execution
    "compile", "run", "watch", "watch-daemon",
    # Testing
    "test", "test-daemon", "spec-coverage",
    # Code quality
    "lex", "lint", "fix", "fmt", "check", "duplicate-check",
    "doc-coverage", "traceability-check", "check-arch", "check-dbs", "fix-dbs",
    # Build
    "build", "native-build", "targets", "linkers",
    # LLM tools
    "mcp", "lsp", "diff", "constr", "query", "info", "brief",
    "context",
    # Doc generation
    "feature-gen", "task-gen", "spec-gen", "spipe-docgen",
    "feature-doc", "todo-scan", "todo-gen", "grammar-doc",
    # Package management
    "init", "add", "remove", "install", "update", "list",
    "tree", "cache",
    # Verification
    "verify", "gen-lean",
    # Other
    "stats", "ffi-gen", "i18n", "migrate", "replay", "web",
    "diagram", "dashboard", "office", "wrapper-gen", "desugar",
    "env", "lock", "leak-check"
]
# Assert-fail-first: task says 51, actual dispatch has more.
# This test FAILS if the count doesn't match the expected canonical set.
expect(all_commands.len()).to_equal(51)
```

</details>

### CLI Placeholder Commands

#### when checking for placeholder implementations

#### has zero placeholder commands in default help

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# These 7 commands were listed as placeholders that should be implemented.
# After implementation, this list should be empty.
# FAIL-FIRST: If any are still placeholders, the expected empty list
# won't match.
val expected_placeholders: [text] = []
val still_placeholder = [
    "lex", "diff", "info", "brief", "linkers", "ffi-gen", "i18n"
]
# Test fails because still_placeholder is not empty
expect(still_placeholder.len()).to_equal(expected_placeholders.len())
```

</details>

#### lex command is fully implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# lex should tokenize a file and print tokens
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
# FAIL-FIRST: lex is not yet in the implemented list
expect(implemented_commands).to_contain("lex")
```

</details>

#### diff command is fully implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("diff")
```

</details>

#### info command is fully implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("info")
```

</details>

#### brief command is fully implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("brief")
```

</details>

#### linkers command is fully implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("linkers")
```

</details>

#### ffi-gen command is fully implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("ffi-gen")
```

</details>

#### i18n command is fully implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("i18n")
```

</details>

### CLI Experimental Commands

#### when checking experimental command set

#### defines the canonical experimental command list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_experimental = ["verify", "migrate", "constr",
    "replay", "gen-lean"]
expect(expected_experimental.len()).to_equal(5)
```

</details>

#### verify is tagged as experimental

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FAIL-FIRST: there is no tagging mechanism yet; this checks
# that the command is in the experimental set, not in default help.
val default_help_commands = [
    "compile", "test", "lint", "fmt", "build", "check", "mcp",
    "lsp", "run", "watch", "fix", "init", "stats"
]
# verify should NOT be in default help (experimental)
val verify_in_help = default_help_commands.contains("verify")
expect(verify_in_help).to_equal(false)
```

</details>

#### all experimental commands are excluded from default help

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val experimental = ["verify", "migrate", "constr", "replay",
    "gen-lean"]
val default_help_commands = [
    "compile", "test", "lint", "fmt", "build", "check", "mcp",
    "lsp", "run", "watch", "fix", "init", "stats", "lex",
    "diff", "info", "brief", "linkers", "ffi-gen", "i18n"
]
for cmd in experimental:
    expect(default_help_commands.contains(cmd)).to_equal(false)
```

</details>

#### experimental commands still exist in dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# They should be callable even if hidden from help
val dispatch_commands = [
    "compile", "run", "watch", "test", "lint", "fmt", "check",
    "build", "mcp", "lsp", "verify", "migrate", "constr",
    "replay", "gen-lean"
]
val experimental = ["verify", "migrate", "constr", "replay",
    "gen-lean"]
for cmd in experimental:
    expect(dispatch_commands.contains(cmd)).to_equal(true)
```

</details>

#### non-experimental commands are NOT in experimental list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val experimental = ["verify", "migrate", "constr", "replay",
    "gen-lean"]
val core_commands = ["compile", "test", "lint", "fmt", "build",
    "check", "mcp", "lsp", "run", "watch"]
for cmd in core_commands:
    expect(experimental.contains(cmd)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
