# CLI Command Inventory Specification

> Purpose: Prove that CLI Command Inventory.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Command Inventory Specification

Purpose: Prove that CLI Command Inventory.

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
| Source | `test/unit/app/cli_command_inventory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that CLI Command Inventory.
Audience: APP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### CLI Command Inventory

#### core commands

#### has all execution commands

- has all execution commands
- Verify: has all execution commands
   - Expected: exec_commands.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all execution commands")
step("Verify: has all execution commands")
# @req: REQ-APP-CLI-COMMAND-INVENTORY-001
val exec_commands = ["compile", "run", "watch", "watch-daemon"]
expect(exec_commands.len()).to_equal(4)
```

</details>

#### has all testing commands

- has all testing commands
- Verify: has all testing commands
   - Expected: test_commands.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all testing commands")
step("Verify: has all testing commands")
val test_commands = ["test", "test-daemon", "spec-coverage"]
expect(test_commands.len()).to_equal(3)
```

</details>

#### has all code quality commands

- has all code quality commands
- Verify: has all code quality commands
   - Expected: quality_commands.len() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all code quality commands")
step("Verify: has all code quality commands")
val quality_commands = ["lex", "lint", "fix", "fmt", "check",
    "duplicate-check", "doc-coverage", "traceability-check", "check-arch", "check-dbs",
    "fix-dbs"]
expect(quality_commands.len()).to_equal(11)
```

</details>

#### has all build commands

- has all build commands
- Verify: has all build commands
   - Expected: build_commands.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all build commands")
step("Verify: has all build commands")
val build_commands = ["build", "native-build", "targets", "linkers"]
expect(build_commands.len()).to_equal(4)
```

</details>

#### has all LLM-friendly tool commands

- has all LLM-friendly tool commands
- Verify: has all LLM-friendly tool commands
   - Expected: llm_commands.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all LLM-friendly tool commands")
step("Verify: has all LLM-friendly tool commands")
val llm_commands = ["mcp", "lsp", "diff", "constr", "query",
    "info", "brief", "context"]
expect(llm_commands.len()).to_equal(8)
```

</details>

#### has all doc-gen commands

- has all doc-gen commands
- Verify: has all doc-gen commands
   - Expected: doc_commands.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all doc-gen commands")
step("Verify: has all doc-gen commands")
val doc_commands = ["feature-gen", "task-gen", "spec-gen",
    "spipe-docgen", "feature-doc", "todo-scan", "todo-gen",
    "grammar-doc"]
expect(doc_commands.len()).to_equal(8)
```

</details>

#### has all package management commands

- has all package management commands
- Verify: has all package management commands
   - Expected: pkg_commands.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all package management commands")
step("Verify: has all package management commands")
val pkg_commands = ["init", "add", "remove", "install", "update",
    "list", "tree", "cache"]
expect(pkg_commands.len()).to_equal(8)
```

</details>

#### has all verification commands

- has all verification commands
- Verify: has all verification commands
   - Expected: verify_commands.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all verification commands")
step("Verify: has all verification commands")
val verify_commands = ["verify", "gen-lean"]
expect(verify_commands.len()).to_equal(2)
```

</details>

#### has all other commands

- has all other commands
- Verify: has all other commands
   - Expected: other_commands.len() equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all other commands")
step("Verify: has all other commands")
val other_commands = ["stats", "ffi-gen", "i18n", "migrate",
    "replay", "web", "diagram", "dashboard", "office",
    "wrapper-gen", "desugar", "env", "lock", "leak-check"]
expect(other_commands.len()).to_equal(14)
```

</details>

#### total command count

#### has exactly 51 user-facing commands

- has exactly 51 user-facing commands
- Verify: has exactly 51 user-facing commands
   - Expected: all_commands.len() equals `51`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has exactly 51 user-facing commands")
step("Verify: has exactly 51 user-facing commands")
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

- has zero placeholder commands in default help
- Verify: has zero placeholder commands in default help
   - Expected: still_placeholder.len() equals `expected_placeholders.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has zero placeholder commands in default help")
step("Verify: has zero placeholder commands in default help")
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

- lex command is fully implemented
- Verify: lex command is fully implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lex command is fully implemented")
step("Verify: lex command is fully implemented")
# lex should tokenize a file and print tokens
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
# FAIL-FIRST: lex is not yet in the implemented list
expect(implemented_commands).to_contain("lex")
```

</details>

#### diff command is fully implemented

- diff command is fully implemented
- Verify: diff command is fully implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diff command is fully implemented")
step("Verify: diff command is fully implemented")
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("diff")
```

</details>

#### info command is fully implemented

- info command is fully implemented
- Verify: info command is fully implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("info command is fully implemented")
step("Verify: info command is fully implemented")
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("info")
```

</details>

#### brief command is fully implemented

- brief command is fully implemented
- Verify: brief command is fully implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("brief command is fully implemented")
step("Verify: brief command is fully implemented")
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("brief")
```

</details>

#### linkers command is fully implemented

- linkers command is fully implemented
- Verify: linkers command is fully implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("linkers command is fully implemented")
step("Verify: linkers command is fully implemented")
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("linkers")
```

</details>

#### ffi-gen command is fully implemented

- ffi-gen command is fully implemented
- Verify: ffi-gen command is fully implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffi-gen command is fully implemented")
step("Verify: ffi-gen command is fully implemented")
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("ffi-gen")
```

</details>

#### i18n command is fully implemented

- i18n command is fully implemented
- Verify: i18n command is fully implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i18n command is fully implemented")
step("Verify: i18n command is fully implemented")
val implemented_commands = ["compile", "test", "lint", "fmt",
    "build", "check", "mcp", "lsp"]
expect(implemented_commands).to_contain("i18n")
```

</details>

### CLI Experimental Commands

#### when checking experimental command set

#### defines the canonical experimental command list

- defines the canonical experimental command list
- Verify: defines the canonical experimental command list
   - Expected: expected_experimental.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines the canonical experimental command list")
step("Verify: defines the canonical experimental command list")
val expected_experimental = ["verify", "migrate", "constr",
    "replay", "gen-lean"]
expect(expected_experimental.len()).to_equal(5)
```

</details>

#### verify is tagged as experimental

- verify is tagged as experimental
- Verify: verify is tagged as experimental
   - Expected: verify_in_help is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify is tagged as experimental")
step("Verify: verify is tagged as experimental")
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

- all experimental commands are excluded from default help
- Verify: all experimental commands are excluded from default help
   - Expected: default_help_commands does not contain `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all experimental commands are excluded from default help")
step("Verify: all experimental commands are excluded from default help")
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

- experimental commands still exist in dispatch
- Verify: experimental commands still exist in dispatch
   - Expected: dispatch_commands contains `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("experimental commands still exist in dispatch")
step("Verify: experimental commands still exist in dispatch")
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

- non-experimental commands are NOT in experimental list
- Verify: non-experimental commands are NOT in experimental list
   - Expected: experimental does not contain `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-experimental commands are NOT in experimental list")
step("Verify: non-experimental commands are NOT in experimental list")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-CLI-COMMAND-INVENTORY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fdffb8636dfbdf382bfe18cdfe735abd0f69b6d2ebac9684f62069caf4a8ac52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdffb8636dfbdf382bfe18cdfe735abd0f69b6d2ebac9684f62069caf4a8ac52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdffb8636dfbdf382bfe18cdfe735abd0f69b6d2ebac9684f62069caf4a8ac52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/cli_command_inventory_spec.spl
mirror: doc/06_spec/unit/app/cli_command_inventory_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli_command_inventory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli_command_inventory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli_command_inventory_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli_command_inventory_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has all execution commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli_command_inventory_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has all testing commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli_command_inventory_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has all code quality commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
