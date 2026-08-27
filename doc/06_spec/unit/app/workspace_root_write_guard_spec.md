# Workspace Root Write Guard Specification

> Tests covering Workspace root write guard implementation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Workspace Root Write Guard Specification

## Scenarios

### Workspace root write guard implementation

#### ships the root guard script

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ships the root guard script
   - Expected: file_exists("scripts/check-workspace-root-guard.shs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ships the root guard script")
expect(file_exists("scripts/check-workspace-root-guard.shs")).to_equal(true)
```

</details>

#### supports audit fix lock unlock modes

- supports audit fix lock unlock modes
   - Expected: source contains `audit|fix|lock|unlock`
   - Expected: source contains `--apply`
   - Expected: source contains `run_audit`
   - Expected: source contains `run_fix`
   - Expected: source contains `run_lock_preview`
   - Expected: source contains `run_lock_apply`
   - Expected: source contains `run_unlock_apply`
   - Expected: source contains `load_builtin_allowed_root`
   - Expected: source does not contain `FILE.md not found at repository root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports audit fix lock unlock modes")
val source = read_file("scripts/check-workspace-root-guard.shs")
expect(source.contains("audit|fix|lock|unlock")).to_equal(true)
expect(source.contains("--apply")).to_equal(true)
expect(source.contains("run_audit")).to_equal(true)
expect(source.contains("run_fix")).to_equal(true)
expect(source.contains("run_lock_preview")).to_equal(true)
expect(source.contains("run_lock_apply")).to_equal(true)
expect(source.contains("run_unlock_apply")).to_equal(true)
expect(source.contains("load_builtin_allowed_root")).to_equal(true)
expect(source.contains("FILE.md not found at repository root")).to_equal(false)
```

</details>

#### does not delete by default

- does not delete by default
   - Expected: source contains `does not delete files`
   - Expected: source contains `rm -rf "$TMP_DIR"`
   - Expected: source does not contain `rm -rf "$rel"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not delete by default")
val source = read_file("scripts/check-workspace-root-guard.shs")
expect(source.contains("does not delete files")).to_equal(true)
expect(source.contains("rm -rf \"$TMP_DIR\"")).to_equal(true)
expect(source.contains("rm -rf \"$rel\"")).to_equal(false)
```

</details>

#### documents Windows ACL locking

- documents Windows ACL locking
   - Expected: source contains `icacls`
   - Expected: source contains `Administrator`
   - Expected: source contains `protected_lock_dirs`
   - Expected: source contains `MUTABLE_ROOT_DIRS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents Windows ACL locking")
val source = read_file("scripts/check-workspace-root-guard.shs")
expect(source.contains("icacls")).to_equal(true)
expect(source.contains("Administrator")).to_equal(true)
expect(source.contains("protected_lock_dirs")).to_equal(true)
expect(source.contains("MUTABLE_ROOT_DIRS")).to_equal(true)
```

</details>

#### wires lint entrypoints to the staged audit helper

- wires lint entrypoints to the staged audit helper
   - Expected: lint contains `_cli_run_workspace_root_guard()`
   - Expected: lint_entry contains `cli_run_lint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires lint entrypoints to the staged audit helper")
val lint = read_file("src/app/io/cli_lint_commands.spl")
val lint_entry = read_file("src/app/cli/lint_entry.spl")
expect(lint.contains("_cli_run_workspace_root_guard()")).to_equal(true)
expect(lint_entry.contains("cli_run_lint")).to_equal(true)
```

</details>

#### wires tracked CLI lint to staged audit

- wires tracked CLI lint to staged audit
   - Expected: ops contains `_cli_run_workspace_root_guard`
   - Expected: ops contains `check-workspace-root-guard.shs`
   - Expected: lint contains `_cli_run_workspace_root_guard()`
   - Expected: lint_entry contains `cli_run_lint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires tracked CLI lint to staged audit")
val ops = read_file("src/app/io/cli_ops.spl")
val lint = read_file("src/app/io/cli_lint_commands.spl")
val lint_entry = read_file("src/app/cli/lint_entry.spl")
expect(ops.contains("_cli_run_workspace_root_guard")).to_equal(true)
expect(ops.contains("check-workspace-root-guard.shs")).to_equal(true)
expect(lint.contains("_cli_run_workspace_root_guard()")).to_equal(true)
expect(lint_entry.contains("cli_run_lint")).to_equal(true)
```

</details>

#### wires tracked repo hygiene to staged audit

- wires tracked repo hygiene to staged audit
   - Expected: source contains `check-workspace-root-guard.shs audit --staged`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires tracked repo hygiene to staged audit")
val source = read_file("scripts/check/check-repo-hygiene.shs")
expect(source.contains("check-workspace-root-guard.shs audit --staged")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/workspace_root_write_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Workspace root write guard implementation.
- Workspace root write guard implementation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b88db97a13c8dd7294498f0c7bf1d0e5af070201cf62b50ba8df37550b6294a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b88db97a13c8dd7294498f0c7bf1d0e5af070201cf62b50ba8df37550b6294a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b88db97a13c8dd7294498f0c7bf1d0e5af070201cf62b50ba8df37550b6294a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/workspace_root_write_guard_spec.spl
mirror: doc/06_spec/unit/app/workspace_root_write_guard_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/app/workspace_root_write_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/workspace_root_write_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/workspace_root_write_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/app/workspace_root_write_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships the root guard script' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/workspace_root_write_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports audit fix lock unlock modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/workspace_root_write_guard_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not delete by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
