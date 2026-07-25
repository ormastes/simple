# Workspace Root Write Guard Specification

> <details>

<!-- sdn-diagram:id=workspace_root_write_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=workspace_root_write_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

workspace_root_write_guard_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=workspace_root_write_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Workspace Root Write Guard Specification

## Scenarios

### Workspace root write guard implementation

#### ships the root guard script

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("scripts/check-workspace-root-guard.shs")).to_equal(true)
```

</details>

#### supports audit fix lock unlock modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("scripts/check-workspace-root-guard.shs")
expect(source.contains("does not delete files")).to_equal(true)
expect(source.contains("rm -rf \"$TMP_DIR\"")).to_equal(true)
expect(source.contains("rm -rf \"$rel\"")).to_equal(false)
```

</details>

#### documents Windows ACL locking

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("scripts/check-workspace-root-guard.shs")
expect(source.contains("icacls")).to_equal(true)
expect(source.contains("Administrator")).to_equal(true)
expect(source.contains("protected_lock_dirs")).to_equal(true)
expect(source.contains("MUTABLE_ROOT_DIRS")).to_equal(true)
```

</details>

#### wires lint entrypoints to the staged audit helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lint = read_file("src/app/io/cli_lint_commands.spl")
val lint_entry = read_file("src/app/cli/lint_entry.spl")
expect(lint.contains("_cli_run_workspace_root_guard()")).to_equal(true)
expect(lint_entry.contains("_cli_run_workspace_root_guard()")).to_equal(true)
```

</details>

#### wires tracked CLI lint to staged audit

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ops = read_file("src/app/io/cli_ops.spl")
val lint = read_file("src/app/io/cli_lint_commands.spl")
val lint_entry = read_file("src/app/cli/lint_entry.spl")
expect(ops.contains("_cli_run_workspace_root_guard")).to_equal(true)
expect(ops.contains("check-workspace-root-guard.shs")).to_equal(true)
expect(lint.contains("_cli_run_workspace_root_guard()")).to_equal(true)
expect(lint_entry.contains("_cli_run_workspace_root_guard()")).to_equal(true)
```

</details>

#### wires tracked repo hygiene to staged audit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("scripts/check/check-repo-hygiene.shs")
expect(source.contains("check-workspace-root-guard.shs audit --staged")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/workspace_root_write_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
