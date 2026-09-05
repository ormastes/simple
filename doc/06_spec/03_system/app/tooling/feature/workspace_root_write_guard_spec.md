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

### Workspace root write guard

#### has a host guard script

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("scripts/check-workspace-root-guard.shs")).to_equal(true)
```

</details>

#### uses FILE.md as policy source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("scripts/check-workspace-root-guard.shs")
expect(source.contains("FILE.md")).to_equal(true)
expect(source.contains("load_allowed_root")).to_equal(true)
```

</details>

#### defines root and immediate-child diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("scripts/check-workspace-root-guard.shs")
expect(source.contains("WRG001")).to_equal(true)
expect(source.contains("WRG002")).to_equal(true)
```

</details>

#### quarantines instead of deleting

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("scripts/check-workspace-root-guard.shs")
expect(source.contains("build/workspace_quarantine")).to_equal(true)
expect(source.contains("mv \"$rel\" \"$dest\"")).to_equal(true)
```

</details>

#### has staged lint integration

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapper = read_file("bin/simple")
val cli_ops = read_file("src/app/io/cli_ops.spl")
val cli_lint = read_file("src/app/io/cli_lint_commands.spl")
expect(wrapper.contains("check-workspace-root-guard.shs")).to_equal(true)
expect(wrapper.contains("audit --staged")).to_equal(true)
expect(cli_ops.contains("_cli_run_workspace_root_guard")).to_equal(true)
expect(cli_lint.contains("_cli_run_workspace_root_guard()")).to_equal(true)
```

</details>

#### has tracked repo hygiene integration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hygiene = read_file("scripts/check/check-repo-hygiene.shs")
expect(hygiene.contains("check-workspace-root-guard.shs audit --staged")).to_equal(true)
```

</details>

#### has a pre-commit hook wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hook = read_file("scripts/hooks/pre-commit")
expect(hook.contains("check-workspace-root-guard.shs audit --staged")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/tooling/feature/workspace_root_write_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Workspace root write guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
