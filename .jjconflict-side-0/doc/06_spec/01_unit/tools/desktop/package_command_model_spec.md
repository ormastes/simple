# Package Command Model Specification

> <details>

<!-- sdn-diagram:id=package_command_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=package_command_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

package_command_model_spec -> std
package_command_model_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=package_command_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Package Command Model Specification

## Scenarios

### package command model

#### plans package installation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = parse_package_command(["install", "-y", "git"]).unwrap()

expect(plan.action).to_equal("install")
expect(plan.package_name).to_equal("git")
expect(plan.assume_yes).to_equal(true)
```

</details>

#### plans list without a package name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = parse_package_command(["list"]).unwrap()

expect(plan.action).to_equal("list")
expect(plan.package_name).to_equal("")
```

</details>

#### rejects missing package names for install

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_package_command(["install"]).is_err()).to_equal(true)
```

</details>

#### summarizes planned action

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = parse_package_command(["remove", "--dry-run", "tmux"]).unwrap()

expect(plan.dry_run).to_equal(true)
expect(package_command_summary(plan)).to_equal("pkg remove tmux")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/desktop/package_command_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- package command model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
