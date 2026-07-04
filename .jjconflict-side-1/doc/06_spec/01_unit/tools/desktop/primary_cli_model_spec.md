# Primary Cli Model Specification

> <details>

<!-- sdn-diagram:id=primary_cli_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=primary_cli_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

primary_cli_model_spec -> std
primary_cli_model_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=primary_cli_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primary Cli Model Specification

## Scenarios

### primary CLI model

#### lists the required minimal commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = primary_cli_names()

expect(names).to_contain("shell")
expect(names).to_contain("tmux")
expect(names).to_contain("ssh")
expect(names).to_contain("ls")
expect(names).to_contain("mkdir")
expect(names).to_contain("chmod")
expect(names).to_contain("sudo")
expect(names).to_contain("pkg")
```

</details>

#### maps commands to executable paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmux = primary_cli_find("tmux").unwrap()
val pkg = primary_cli_find("pkg").unwrap()

expect(tmux.executable).to_equal("/usr/bin/tmux")
expect(pkg.executable).to_equal("/usr/sbin/pkg")
```

</details>

#### reports availability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(primary_cli_is_available("ssh")).to_equal(true)
expect(primary_cli_is_available("unknown")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/desktop/primary_cli_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- primary CLI model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
