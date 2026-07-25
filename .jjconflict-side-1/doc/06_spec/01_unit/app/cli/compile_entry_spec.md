# Compile Entry Specification

> 1. expect args len

<!-- sdn-diagram:id=compile_entry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compile_entry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compile_entry_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compile_entry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Entry Specification

## Scenarios

### compile_entry normalize_compile_args

#### keeps the compile token and subcommand args after the wrapper paths

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw_args = [
    "bin/simple",
    "src/app/cli/compile_entry.spl",
    "compile",
    "src/app/hosted_apps/smux_client.spl",
    "--target",
    "x86_64-unknown-none",
    "-o",
    "/tmp/smux.smf"
]

val args = normalize_compile_args(raw_args)

expect args.len() == 6
expect args[0] == "compile"
expect args[1] == "src/app/hosted_apps/smux_client.spl"
expect args[2] == "--target"
expect args[3] == "x86_64-unknown-none"
expect args[4] == "-o"
expect args[5] == "/tmp/smux.smf"
```

</details>

#### returns an empty list when argv is missing

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = normalize_compile_args(nil)
expect args.len() == 0
```

</details>

#### returns an empty list when only wrapper metadata is present

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = normalize_compile_args(["bin/simple", "src/app/cli/compile_entry.spl"])
expect args.len() == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/compile_entry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compile_entry normalize_compile_args

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
