# Parse Utils Specification

> 1. expect mode unwrap

<!-- sdn-diagram:id=parse_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parse_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parse_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parse_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parse Utils Specification

## Scenarios

### ParseUtils

#### finds a flag value

1. expect mode unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--mode", "fast", "--verbose"]
val mode = _parse_flag_value(args, "--mode")
expect mode.unwrap() == "fast"
```

</details>

#### returns nil for a missing flag value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--verbose"]
val mode = _parse_flag_value(args, "--mode")
expect mode == nil
```

</details>

#### detects boolean flags

1. expect  has flag
2. expect  has flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--mode", "fast", "--verbose"]
expect _has_flag(args, "--verbose") == true
expect _has_flag(args, "--quiet") == false
```

</details>

#### splits comma separated flags and drops blanks

1. expect flags len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = _parse_csv_flags("native, , smf")
expect flags.len() == 2
expect flags[0] == "native"
expect flags[1] == "smf"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/parse_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ParseUtils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
