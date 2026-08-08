# Mktemp Specification

> <details>

<!-- sdn-diagram:id=mktemp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mktemp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mktemp_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mktemp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mktemp Specification

## Scenarios

### mktemp tool

#### temp file creation

#### generates unique names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts1: i64 = 1000
val ts2: i64 = 1001
val name1 = "tmp.{ts1}"
val name2 = "tmp.{ts2}"
expect(name1 != name2).to_equal(true)
```

</details>

#### uses /tmp prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "tmp.12345"
val path = "/tmp/{name}"
expect(path).to_start_with("/tmp/")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/mktemp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- mktemp tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
