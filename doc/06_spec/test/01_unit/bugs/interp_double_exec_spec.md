# Interp Double Exec Specification

> <details>

<!-- sdn-diagram:id=interp_double_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interp_double_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interp_double_exec_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interp_double_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Double Exec Specification

## Scenarios

### Double execution bug

#### guard prevents multiple executions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_guard_single_call()).to_equal(1)
expect(_test_guard_is_set()).to_equal(true)
```

</details>

#### calling guarded_main again is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_guard_multiple_calls()).to_equal(1)
```

</details>

#### without guard, count increments each call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_unguarded_calls()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/interp_double_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Double execution bug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
