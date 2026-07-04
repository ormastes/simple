# Native directory create operations

> Verifies the native directory API can create and remove a temporary directory through the Simple directory facade.

<!-- sdn-diagram:id=native_ops_dir_create_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_dir_create_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_dir_create_spec -> app
native_ops_dir_create_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_ops_dir_create_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native directory create operations

Verifies the native directory API can create and remove a temporary directory through the Simple directory facade.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_dir_create_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the native directory API can create and remove a temporary directory
through the Simple directory facade.

## Acceptance

- A temporary directory can be created.
- The directory is detected as a directory.
- The directory tree can be removed.

## Scenarios

### Native Directory Ops

<details>
<summary>Advanced: creates directories</summary>

#### creates directories _(slow)_

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "{tmp}/simple_native_dir_test"

check(dir_create(test_dir, false))
check(is_dir(test_dir))
check(dir_remove_all(test_dir) == 0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
