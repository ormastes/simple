# Native Ops Dir Recursive Specification

> <details>

<!-- sdn-diagram:id=native_ops_dir_recursive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_dir_recursive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_dir_recursive_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_ops_dir_recursive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Ops Dir Recursive Specification

## Scenarios

### Native Directory Ops

<details>
<summary>Advanced: creates nested directories recursively</summary>

#### creates nested directories recursively _(slow)_

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "{tmp}/simple_native_deep/sub1/sub2"

# rt_dir_create not available in bootstrap runtime, use shell mkdir -p
check(shell_mkdir_p(test_dir))
check(is_dir(test_dir))
check(shell_rm_rf("{tmp}/simple_native_deep"))
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_dir_recursive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native Directory Ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
