# Native Ops File Size Specification

> <details>

<!-- sdn-diagram:id=native_ops_file_size_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_file_size_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_file_size_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_ops_file_size_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Ops File Size Specification

## Scenarios

### Native File Ops

<details>
<summary>Advanced: gets file size</summary>

#### gets file size _(slow)_

1. check
   - Expected: file_size_raw(test_file) equals `6`
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "{tmp}/simple_size_test.txt"

check(file_write(test_file, "12345"))
expect(file_size_raw(test_file)).to_equal(6)
check(file_delete(test_file))
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_file_size_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native File Ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
