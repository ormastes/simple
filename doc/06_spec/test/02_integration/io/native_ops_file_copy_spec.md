# Native Ops File Copy Specification

> <details>

<!-- sdn-diagram:id=native_ops_file_copy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_file_copy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_file_copy_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_ops_file_copy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Ops File Copy Specification

## Scenarios

### Native File Ops

<details>
<summary>Advanced: copies files</summary>

#### copies files _(slow)_

1. check
2. check
   - Expected: file_read(dst).trim() equals `Copy test`
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "{tmp}/simple_copy_src.txt"
val dst = "{tmp}/simple_copy_dst.txt"

check(file_write(src, "Copy test"))
check(file_copy(src, dst))
expect(file_read(dst).trim()).to_equal("Copy test")
check(file_delete(src))
check(file_delete(dst))
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_file_copy_spec.spl` |
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
