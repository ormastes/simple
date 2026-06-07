# Native Ops File Read Write Specification

> <details>

<!-- sdn-diagram:id=native_ops_file_read_write_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_file_read_write_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_file_read_write_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_ops_file_read_write_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Ops File Read Write Specification

## Scenarios

### Native File Ops

<details>
<summary>Advanced: creates and reads files</summary>

#### creates and reads files _(slow)_

1. check
2. check
   - Expected: file_read(test_file).trim() equals `content`
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "{tmp}/simple_native_file_test.txt"
val content = "Hello from native SFFI!"

check(file_write(test_file, content))
check(file_exists(test_file))
expect(file_read(test_file).trim()).to_equal(content)
check(file_delete(test_file))
check(not file_exists(test_file))
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_file_read_write_spec.spl` |
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
