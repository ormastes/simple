# Native file size operations

> Verifies the native file API can write a temporary file, report its size through the Simple file-ops facade, and delete the file.

<!-- sdn-diagram:id=native_ops_file_size_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_file_size_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_file_size_spec -> app
native_ops_file_size_spec -> std
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

# Native file size operations

Verifies the native file API can write a temporary file, report its size through the Simple file-ops facade, and delete the file.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_file_size_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the native file API can write a temporary file, report its size through
the Simple file-ops facade, and delete the file.

## Acceptance

- A temporary file can be written in the host temp directory.
- `file_size_raw` reports the expected size.
- The temporary file is removed after the check.

## Scenarios

### Native File Ops

<details>
<summary>Advanced: gets file size</summary>

#### gets file size _(slow)_

- check
   - Expected: file_size_raw(test_file) equals `6`
- check


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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
