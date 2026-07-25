# Native file read/write operations

> Verifies the native file API can write, detect, read, and delete a temporary text file through the Simple file-ops facade.

<!-- sdn-diagram:id=native_ops_file_read_write_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_file_read_write_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_file_read_write_spec -> app
native_ops_file_read_write_spec -> std
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

# Native file read/write operations

Verifies the native file API can write, detect, read, and delete a temporary text file through the Simple file-ops facade.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_file_read_write_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the native file API can write, detect, read, and delete a temporary
text file through the Simple file-ops facade.

## Acceptance

- A temporary file can be written.
- The file exists and reads back with the expected content.
- The file can be deleted and no longer exists.

## Scenarios

### Native File Ops

<details>
<summary>Advanced: creates and reads files</summary>

#### creates and reads files _(slow)_

- check
- check
   - Expected: file_read(test_file).trim() equals `content`
- check
- check


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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
