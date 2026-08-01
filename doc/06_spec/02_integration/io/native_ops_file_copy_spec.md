# Native file copy operations

> Verifies the native file API can copy a temporary file and read the copied content through the Simple file-ops facade.

<!-- sdn-diagram:id=native_ops_file_copy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_file_copy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_file_copy_spec -> app
native_ops_file_copy_spec -> std
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

# Native file copy operations

Verifies the native file API can copy a temporary file and read the copied content through the Simple file-ops facade.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_file_copy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the native file API can copy a temporary file and read the copied
content through the Simple file-ops facade.

## Acceptance

- A source file can be written.
- The source file can be copied to a destination.
- The copied content matches and both files are removed.

## Scenarios

### Native File Ops

<details>
<summary>Advanced: copies files</summary>

#### copies files _(slow)_

- check
- check
   - Expected: file_read(dst).trim() equals `Copy test`
- check
- check


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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
