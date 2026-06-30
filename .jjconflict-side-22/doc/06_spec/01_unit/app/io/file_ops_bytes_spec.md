# File Ops Bytes Specification

> <details>

<!-- sdn-diagram:id=file_ops_bytes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_ops_bytes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_ops_bytes_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_ops_bytes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Ops Bytes Specification

## Scenarios

### app.io file byte operations

#### writes byte arrays through shared file ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple-file-write-bytes-spec.bin"
val (_out, _err, _code) = process_run("rm", ["-f", path])
expect(file_write_bytes(path, [65u8, 66u8, 67u8])).to_equal(true)
expect(file_read(path)).to_equal("ABC")
expect(file_read_bytes(path) ?? []).to_equal([65, 66, 67])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/file_ops_bytes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app.io file byte operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
