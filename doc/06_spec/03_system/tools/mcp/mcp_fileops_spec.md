# Mcp Fileops Specification

> <details>

<!-- sdn-diagram:id=mcp_fileops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_fileops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_fileops_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_fileops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Fileops Specification

## Scenarios

### MCP file operations

#### creates, reads, overwrites, and deletes a file through runtime file ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content1 = "Initial content\n"
val content2 = "Updated content\n"

expect(file_write(TEST_FILE, content1)).to_equal(true)
expect(file_exists(TEST_FILE)).to_equal(true)
expect(file_read(TEST_FILE)).to_equal(content1)

expect(file_write(TEST_FILE, content2)).to_equal(true)
expect(file_read(TEST_FILE)).to_equal(content2)

expect(file_delete(TEST_FILE)).to_equal(true)
expect(file_exists(TEST_FILE)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | MCP |
| Status | Active |
| Source | `test/03_system/tools/mcp/mcp_fileops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP file operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
