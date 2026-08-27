# Engine2d Readback Metadata Specification

> <details>

<!-- sdn-diagram:id=engine2d_readback_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_readback_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_readback_metadata_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_readback_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Readback Metadata Specification

## Scenarios

### no-GC Engine2D readback metadata

#### preserves source, backend handle, pixel count, and checksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readback = engine2d_readback_with_handle([1u32, 2u32, 3u32], "device_readback", 77)

expect(readback.source).to_equal("device_readback")
expect(readback.backend_handle).to_equal(77)
expect(readback.pixel_count).to_equal(3)
expect(readback.checksum).to_equal(6)
```

</details>

#### keeps zero-handle metadata for CPU mirror readbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readback = engine2d_readback([9u32], "cpu_mirror")

expect(readback.source).to_equal("cpu_mirror")
expect(readback.backend_handle).to_equal(0)
expect(readback.pixel_count).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/engine2d_readback_metadata_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- no-GC Engine2D readback metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
