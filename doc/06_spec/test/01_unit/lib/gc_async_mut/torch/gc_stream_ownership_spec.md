# Gc Stream Ownership Specification

> <details>

<!-- sdn-diagram:id=gc_stream_ownership_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_stream_ownership_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_stream_ownership_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_stream_ownership_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Stream Ownership Specification

## Scenarios

### GC Stream Ownership

### 3-field Stream pattern

#### stream has handle, owns_handle, and device_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_stream(1, 0)
expect(s.handle).to_equal(1)
expect(s.owns_handle).to_equal(true)
expect(s.device_id).to_equal(0)
```

</details>

#### owned stream frees on drop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_stream(2, 0)
# Verify the stream would free (owns_handle is true)
expect(s.should_free()).to_equal(true)
```

</details>

#### borrowed stream does not free

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = MockStream(handle: 3, owns_handle: false, device_id: 0)
# Verify the stream would NOT free (owns_handle is false)
expect(s.should_free()).to_equal(false)
```

</details>

#### device id preserved across ownership

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_stream(4, 1)
expect(s.device()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/torch/gc_stream_ownership_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GC Stream Ownership
- 3-field Stream pattern

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
