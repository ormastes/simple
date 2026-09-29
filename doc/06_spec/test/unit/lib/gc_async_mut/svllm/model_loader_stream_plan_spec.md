# Model Loader Stream Plan Specification

> <details>

<!-- sdn-diagram:id=model_loader_stream_plan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=model_loader_stream_plan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

model_loader_stream_plan_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=model_loader_stream_plan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Stream Plan Specification

## Scenarios

### svLLM tensor stream plan

#### builds a plan-only single-segment read plan for one chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "test/fixtures/svllm/valid_pack"
val name = "tok_embeddings.weight"
expect(stream_plan_status(root, name)).to_equal("ok")
expect(stream_plan_execution_status(root, name)).to_equal("plan_only_not_scheduled")
expect(stream_plan_total_bytes(root, name)).to_equal(16)
expect(stream_plan_segment_count(root, name)).to_equal(1)
expect(stream_plan_segment_path(root, name, 0)).to_equal("data-000.bin")
expect(stream_plan_segment_offset(root, name, 0)).to_equal(0)
expect(stream_plan_segment_bytes(root, name, 0)).to_equal(16)
expect(stream_plan_segment_tensor_offset(root, name, 0)).to_equal(0)
expect(stream_plan_pin_requested(root, name)).to_equal(true)
expect(stream_plan_device_staging_requested(root, name)).to_equal(true)
```

</details>

#### splits a cross-chunk tensor span into ordered read segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "test/fixtures/svllm/cross_chunk_pack"
val name = "split.weight"
expect(stream_plan_status(root, name)).to_equal("ok")
expect(stream_plan_total_bytes(root, name)).to_equal(7)
expect(stream_plan_segment_count(root, name)).to_equal(2)
expect(stream_plan_segment_path(root, name, 0)).to_equal("data-000.bin")
expect(stream_plan_segment_offset(root, name, 0)).to_equal(1)
expect(stream_plan_segment_bytes(root, name, 0)).to_equal(4)
expect(stream_plan_segment_tensor_offset(root, name, 0)).to_equal(0)
expect(stream_plan_segment_path(root, name, 1)).to_equal("data-001.bin")
expect(stream_plan_segment_offset(root, name, 1)).to_equal(0)
expect(stream_plan_segment_bytes(root, name, 1)).to_equal(3)
expect(stream_plan_segment_tensor_offset(root, name, 1)).to_equal(4)
```

</details>

#### reports missing tensor names without returning a plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(stream_plan_status("test/fixtures/svllm/valid_pack", "missing.weight")).to_equal("tensor_not_found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/svllm/model_loader_stream_plan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svLLM tensor stream plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
