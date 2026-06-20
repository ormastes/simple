# System Test - SvLLM Dashboard Metric Flow

> End-to-end metric flow test from TensorPack → SvllmStatus → IDE dashboard. Verifies that tensor/chunk cardinality flows through the complete observability pipeline and surfaces correctly in the dashboard metrics and summary lines.

<!-- sdn-diagram:id=svllm_dashboard_metric_flow_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svllm_dashboard_metric_flow_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svllm_dashboard_metric_flow_system_spec -> std
svllm_dashboard_metric_flow_system_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svllm_dashboard_metric_flow_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Test - SvLLM Dashboard Metric Flow

End-to-end metric flow test from TensorPack → SvllmStatus → IDE dashboard. Verifies that tensor/chunk cardinality flows through the complete observability pipeline and surfaces correctly in the dashboard metrics and summary lines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SVLLM-METRICS, #IDE-DASHBOARD-SVLLM |
| Category | ML / Observability / Metric Flow |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/03_system/tools/svllm_dashboard_metric_flow_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end metric flow test from TensorPack → SvllmStatus → IDE dashboard.
Verifies that tensor/chunk cardinality flows through the complete observability
pipeline and surfaces correctly in the dashboard metrics and summary lines.

## Metric Flow
1. TensorPack.plan_chunks produces tensors + chunks with real cardinality
2. svllm_status_from_pack(pack) → SvllmStatus with tensor_count/chunk_count
3. IDE dashboard imports SvllmStatus and surfaces counts in:
   - ide_agent_dashboard_svllm_metrics_line → "chunks=X tensors=Y"
   - ide_agent_dashboard_summary_svllm_for → "svllm_chunks=X svllm_tensors=Y"
   - ide_agent_dashboard_surface_svllm_for → lanes include "svllm-inference"

## Scenarios

### SvLLM Dashboard Metric Flow

#### plan_chunks produces multiple chunks for large tensors

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build 3 tensors with byte_len large enough to force multiple chunks.
# Preferred chunk size is 2 MiB (2097152 bytes).
# With 3 tensors of 1.5 MiB each:
#   - Tensor 0 (1.5M): placed at offset 0, chunk 0 grows to 1.5M
#   - Tensor 1 (1.5M): would be 3M total, exceeds 2.097M threshold
#     → closes chunk 0, starts chunk 1
#   - Tensor 2 (1.5M): would be 3M total again, closes chunk 1, starts chunk 2
# Result: 3 tensors, 3 chunks.

var tensors: [TensorInfo] = []
tensors.push(TensorInfo(
    name: "weight_0",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_1",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_2",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))

val pack = plan_chunks(tensors, 4096, 2097152)

# Verify the plan produced multiple chunks (not just one).
verify(pack.chunks.len() > 1)
# Verify all 3 tensors are in the pack.
verify(pack.tensors.len() == 3)
```

</details>

#### svllm_status_from_pack flows pack cardinality to status

- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build the same 3-tensor, multi-chunk pack.
var tensors: [TensorInfo] = []
tensors.push(TensorInfo(
    name: "weight_0",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_1",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_2",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))

val pack = plan_chunks(tensors, 4096, 2097152)
val status = svllm_status_from_pack(pack, true, true, true, true, "demo-model")

# Verify cardinality flowed through.
verify(status.tensor_count == pack.tensors.len())
verify(status.chunk_count == pack.chunks.len())
# Verify pack_available is set (we have chunks).
verify(status.pack_available == true)
# Verify the status is ready (all 5 flags true).
verify(status.readiness == "ready")
```

</details>

#### svllm_status_summary surfaces chunk and tensor counts

- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build the multi-chunk pack and status.
var tensors: [TensorInfo] = []
tensors.push(TensorInfo(
    name: "weight_0",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_1",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_2",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))

val pack = plan_chunks(tensors, 4096, 2097152)
val status = svllm_status_from_pack(pack, true, true, true, true, "demo-model")

# Get the summary line.
val summary = svllm_status_summary(status)

# Verify it contains the "chunks=" marker and the actual chunk count.
verify(summary.contains("chunks="))
val chunk_count_text = status.chunk_count.to_text()
verify(summary.contains(chunk_count_text))

# Verify it contains the "tensors=" marker and the actual tensor count.
verify(summary.contains("tensors="))
val tensor_count_text = status.tensor_count.to_text()
verify(summary.contains(tensor_count_text))
```

</details>

#### ide_agent_dashboard_svllm_metrics_line surfaces pack cardinality

- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build the multi-chunk pack and status.
var tensors: [TensorInfo] = []
tensors.push(TensorInfo(
    name: "weight_0",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_1",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_2",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))

val pack = plan_chunks(tensors, 4096, 2097152)
val status = svllm_status_from_pack(pack, true, true, true, true, "demo-model")

# Get the metrics line from the dashboard.
val metrics_line = ide_agent_dashboard_svllm_metrics_line(status)

# Verify the metrics line contains both chunk and tensor counts.
verify(metrics_line.contains("chunks="))
verify(metrics_line.contains("tensors="))
val chunk_count_text = status.chunk_count.to_text()
verify(metrics_line.contains(chunk_count_text))
val tensor_count_text = status.tensor_count.to_text()
verify(metrics_line.contains(tensor_count_text))
```

</details>

#### ide_agent_dashboard_summary_svllm_for surfaces chunk/tensor metrics

- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build the multi-chunk pack and status.
var tensors: [TensorInfo] = []
tensors.push(TensorInfo(
    name: "weight_0",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_1",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_2",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))

val pack = plan_chunks(tensors, 4096, 2097152)
val status = svllm_status_from_pack(pack, true, true, true, true, "demo-model")

# Get the dashboard summary line.
val summary = ide_agent_dashboard_summary_svllm_for(status)

# Verify the summary includes the svllm_chunks and svllm_tensors metrics.
verify(summary.contains("svllm_chunks="))
verify(summary.contains("svllm_tensors="))
# Verify it ends with the svllm readiness status.
verify(summary.ends_with("svllm=ready"))
```

</details>

#### ide_agent_dashboard_surface_svllm_for includes svllm-inference lane

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build the multi-chunk pack and status.
var tensors: [TensorInfo] = []
tensors.push(TensorInfo(
    name: "weight_0",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_1",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "weight_2",
    shape: [1500],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))

val pack = plan_chunks(tensors, 4096, 2097152)
val status = svllm_status_from_pack(pack, true, true, true, true, "demo-model")

# Get the dashboard surface.
val surface = ide_agent_dashboard_surface_svllm_for(status)

# Verify the surface has lanes.
verify(surface.lanes.len() > 0)

# Verify the svllm-inference lane is present.
var found_svllm_lane = false
for lane in surface.lanes:
    if lane.lane_id == "svllm-inference":
        found_svllm_lane = true

verify(found_svllm_lane)
```

</details>

#### metric flow end-to-end: pack → status → dashboard

- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Comprehensive end-to-end test: verify the complete flow
# from planning chunks through dashboard rendering.
var tensors: [TensorInfo] = []
tensors.push(TensorInfo(
    name: "embedding",
    shape: [2048, 768],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "attention",
    shape: [32, 64, 128],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))
tensors.push(TensorInfo(
    name: "output",
    shape: [512],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
))

# Step 1: Plan chunks.
val pack = plan_chunks(tensors, 4096, 2097152)
verify(pack.tensors.len() == 3)
verify(pack.chunks.len() > 1)

# Step 2: Build status from pack.
val status = svllm_status_from_pack(pack, true, true, true, true, "llama-7b")
verify(status.tensor_count == pack.tensors.len())
verify(status.chunk_count == pack.chunks.len())

# Step 3: Verify metrics flow to summary.
val summary = ide_agent_dashboard_summary_svllm_for(status)
val chunk_text = status.chunk_count.to_text()
val tensor_text = status.tensor_count.to_text()
verify(summary.contains("svllm_chunks=" + chunk_text))
verify(summary.contains("svllm_tensors=" + tensor_text))
verify(summary.ends_with("svllm=ready"))

# Step 4: Verify surface includes the lane.
val surface = ide_agent_dashboard_surface_svllm_for(status)
var found_lane = false
for lane in surface.lanes:
    if lane.lane_id == "svllm-inference":
        found_lane = true
verify(found_lane)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
