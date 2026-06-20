# Agent Dashboard Specification

> <details>

<!-- sdn-diagram:id=agent_dashboard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_dashboard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_dashboard_spec -> std
agent_dashboard_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_dashboard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Dashboard Specification

## Scenarios

### ide_agent_dashboard — existing surface

#### default lanes returns 3 lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lanes = ide_agent_dashboard_default_lanes()
expect(lanes.len()).to_equal(3)
```

</details>

#### spark lane is unavailable by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lanes = ide_agent_dashboard_default_lanes()
val spark = lanes.get(0)
expect(spark.provider).to_equal("spark")
expect(spark.status).to_equal("unavailable")
```

</details>

#### normal-implementation lane is ready by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lanes = ide_agent_dashboard_default_lanes()
val impl_lane = lanes.get(1)
expect(impl_lane.provider).to_equal("normal")
expect(impl_lane.status).to_equal("ready")
```

</details>

#### normal-review lane is ready by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lanes = ide_agent_dashboard_default_lanes()
val rev_lane = lanes.get(2)
expect(rev_lane.provider).to_equal("normal")
expect(rev_lane.role).to_equal("review")
expect(rev_lane.status).to_equal("ready")
```

</details>

#### default spark lane is structurally valid (correct provider/source/gate)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lanes = ide_agent_dashboard_default_lanes()
val spark = lanes.get(0)
# spark-research has the right provider/source/gate — structurally valid
expect(_ide_agent_dashboard_lane_valid(spark)).to_equal(true)
```

</details>

#### normal implementation lane is structurally valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lanes = ide_agent_dashboard_default_lanes()
expect(_ide_agent_dashboard_lane_valid(lanes.get(1))).to_equal(true)
```

</details>

#### base surface has non-zero blocked_count (spark-research is unavailable)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = ide_agent_dashboard_surface()
expect(surface.blocked_count > 0).to_equal(true)
```

</details>

#### base surface ready_for_integration is false when spark lane is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = ide_agent_dashboard_surface()
expect(surface.ready_for_integration).to_equal(false)
```

</details>

#### base surface has modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = ide_agent_dashboard_surface()
expect(surface.modes.len() > 0).to_equal(true)
```

</details>

#### summary contains tool count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ide_agent_dashboard_summary()
expect(s.starts_with("agent-dashboard:")).to_equal(true)
```

</details>

### ide_agent_dashboard — lane validity

#### lane with unknown provider is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = IdeAgentDashboardLane(
    lane_id: "x",
    provider: "unknown-prov",
    role: "r",
    status: "ready",
    requires_review: false,
    source_module: "assistant.control_plane",
    review_gate_id: "spark-output-reviewed",
    degraded_reason: ""
)
expect(_ide_agent_dashboard_lane_valid(bad)).to_equal(false)
```

</details>

#### lane with bad status is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = IdeAgentDashboardLane(
    lane_id: "x",
    provider: "normal",
    role: "r",
    status: "unknown-status",
    requires_review: false,
    source_module: "assistant.control_plane",
    review_gate_id: "normal-review-available",
    degraded_reason: ""
)
expect(_ide_agent_dashboard_lane_valid(bad)).to_equal(false)
```

</details>

#### svllm lane with correct fields is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offline_status = svllm_status_default()
val lane = ide_agent_dashboard_svllm_lane(offline_status)
expect(_ide_agent_dashboard_lane_valid(lane)).to_equal(true)
```

</details>

#### svllm lane with wrong source_module is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = IdeAgentDashboardLane(
    lane_id: "svllm-inference",
    provider: "svllm",
    role: "inference",
    status: "ready",
    requires_review: false,
    source_module: "assistant.control_plane",
    review_gate_id: "svllm-inference-ready",
    degraded_reason: ""
)
expect(_ide_agent_dashboard_lane_valid(bad)).to_equal(false)
```

</details>

#### svllm lane with wrong gate_id is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = IdeAgentDashboardLane(
    lane_id: "svllm-inference",
    provider: "svllm",
    role: "inference",
    status: "ready",
    requires_review: false,
    source_module: "std.gc_async_mut.svllm",
    review_gate_id: "spark-output-reviewed",
    degraded_reason: ""
)
expect(_ide_agent_dashboard_lane_valid(bad)).to_equal(false)
```

</details>

### ide_agent_dashboard — svllm lane mapping

#### ready svllm status maps to ready lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_status = svllm_status_from(true, true, true, true, true, "llama3")
val lane = ide_agent_dashboard_svllm_lane(ready_status)
expect(lane.status).to_equal("ready")
expect(lane.degraded_reason).to_equal("")
```

</details>

#### degraded svllm status maps to blocked lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# loader_ready=true, others false -> degraded (some flags true)
val degraded_status = svllm_status_from(false, true, false, false, false, "")
val lane = ide_agent_dashboard_svllm_lane(degraded_status)
expect(lane.status).to_equal("blocked")
```

</details>

#### degraded lane has first reason populated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val degraded_status = svllm_status_from(false, true, false, false, false, "")
val lane = ide_agent_dashboard_svllm_lane(degraded_status)
expect(lane.degraded_reason != "").to_equal(true)
```

</details>

#### offline svllm status maps to unavailable lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offline_status = svllm_status_default()
val lane = ide_agent_dashboard_svllm_lane(offline_status)
expect(lane.status).to_equal("unavailable")
```

</details>

#### offline lane degraded_reason is non-empty fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offline_status = svllm_status_default()
val lane = ide_agent_dashboard_svllm_lane(offline_status)
# reasons list is non-empty for offline (all 5 flags false)
expect(lane.degraded_reason != "").to_equal(true)
```

</details>

#### svllm lane has correct fixed fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offline_status = svllm_status_default()
val lane = ide_agent_dashboard_svllm_lane(offline_status)
expect(lane.lane_id).to_equal("svllm-inference")
expect(lane.provider).to_equal("svllm")
expect(lane.role).to_equal("inference")
expect(lane.requires_review).to_equal(false)
expect(lane.source_module).to_equal("std.gc_async_mut.svllm")
expect(lane.review_gate_id).to_equal("svllm-inference-ready")
```

</details>

#### empty reasons list uses svllm-{readiness} fallback for degraded

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Construct a SvllmStatus directly with degraded readiness but empty reasons
# to exercise the empty-reasons guard branch.
val manual_status = SvllmStatus(
    engine_id: "svllm",
    phase: "A1",
    served_model: "",
    pack_available: false,
    loader_ready: false,
    nvfs_ready: false,
    kv_cache_ready: false,
    model_loaded: false,
    readiness: "degraded",
    reasons: [],
    consumer_module: "app.ide.agent_dashboard"
)
val lane = ide_agent_dashboard_svllm_lane(manual_status)
expect(lane.status).to_equal("blocked")
expect(lane.degraded_reason).to_equal("svllm-degraded")
```

</details>

#### empty reasons list uses svllm-{readiness} fallback for offline

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manual_status = SvllmStatus(
    engine_id: "svllm",
    phase: "A1",
    served_model: "",
    pack_available: false,
    loader_ready: false,
    nvfs_ready: false,
    kv_cache_ready: false,
    model_loaded: false,
    readiness: "offline",
    reasons: [],
    consumer_module: "app.ide.agent_dashboard"
)
val lane = ide_agent_dashboard_svllm_lane(manual_status)
expect(lane.status).to_equal("unavailable")
expect(lane.degraded_reason).to_equal("svllm-offline")
```

</details>

### ide_agent_dashboard — svllm gate

#### ready svllm status produces ready gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_status = svllm_status_from(true, true, true, true, true, "llama3")
val gate = ide_agent_dashboard_svllm_gate(ready_status)
expect(gate.status).to_equal("ready")
expect(gate.reason).to_equal("")
```

</details>

#### offline svllm status produces missing gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offline_status = svllm_status_default()
val gate = ide_agent_dashboard_svllm_gate(offline_status)
expect(gate.status).to_equal("missing")
```

</details>

#### degraded svllm status produces missing gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val degraded_status = svllm_status_from(false, true, false, false, false, "")
val gate = ide_agent_dashboard_svllm_gate(degraded_status)
expect(gate.status).to_equal("missing")
```

</details>

#### gate is not required (optional infra)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offline_status = svllm_status_default()
val gate = ide_agent_dashboard_svllm_gate(offline_status)
expect(gate.required).to_equal(false)
```

</details>

#### gate has correct fixed fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offline_status = svllm_status_default()
val gate = ide_agent_dashboard_svllm_gate(offline_status)
expect(gate.gate_id).to_equal("svllm-inference-ready")
expect(gate.source_module).to_equal("std.gc_async_mut.svllm")
```

</details>

### ide_agent_dashboard — surface_with_svllm blocked-count semantics

#### offline svllm does not increase blocked_count vs base surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = editor_mcp_tools()
val lanes = ide_agent_dashboard_default_lanes()
val base = ide_agent_dashboard_surface_from_tools(tools, lanes)
val offline_status = svllm_status_default()
val with_svllm = ide_agent_dashboard_surface_with_svllm(tools, lanes, offline_status)
# offline svllm -> "reviewed" lane (non-blocking); gate is required:false
expect(with_svllm.blocked_count).to_equal(base.blocked_count)
```

</details>

#### degraded svllm increases blocked_count by 1 vs base

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = editor_mcp_tools()
val lanes = ide_agent_dashboard_default_lanes()
val base = ide_agent_dashboard_surface_from_tools(tools, lanes)
val degraded_status = svllm_status_from(false, true, false, false, false, "")
val with_svllm = ide_agent_dashboard_surface_with_svllm(tools, lanes, degraded_status)
# degraded svllm -> "blocked" lane (counts as +1); gate is required:false (no extra)
expect(with_svllm.blocked_count).to_equal(base.blocked_count + 1)
```

</details>

#### ready svllm does not increase blocked_count vs base

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = editor_mcp_tools()
val lanes = ide_agent_dashboard_default_lanes()
val base = ide_agent_dashboard_surface_from_tools(tools, lanes)
val ready_status = svllm_status_from(true, true, true, true, true, "llama3")
val with_svllm = ide_agent_dashboard_surface_with_svllm(tools, lanes, ready_status)
expect(with_svllm.blocked_count).to_equal(base.blocked_count)
```

</details>

#### surface_with_svllm has one more lane than base

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = editor_mcp_tools()
val lanes = ide_agent_dashboard_default_lanes()
val base = ide_agent_dashboard_surface_from_tools(tools, lanes)
val offline_status = svllm_status_default()
val with_svllm = ide_agent_dashboard_surface_with_svllm(tools, lanes, offline_status)
expect(with_svllm.lanes.len()).to_equal(base.lanes.len() + 1)
```

</details>

#### surface_with_svllm has one more gate than base

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = editor_mcp_tools()
val lanes = ide_agent_dashboard_default_lanes()
val base = ide_agent_dashboard_surface_from_tools(tools, lanes)
val offline_status = svllm_status_default()
val with_svllm = ide_agent_dashboard_surface_with_svllm(tools, lanes, offline_status)
expect(with_svllm.gates.len()).to_equal(base.gates.len() + 1)
```

</details>

#### surface_svllm() returns a valid surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = ide_agent_dashboard_surface_svllm()
expect(surface.app_id).to_equal("agent-dashboard")
expect(surface.lanes.len() > 0).to_equal(true)
expect(surface.gates.len() > 0).to_equal(true)
```

</details>

### ide_agent_dashboard — svllm summary

#### summary_svllm contains svllm readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ide_agent_dashboard_summary_svllm()
expect(s.starts_with("agent-dashboard:")).to_equal(true)
# default is offline; metrics tokens precede svllm= so ends_with still holds
val found = s.ends_with("svllm=offline")
expect(found).to_equal(true)
```

</details>

#### summary_svllm_for ready status ends_with svllm=ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_status = svllm_status_from(true, true, true, true, true, "llama3")
val s = ide_agent_dashboard_summary_svllm_for(ready_status)
expect(s.ends_with("svllm=ready")).to_equal(true)
```

</details>

#### summary_svllm_for offline status contains svllm_chunks= and svllm_tensors=

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ide_agent_dashboard_summary_svllm()
expect(s).to_contain("svllm_chunks=")
expect(s).to_contain("svllm_tensors=")
```

</details>

#### summary_svllm_for offline status has zero chunk and tensor counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ide_agent_dashboard_summary_svllm()
expect(s).to_contain("svllm_chunks=0")
expect(s).to_contain("svllm_tensors=0")
```

</details>

### ide_agent_dashboard — svllm metrics_line

#### metrics_line offline status has chunks=0 tensors=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offline_status = svllm_status_default()
val line = ide_agent_dashboard_svllm_metrics_line(offline_status)
expect(line.starts_with("svllm-metrics:")).to_equal(true)
expect(line).to_contain("chunks=0")
expect(line).to_contain("tensors=0")
expect(line).to_contain("pack_available=false")
```

</details>

#### metrics_line from real pack reflects pack cardinality

- tensors push
- tensors push
   - Expected: line.starts_with("svllm-metrics:") is true
   - Expected: status.chunk_count equals `expected_chunks`
   - Expected: status.tensor_count equals `expected_tensors`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a minimal 2-tensor pack via plan_chunks, derive status from it,
# then verify the metrics line reflects the actual chunk/tensor counts.
val t1 = TensorInfo(
    name: "embed.weight",
    shape: [32000, 4096],
    dtype: Dtype.F16,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 262144000
)
val t2 = TensorInfo(
    name: "lm_head.weight",
    shape: [32000, 4096],
    dtype: Dtype.F16,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 262144000
)
var tensors: [TensorInfo] = []
tensors.push(t1)
tensors.push(t2)
val pack = plan_chunks(tensors, 4096, 2097152)
val status = svllm_status_from_pack(pack, false, false, false, false, "")
val line = ide_agent_dashboard_svllm_metrics_line(status)
expect(line.starts_with("svllm-metrics:")).to_equal(true)
expect(line).to_contain("pack_available=true")
val expected_chunks = pack.chunks.len()
val expected_tensors = pack.tensors.len()
expect(status.chunk_count).to_equal(expected_chunks)
expect(status.tensor_count).to_equal(expected_tensors)
```

</details>

#### summary_svllm_for with pack status contains svllm_chunks and svllm_tensors

- tensors push
   - Expected: s.ends_with("svllm=ready") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = TensorInfo(
    name: "weight",
    shape: [128, 64],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 32768
)
var tensors: [TensorInfo] = []
tensors.push(t1)
val pack = plan_chunks(tensors, 4096, 2097152)
val status = svllm_status_from_pack(pack, true, true, true, true, "test-model")
val s = ide_agent_dashboard_summary_svllm_for(status)
expect(s).to_contain("svllm_chunks=")
expect(s).to_contain("svllm_tensors=")
# ends_with contract: line still ends with svllm=ready
expect(s.ends_with("svllm=ready")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/agent_dashboard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ide_agent_dashboard — existing surface
- ide_agent_dashboard — lane validity
- ide_agent_dashboard — svllm lane mapping
- ide_agent_dashboard — svllm gate
- ide_agent_dashboard — surface_with_svllm blocked-count semantics
- ide_agent_dashboard — svllm summary
- ide_agent_dashboard — svllm metrics_line

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
