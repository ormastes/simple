# Web Route GPU Offload

> These scenarios verify the reusable web route offload boundary. It admits only coarse payload work such as inference, embedding, ranking, and transform batches. HTTP parsing, routing, reverse proxy forwarding, and control-plane responses stay CPU-owned.

<!-- sdn-diagram:id=web_route_gpu_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_route_gpu_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_route_gpu_offload_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_route_gpu_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Route GPU Offload

These scenarios verify the reusable web route offload boundary. It admits only coarse payload work such as inference, embedding, ranking, and transform batches. HTTP parsing, routing, reverse proxy forwarding, and control-plane responses stay CPU-owned.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_gpu_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the reusable web route offload boundary. It admits only
coarse payload work such as inference, embedding, ranking, and transform
batches. HTTP parsing, routing, reverse proxy forwarding, and control-plane
responses stay CPU-owned.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Web inference routes may use `gpu_web_inference_batch`.
- Embedding routes may use `gpu_web_embedding_batch`.
- Ranking routes may use `gpu_web_rank_batch`.
- Transform routes may use `gpu_web_transform_batch`.
- Proxy forwarding and HTTP control-plane work must not dispatch to GPU.
- CPU response data remains authoritative.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Use this adapter after a CPU worker has accepted TCP, parsed HTTP, routed the
request, authenticated it, and identified a GPU-worthy route such as `/infer`,
`/embed`, `/rank`, or `/image/transform`.

## Scenarios

### web route GPU offload adapter

#### should map web route kinds to reusable GPU work kinds

- Map public route kinds to shared web/db work kinds
   - Expected: web_gpu_route_work_kind(WebGpuRouteKind.Inference) equals `GpuWdbWorkKind.WebInference`
   - Expected: web_gpu_route_work_kind(WebGpuRouteKind.Embedding) equals `GpuWdbWorkKind.WebEmbedding`
   - Expected: web_gpu_route_work_kind(WebGpuRouteKind.Rank) equals `GpuWdbWorkKind.WebRank`
   - Expected: web_gpu_route_work_kind(WebGpuRouteKind.Transform) equals `GpuWdbWorkKind.WebTransform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Map public route kinds to shared web/db work kinds")
expect(web_gpu_route_work_kind(WebGpuRouteKind.Inference)).to_equal(GpuWdbWorkKind.WebInference)
expect(web_gpu_route_work_kind(WebGpuRouteKind.Embedding)).to_equal(GpuWdbWorkKind.WebEmbedding)
expect(web_gpu_route_work_kind(WebGpuRouteKind.Rank)).to_equal(GpuWdbWorkKind.WebRank)
expect(web_gpu_route_work_kind(WebGpuRouteKind.Transform)).to_equal(GpuWdbWorkKind.WebTransform)
```

</details>

#### should estimate payload bytes from item count and item size

- Estimate a route batch payload
   - Expected: web_gpu_route_estimated_payload_bytes(16, 256) equals `4096`
   - Expected: web_gpu_route_estimated_payload_bytes(0, 256) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Estimate a route batch payload")
expect(web_gpu_route_estimated_payload_bytes(16, 256)).to_equal(4096)
expect(web_gpu_route_estimated_payload_bytes(0, 256)).to_equal(0)
```

</details>

#### should dispatch registered inference routes through GPU accounting

- Submit an inference route to the registered GPU target
- gpu wdb queue initial
- web route budget
   - Expected: execution.submission.dispatch_target equals `gpu_web_inference_batch`
   - Expected: execution.state_after.completed_count equals `1`
   - Expected: execution.cpu_status equals `200`
   - Expected: execution.cpu_body equals `cpu-result`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit an inference route to the registered GPU target")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_inference_batch"])
val execution = web_gpu_route_offload_execute(
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    256,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    web_route_budget(),
    200,
    "cpu-result"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.dispatch_target).to_equal("gpu_web_inference_batch")
expect(execution.state_after.completed_count).to_equal(1)
expect(execution.cpu_status).to_equal(200)
expect(execution.cpu_body).to_equal("cpu-result")
expect(execution.cpu_authoritative).to_be(true)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(execution.profile.pinned_host_required).to_be(true)
expect(web_gpu_route_profile_allows_gpu(execution)).to_be(true)
```

</details>

#### should fall back when embedding target is not registered

- Avoid fake GPU evidence without a registered embedding target
- gpu wdb queue initial
- gpu wdb library empty
- web route budget
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `gpu-unavailable`
   - Expected: execution.state_after.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid fake GPU evidence without a registered embedding target")
val execution = web_gpu_route_offload_execute(
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    256,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_empty(),
    true,
    true,
    web_route_budget(),
    200,
    "cpu-embedding"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("gpu-unavailable")
expect(execution.state_after.cpu_fallback_count).to_equal(1)
```

</details>

#### should keep tiny rank batches on CPU

- Reject tiny batches for GPU performance claims
- gpu wdb queue initial
- web route budget
   - Expected: execution.submission.reason equals `batch-too-small`
   - Expected: execution.submission.stream_id equals `-1`
   - Expected: execution.schedule_action equals `GpuWdbScheduleAction.RunCpuFallback`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject tiny batches for GPU performance claims")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_rank_batch"])
val execution = web_gpu_route_offload_execute(
    "/rank",
    WebGpuRouteKind.Rank,
    1,
    128,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    web_route_budget(),
    200,
    "cpu-rank"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.reason).to_equal("batch-too-small")
expect(execution.submission.stream_id).to_equal(-1)
expect(execution.schedule_action).to_equal(GpuWdbScheduleAction.RunCpuFallback)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(web_gpu_route_profile_allows_gpu(execution)).to_be(false)
```

</details>

#### should defer tiny batchable embedding routes to the accumulator

- Use the shared scheduler before mutating GPU queue state
- gpu wdb queue initial
- web route budget
   - Expected: execution.schedule_action equals `GpuWdbScheduleAction.DeferForBatch`
   - Expected: execution.submission.dispatch_target equals `gpu_batch_accumulator`
   - Expected: execution.submission.reason equals `batch-too-small-defer`
   - Expected: execution.state_after.queue_depth equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the shared scheduler before mutating GPU queue state")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_embedding_batch"])
val execution = web_gpu_route_offload_execute_scheduled(
    "/embed",
    WebGpuRouteKind.Embedding,
    1,
    128,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    web_route_budget(),
    GpuWdbScheduleClass.Batch,
    true,
    200,
    "cpu-embedding"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.schedule_action).to_equal(GpuWdbScheduleAction.DeferForBatch)
expect(execution.submission.dispatch_target).to_equal("gpu_batch_accumulator")
expect(execution.submission.reason).to_equal("batch-too-small-defer")
expect(execution.state_after.queue_depth).to_equal(0)
```

</details>

#### should keep stale route target generations on CPU fallback

- Bind scheduled route GPU dispatch to an expected target generation
- gpu wdb queue initial
- web route budget
   - Expected: execution.schedule_action equals `GpuWdbScheduleAction.RunCpuFallback`
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `stale-generation`
   - Expected: execution.state_after.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind scheduled route GPU dispatch to an expected target generation")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_embedding_batch"])
val execution = web_gpu_route_offload_execute_scheduled_with_generation(
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    256,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    2,
    true,
    web_route_budget(),
    GpuWdbScheduleClass.Interactive,
    false,
    200,
    "cpu-embedding"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.schedule_action).to_equal(GpuWdbScheduleAction.RunCpuFallback)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("stale-generation")
expect(execution.state_after.cpu_fallback_count).to_equal(1)
```

</details>

#### should add deferred embedding routes to the reusable accumulator

- Preserve CPU response authority while accumulating tiny GPU work
- gpu wdb queue initial
- web route budget
- gpu wdb batch accumulator
   - Expected: accumulated.execution.schedule_action equals `GpuWdbScheduleAction.DeferForBatch`
   - Expected: accumulated.execution.cpu_body equals `cpu-embedding`
   - Expected: accumulated.execution.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve CPU response authority while accumulating tiny GPU work")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_embedding_batch"])
val accumulated = web_gpu_route_offload_execute_accumulating(
    "/embed",
    WebGpuRouteKind.Embedding,
    1,
    128,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    web_route_budget(),
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding),
    200,
    "cpu-embedding"
)
expect(accumulated.execution.schedule_action).to_equal(GpuWdbScheduleAction.DeferForBatch)
expect(accumulated.execution.cpu_authoritative).to_be(true)
expect(accumulated.execution.cpu_body).to_equal("cpu-embedding")
expect(accumulated.execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(accumulated.accumulator_result.accepted).to_be(true)
expect(accumulated.accumulator_result.should_flush).to_be(false)
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(1)
```

</details>

#### should not accumulate web route work that dispatches immediately

- Keep accumulator state unchanged for GPU-worthy route batches
- gpu wdb queue initial
- web route budget
- gpu wdb batch accumulator
   - Expected: accumulated.execution.schedule_action equals `GpuWdbScheduleAction.DispatchGpu`
   - Expected: accumulated.accumulator_result.reason equals `route-not-deferred`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep accumulator state unchanged for GPU-worthy route batches")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_inference_batch"])
val accumulated = web_gpu_route_offload_execute_accumulating(
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    256,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    web_route_budget(),
    GpuWdbScheduleClass.Batch,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebInference),
    200,
    "cpu-infer"
)
expect(accumulated.execution.schedule_action).to_equal(GpuWdbScheduleAction.DispatchGpu)
expect(accumulated.accumulator_result.accepted).to_be(false)
expect(accumulated.accumulator_result.reason).to_equal("route-not-deferred")
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(0)
```

</details>

#### should keep proxy forwarding on the CPU even if a target is registered

- Preserve the reverse proxy as CPU control-plane work
- gpu wdb queue initial
- web route budget
   - Expected: execution.submission.execution.decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: execution.submission.reason equals `control-plane-stays-on-cpu`
   - Expected: execution.cpu_status equals `502`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.CpuOnly`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve the reverse proxy as CPU control-plane work")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["cpu_proxy_stream"])
val execution = web_gpu_route_offload_execute(
    "/api/",
    WebGpuRouteKind.ProxyForwarding,
    16,
    256,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    web_route_budget(),
    502,
    "proxy handled on cpu"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.execution.decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(execution.submission.reason).to_equal("control-plane-stays-on-cpu")
expect(execution.cpu_status).to_equal(502)
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.CpuOnly)
expect(web_gpu_route_profile_allows_gpu(execution)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
