# Web Route GPU Offload Profiles

> These scenarios verify reusable web GPU offload profiles for coarse application payload work. Profiles bundle registry targets, queue defaults, budgets, GPU availability, and CPU fallback policy for web inference, embedding, ranking, and transform routes.

<!-- sdn-diagram:id=web_route_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_route_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_route_profile_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_route_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Route GPU Offload Profiles

These scenarios verify reusable web GPU offload profiles for coarse application payload work. Profiles bundle registry targets, queue defaults, budgets, GPU availability, and CPU fallback policy for web inference, embedding, ranking, and transform routes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/web_db_offload/web_route_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify reusable web GPU offload profiles for coarse application
payload work. Profiles bundle registry targets, queue defaults, budgets, GPU
availability, and CPU fallback policy for web inference, embedding, ranking,
and transform routes.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Web server code can reuse named GPU offload profiles.
- Inference profiles register only inference targets.
- All-web profiles register inference, embedding, rank, and transform targets.
- CPU-only profiles preserve authoritative CPU fallback.
- Proxy forwarding remains CPU-owned even through a GPU profile.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Use `web_gpu_profile_all` for a web process that has every coarse GPU route
target loaded, then call `web_gpu_profile_execute` after CPU routing and auth.

## Scenarios

### web route reusable GPU offload profiles

#### should dispatch inference with the inference profile

- Use an inference-only profile for /infer batches
   - Expected: profile.name equals `web-inference`
   - Expected: execution.submission.dispatch_target equals `gpu_web_inference_batch`
   - Expected: execution.cpu_body equals `cpu-infer`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use an inference-only profile for /infer batches")
val profile = web_gpu_profile_inference("cuda", 1, 4)
val execution = web_gpu_profile_execute(
    profile,
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    256,
    200,
    "cpu-infer"
)
expect(profile.name).to_equal("web-inference")
expect(web_gpu_route_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.dispatch_target).to_equal("gpu_web_inference_batch")
expect(execution.cpu_body).to_equal("cpu-infer")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(web_gpu_route_profile_allows_gpu(execution)).to_be(true)
expect(web_gpu_profile_execution_used_gpu(execution)).to_be(true)
expect(web_gpu_profile_execution_allows_gpu(execution)).to_be(true)
```

</details>

#### should advance web profile queue state across sequential executions

- Return the updated profile so web server code keeps queue accounting current
   - Expected: first.profile.queue_state.submitted_count equals `1`
   - Expected: first.profile.queue_state.completed_count equals `1`
   - Expected: first.profile.queue_state.gpu_hit_count equals `1`
   - Expected: second.profile.queue_state.submitted_count equals `2`
   - Expected: second.profile.queue_state.completed_count equals `2`
   - Expected: second.profile.queue_state.gpu_hit_count equals `2`
   - Expected: second.execution.cpu_body equals `cpu-infer-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return the updated profile so web server code keeps queue accounting current")
val profile = web_gpu_profile_inference("cuda", 1, 4)
val first = web_gpu_profile_execute_advancing(
    profile,
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    256,
    200,
    "cpu-infer-1"
)
val second = web_gpu_profile_execute_advancing(
    first.profile,
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    256,
    200,
    "cpu-infer-2"
)
expect(web_gpu_route_offload_used_gpu(first.execution)).to_be(true)
expect(web_gpu_route_offload_used_gpu(second.execution)).to_be(true)
expect(first.profile.queue_state.submitted_count).to_equal(1)
expect(first.profile.queue_state.completed_count).to_equal(1)
expect(first.profile.queue_state.gpu_hit_count).to_equal(1)
expect(second.profile.queue_state.submitted_count).to_equal(2)
expect(second.profile.queue_state.completed_count).to_equal(2)
expect(second.profile.queue_state.gpu_hit_count).to_equal(2)
expect(second.execution.cpu_body).to_equal("cpu-infer-2")
expect(second.execution.cpu_authoritative).to_be(true)
```

</details>

#### should export advancing web profile APIs through the web offload package

- Let web server code import profile advancement from std.web_db_offload
   - Expected: advanced.profile.queue_state.submitted_count equals `1`
   - Expected: advanced.profile.queue_state.completed_count equals `1`
   - Expected: advanced.execution.cpu_body equals `cpu-infer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let web server code import profile advancement from std.web_db_offload")
val profile = exported_web_gpu_profile_inference("cuda", 1, 4)
val advanced = exported_web_gpu_profile_execute_advancing(
    profile,
    "/infer",
    ExportedWebGpuRouteKind.Inference,
    16,
    256,
    200,
    "cpu-infer"
)
expect(advanced.profile.queue_state.submitted_count).to_equal(1)
expect(advanced.profile.queue_state.completed_count).to_equal(1)
expect(advanced.execution.cpu_body).to_equal("cpu-infer")
```

</details>

#### should execute web inference profile through strict measured device backend

- Allow web route GPU evidence only through native backend timing
   - Expected: result.execution.cpu_body equals `cpu-infer`
   - Expected: result.device_result.submission.dispatch_target equals `gpu_web_inference_batch`
   - Expected: result.device_result.reason equals `production-device-measured`
   - Expected: result.device_result.evidence.device_time_us equals `41`
   - Expected: result.profile.queue_state.gpu_hit_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Allow web route GPU evidence only through native backend timing")
val profile = web_gpu_profile_inference("cuda", 7, 4)
val backend = gpu_wdb_device_backend(
    "cuda",
    7,
    ["gpu_web_inference_batch"],
    true,
    "cuda-device-0"
)
val result = exported_web_gpu_profile_execute_device(
    profile,
    "/infer",
    ExportedWebGpuRouteKind.Inference,
    16,
    512,
    200,
    "cpu-infer",
    backend,
    7,
    100,
    180,
    41,
    "cuda-event"
)
expect(result.execution.cpu_body).to_equal("cpu-infer")
expect(result.execution.cpu_authoritative).to_be(true)
expect(result.device_result.submission.accepted).to_be(true)
expect(result.device_result.submission.dispatch_target).to_equal("gpu_web_inference_batch")
expect(result.device_result.production_device_claim).to_be(true)
expect(result.device_result.reason).to_equal("production-device-measured")
expect(result.device_result.evidence.backend_timing_valid).to_be(true)
expect(result.device_result.evidence.device_time_us).to_equal(41)
expect(result.profile.queue_state.gpu_hit_count).to_equal(1)
```

</details>

#### should replace web inference responses only after native candidates match

- Require production native timing and CPU response agreement before replacement
- gpu wdb device backend
   - Expected: result.execution.cpu_body equals `cpu-infer`
   - Expected: result.execution.validation_reason equals `production-gpu-web-response-match`
   - Expected: result.validation_reason equals `production-gpu-web-response-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native timing and CPU response agreement before replacement")
val profile = web_gpu_profile_inference("cuda", 7, 4)
val result = web_gpu_profile_execute_device_validated(
    profile,
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    512,
    200,
    "cpu-infer",
    gpu_wdb_device_backend("cuda", 7, ["gpu_web_inference_batch"], true, "cuda-device-0"),
    7,
    200,
    "cpu-infer",
    100,
    180,
    41,
    "cuda-event"
)
expect(result.execution.cpu_body).to_equal("cpu-infer")
expect(result.execution.cpu_authoritative).to_be(false)
expect(result.execution.gpu_dispatched).to_be(true)
expect(result.execution.gpu_candidate_validated).to_be(true)
expect(result.execution.validation_reason).to_equal("production-gpu-web-response-match")
expect(result.gpu_candidate_validated).to_be(true)
expect(result.validation_reason).to_equal("production-gpu-web-response-match")
expect(result.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep web inference responses CPU authoritative when native candidates mismatch

- Reject production web response replacement when status or body differs
- gpu wdb device backend
   - Expected: result.execution.cpu_body equals `cpu-infer`
   - Expected: result.execution.validation_reason equals `production-gpu-web-response-mismatch`
   - Expected: result.validation_reason equals `production-gpu-web-response-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject production web response replacement when status or body differs")
val profile = web_gpu_profile_inference("cuda", 7, 4)
val result = web_gpu_profile_execute_device_validated(
    profile,
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    512,
    200,
    "cpu-infer",
    gpu_wdb_device_backend("cuda", 7, ["gpu_web_inference_batch"], true, "cuda-device-0"),
    7,
    200,
    "gpu-infer",
    100,
    180,
    41,
    "cuda-event"
)
expect(result.execution.cpu_body).to_equal("cpu-infer")
expect(result.execution.cpu_authoritative).to_be(true)
expect(result.execution.gpu_dispatched).to_be(false)
expect(result.execution.gpu_candidate_validated).to_be(false)
expect(result.execution.validation_reason).to_equal("production-gpu-web-response-mismatch")
expect(result.gpu_candidate_validated).to_be(false)
expect(result.validation_reason).to_equal("production-gpu-web-response-mismatch")
expect(result.device_result.production_device_claim).to_be(true)
```

</details>

#### should replace embedding responses only after native candidates match

- Require production native timing and CPU response agreement before embedding replacement
- gpu wdb device backend
   - Expected: result.execution.cpu_body equals `cpu-embed`
   - Expected: result.execution.submission.dispatch_target equals `gpu_web_embedding_batch`
   - Expected: result.validation_reason equals `production-gpu-web-response-match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native timing and CPU response agreement before embedding replacement")
val profile = web_gpu_profile_embedding("cuda", 7, 4)
val result = web_gpu_profile_execute_device_validated(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    512,
    200,
    "cpu-embed",
    gpu_wdb_device_backend("cuda", 7, ["gpu_web_embedding_batch"], true, "cuda-device-0"),
    7,
    200,
    "cpu-embed",
    100,
    180,
    43,
    "cuda-event"
)
expect(result.execution.cpu_body).to_equal("cpu-embed")
expect(result.execution.cpu_authoritative).to_be(false)
expect(result.execution.gpu_dispatched).to_be(true)
expect(result.execution.submission.dispatch_target).to_equal("gpu_web_embedding_batch")
expect(result.gpu_candidate_validated).to_be(true)
expect(result.validation_reason).to_equal("production-gpu-web-response-match")
expect(result.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep rank responses CPU authoritative when native candidates mismatch

- Reject production rank response replacement when status or body differs
- gpu wdb device backend
   - Expected: result.execution.cpu_body equals `cpu-rank`
   - Expected: result.execution.submission.dispatch_target equals `gpu_web_rank_batch`
   - Expected: result.validation_reason equals `production-gpu-web-response-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject production rank response replacement when status or body differs")
val profile = web_gpu_profile_rank("cuda", 7, 4)
val result = web_gpu_profile_execute_device_validated(
    profile,
    "/rank",
    WebGpuRouteKind.Rank,
    32,
    256,
    200,
    "cpu-rank",
    gpu_wdb_device_backend("cuda", 7, ["gpu_web_rank_batch"], true, "cuda-device-0"),
    7,
    200,
    "gpu-rank",
    100,
    180,
    47,
    "cuda-event"
)
expect(result.execution.cpu_body).to_equal("cpu-rank")
expect(result.execution.cpu_authoritative).to_be(true)
expect(result.execution.gpu_dispatched).to_be(false)
expect(result.execution.submission.dispatch_target).to_equal("gpu_web_rank_batch")
expect(result.gpu_candidate_validated).to_be(false)
expect(result.validation_reason).to_equal("production-gpu-web-response-mismatch")
expect(result.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep perf-only web device runs from replacing CPU responses

- Reject web response replacement without production native timing
- gpu wdb device backend
   - Expected: result.execution.cpu_body equals `cpu-infer`
   - Expected: result.execution.validation_reason equals `production-device-not-measured`
   - Expected: result.validation_reason equals `production-device-not-measured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject web response replacement without production native timing")
val profile = web_gpu_profile_inference("cuda", 7, 4)
val result = web_gpu_profile_execute_device_validated(
    profile,
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    512,
    200,
    "cpu-infer",
    gpu_wdb_device_backend("mock", 7, ["gpu_web_inference_batch"], false, "mock-device"),
    7,
    200,
    "cpu-infer",
    100,
    180,
    41,
    "mock-clock"
)
expect(result.execution.cpu_body).to_equal("cpu-infer")
expect(result.execution.cpu_authoritative).to_be(true)
expect(result.execution.gpu_dispatched).to_be(false)
expect(result.execution.gpu_candidate_validated).to_be(false)
expect(result.execution.validation_reason).to_equal("production-device-not-measured")
expect(result.gpu_candidate_validated).to_be(false)
expect(result.validation_reason).to_equal("production-device-not-measured")
expect(result.device_result.production_device_claim).to_be(false)
```

</details>

#### should keep stale web native target generations on CPU fallback

- Prevent old web GPU kernels from producing production evidence
   - Expected: result.execution.cpu_body equals `cpu-infer`
   - Expected: result.device_result.submission.dispatch_target equals `cpu_fallback`
   - Expected: result.device_result.submission.reason equals `stale-generation`
   - Expected: result.profile.queue_state.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prevent old web GPU kernels from producing production evidence")
val profile = web_gpu_profile_inference("cuda", 7, 4)
val backend = gpu_wdb_device_backend(
    "cuda",
    7,
    ["gpu_web_inference_batch"],
    true,
    "cuda-device-0"
)
val result = web_gpu_profile_execute_device(
    profile,
    "/infer",
    WebGpuRouteKind.Inference,
    16,
    512,
    200,
    "cpu-infer",
    backend,
    8,
    100,
    180,
    41,
    "cuda-event"
)
expect(result.execution.cpu_body).to_equal("cpu-infer")
expect(result.device_result.submission.accepted).to_be(false)
expect(result.device_result.submission.dispatch_target).to_equal("cpu_fallback")
expect(result.device_result.submission.reason).to_equal("stale-generation")
expect(result.device_result.production_device_claim).to_be(false)
expect(result.device_result.evidence.backend_timing_valid).to_be(false)
expect(result.profile.queue_state.cpu_fallback_count).to_equal(1)
```

</details>

#### should not claim embedding GPU evidence from the inference profile

- Keep profile target registration scoped to loaded route libraries
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.cpu_body equals `cpu-embed`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep profile target registration scoped to loaded route libraries")
val profile = web_gpu_profile_inference("cuda", 1, 4)
val execution = web_gpu_profile_execute(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    256,
    200,
    "cpu-embed"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.cpu_body).to_equal("cpu-embed")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(web_gpu_route_profile_allows_gpu(execution)).to_be(false)
expect(web_gpu_profile_execution_used_gpu(execution)).to_be(false)
expect(web_gpu_profile_execution_allows_gpu(execution)).to_be(false)
```

</details>

#### should dispatch transform routes with the all-web profile

- Use all-web profile targets for image or payload transforms
   - Expected: execution.submission.dispatch_target equals `gpu_web_transform_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use all-web profile targets for image or payload transforms")
val profile = web_gpu_profile_all("cuda", 1, 4)
val execution = web_gpu_profile_execute(
    profile,
    "/image/transform",
    WebGpuRouteKind.Transform,
    8,
    2048,
    200,
    "cpu-transform"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(true)
expect(execution.submission.dispatch_target).to_equal("gpu_web_transform_batch")
expect(web_gpu_profile_execution_allows_gpu(execution)).to_be(true)
```

</details>

#### should replace transform responses only after native candidates match

- Require production native timing and CPU response agreement before transform replacement
- gpu wdb device backend
   - Expected: result.execution.cpu_body equals `cpu-transform`
   - Expected: result.validation_reason equals `production-gpu-web-response-match`
   - Expected: result.device_result.submission.dispatch_target equals `gpu_web_transform_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native timing and CPU response agreement before transform replacement")
val profile = web_gpu_profile_transform("cuda", 7, 4)
val result = web_gpu_profile_execute_device_validated(
    profile,
    "/image/transform",
    WebGpuRouteKind.Transform,
    8,
    2048,
    200,
    "cpu-transform",
    gpu_wdb_device_backend("cuda", 7, ["gpu_web_transform_batch"], true, "cuda-device-0"),
    7,
    200,
    "cpu-transform",
    100,
    180,
    41,
    "cuda-event"
)
expect(result.execution.cpu_body).to_equal("cpu-transform")
expect(result.execution.cpu_authoritative).to_be(false)
expect(result.execution.gpu_dispatched).to_be(true)
expect(result.gpu_candidate_validated).to_be(true)
expect(result.validation_reason).to_equal("production-gpu-web-response-match")
expect(result.device_result.production_device_claim).to_be(true)
expect(result.device_result.submission.dispatch_target).to_equal("gpu_web_transform_batch")
```

</details>

#### should keep transform responses CPU authoritative when native candidates mismatch

- Reject transform replacement when the GPU response differs from the CPU oracle
- gpu wdb device backend
   - Expected: result.execution.cpu_body equals `cpu-transform`
   - Expected: result.validation_reason equals `production-gpu-web-response-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject transform replacement when the GPU response differs from the CPU oracle")
val profile = web_gpu_profile_transform("cuda", 7, 4)
val result = web_gpu_profile_execute_device_validated(
    profile,
    "/image/transform",
    WebGpuRouteKind.Transform,
    8,
    2048,
    200,
    "cpu-transform",
    gpu_wdb_device_backend("cuda", 7, ["gpu_web_transform_batch"], true, "cuda-device-0"),
    7,
    200,
    "gpu-transform",
    100,
    180,
    41,
    "cuda-event"
)
expect(result.execution.cpu_body).to_equal("cpu-transform")
expect(result.execution.cpu_authoritative).to_be(true)
expect(result.execution.gpu_dispatched).to_be(false)
expect(result.gpu_candidate_validated).to_be(false)
expect(result.validation_reason).to_equal("production-gpu-web-response-mismatch")
expect(result.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep perf-only transform device runs from replacing CPU responses

- Reject transform response replacement without production native timing
- gpu wdb device backend
   - Expected: result.execution.cpu_body equals `cpu-transform`
   - Expected: result.validation_reason equals `production-device-not-measured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject transform response replacement without production native timing")
val profile = web_gpu_profile_transform("host-safe-mock", 7, 4)
val result = web_gpu_profile_execute_device_validated(
    profile,
    "/image/transform",
    WebGpuRouteKind.Transform,
    8,
    2048,
    200,
    "cpu-transform",
    gpu_wdb_device_backend("host-safe-mock", 7, ["gpu_web_transform_batch"], false, "mock-device"),
    7,
    200,
    "cpu-transform",
    100,
    180,
    41,
    "mock-clock"
)
expect(result.execution.cpu_body).to_equal("cpu-transform")
expect(result.execution.cpu_authoritative).to_be(true)
expect(result.execution.gpu_dispatched).to_be(false)
expect(result.gpu_candidate_validated).to_be(false)
expect(result.validation_reason).to_equal("production-device-not-measured")
expect(result.device_result.production_device_claim).to_be(false)
```

</details>

#### should keep CPU-only profiles on CPU fallback

- Disable GPU evidence without losing CPU response authority
   - Expected: execution.submission.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Disable GPU evidence without losing CPU response authority")
val profile = web_gpu_profile_cpu_only("web-maintenance")
val execution = web_gpu_profile_execute(
    profile,
    "/rank",
    WebGpuRouteKind.Rank,
    16,
    256,
    200,
    "cpu-rank"
)
expect(profile.gpu_available).to_be(false)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(web_gpu_profile_execution_used_gpu(execution)).to_be(false)
expect(web_gpu_profile_execution_allows_gpu(execution)).to_be(false)
expect(execution.submission.reason).to_equal("gpu-unavailable")
expect(execution.cpu_authoritative).to_be(true)
```

</details>

#### should defer small scheduled profile batches

- Use profile-level scheduling for batch accumulation
   - Expected: execution.schedule_action equals `GpuWdbScheduleAction.DeferForBatch`
   - Expected: execution.submission.dispatch_target equals `gpu_batch_accumulator`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile-level scheduling for batch accumulation")
val profile = web_gpu_profile_embedding("cuda", 1, 4)
val execution = web_gpu_profile_execute_scheduled(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    1,
    128,
    GpuWdbScheduleClass.Batch,
    true,
    200,
    "cpu-embed"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.schedule_action).to_equal(GpuWdbScheduleAction.DeferForBatch)
expect(execution.submission.dispatch_target).to_equal("gpu_batch_accumulator")
expect(web_gpu_profile_execution_allows_gpu(execution)).to_be(false)
```

</details>

#### should keep stale scheduled web target generations on CPU fallback

- Check expected target generation before scheduled route GPU dispatch
   - Expected: execution.schedule_action equals `GpuWdbScheduleAction.RunCpuFallback`
   - Expected: execution.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.submission.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check expected target generation before scheduled route GPU dispatch")
val profile = web_gpu_profile_embedding("cuda", 1, 4)
val execution = web_gpu_profile_execute_scheduled_for_generation(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    32,
    256,
    GpuWdbScheduleClass.Interactive,
    false,
    2,
    200,
    "cpu-embed"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.schedule_action).to_equal(GpuWdbScheduleAction.RunCpuFallback)
expect(execution.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.submission.reason).to_equal("stale-generation")
expect(web_gpu_profile_execution_allows_gpu(execution)).to_be(false)
```

</details>

#### should accumulate small scheduled profile batches

- Use profile defaults while mutating the reusable web batch accumulator
- gpu wdb batch accumulator
   - Expected: accumulated.execution.schedule_action equals `GpuWdbScheduleAction.DeferForBatch`
   - Expected: accumulated.execution.cpu_body equals `cpu-embed`
   - Expected: accumulated.execution.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile defaults while mutating the reusable web batch accumulator")
val profile = web_gpu_profile_embedding("cuda", 1, 4)
val accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    1,
    128,
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding),
    200,
    "cpu-embed"
)
expect(web_gpu_route_offload_used_gpu(accumulated.execution)).to_be(false)
expect(accumulated.execution.schedule_action).to_equal(GpuWdbScheduleAction.DeferForBatch)
expect(accumulated.execution.cpu_body).to_equal("cpu-embed")
expect(accumulated.execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(accumulated.accumulator_result.accepted).to_be(true)
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(1)
```

</details>

#### should leave profile accumulator unchanged for immediate web dispatch

- Do not accumulate profile work that is already GPU-worthy
- gpu wdb batch accumulator
   - Expected: accumulated.execution.submission.dispatch_target equals `gpu_web_transform_batch`
   - Expected: accumulated.accumulator_result.reason equals `route-not-deferred`
   - Expected: accumulated.accumulator_result.accumulator.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not accumulate profile work that is already GPU-worthy")
val profile = web_gpu_profile_all("cuda", 1, 4)
val accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/image/transform",
    WebGpuRouteKind.Transform,
    8,
    2048,
    GpuWdbScheduleClass.Batch,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebTransform),
    200,
    "cpu-transform"
)
expect(web_gpu_route_offload_used_gpu(accumulated.execution)).to_be(true)
expect(web_gpu_profile_execution_allows_gpu(accumulated.execution)).to_be(true)
expect(accumulated.execution.submission.dispatch_target).to_equal("gpu_web_transform_batch")
expect(accumulated.accumulator_result.accepted).to_be(false)
expect(accumulated.accumulator_result.reason).to_equal("route-not-deferred")
expect(accumulated.accumulator_result.accumulator.item_count).to_equal(0)
```

</details>

#### should flush accumulated web profile work through a registered GPU target

- Use profile queue and targets to submit a ready embedding batch
- gpu wdb batch accumulator
   - Expected: flushed.submission.dispatch_target equals `gpu_web_embedding_batch`
   - Expected: flushed.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile queue and targets to submit a ready embedding batch")
val profile = web_gpu_profile_embedding("cuda", 1, 4)
val first_accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    128,
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding),
    200,
    "cpu-embed"
)
val accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    128,
    GpuWdbScheduleClass.Background,
    first_accumulated.accumulator_result.accumulator,
    200,
    "cpu-embed"
)
val flushed = web_gpu_profile_flush_accumulator_current(
    profile,
    accumulated.accumulator_result.accumulator
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(true)
expect(flushed.submission.dispatch_target).to_equal("gpu_web_embedding_batch")
expect(flushed.accumulator_after.item_count).to_equal(0)
```

</details>

#### should advance web profile queue state after accumulator flush

- Return a profile with queued batch pressure after flushing accumulated work
- gpu wdb batch accumulator
   - Expected: flushed.flush.submission.dispatch_target equals `gpu_web_embedding_batch`
   - Expected: flushed.profile.queue_state.submitted_count equals `1`
   - Expected: flushed.profile.queue_state.gpu_hit_count equals `1`
   - Expected: flushed.profile.queue_state.queue_depth equals `1`
   - Expected: flushed.profile.queue_state.completed_count equals `0`
   - Expected: flushed.flush.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return a profile with queued batch pressure after flushing accumulated work")
val profile = web_gpu_profile_embedding("cuda", 1, 4)
val first_accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    128,
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding),
    200,
    "cpu-embed"
)
val accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    128,
    GpuWdbScheduleClass.Background,
    first_accumulated.accumulator_result.accumulator,
    200,
    "cpu-embed"
)
val flushed = web_gpu_profile_flush_accumulator_current_advancing(
    profile,
    accumulated.accumulator_result.accumulator
)
expect(flushed.flush.attempted).to_be(true)
expect(flushed.flush.submission.accepted).to_be(true)
expect(flushed.flush.submission.dispatch_target).to_equal("gpu_web_embedding_batch")
expect(flushed.profile.queue_state.submitted_count).to_equal(1)
expect(flushed.profile.queue_state.gpu_hit_count).to_equal(1)
expect(flushed.profile.queue_state.queue_depth).to_equal(1)
expect(flushed.profile.queue_state.completed_count).to_equal(0)
expect(flushed.flush.accumulator_after.item_count).to_equal(0)
```

</details>

#### should complete web profile flushed submissions and release queue pressure

- Use profile-level completion after a queued GPU batch finishes
- gpu wdb batch accumulator
   - Expected: completed.queue_state.submitted_count equals `1`
   - Expected: completed.queue_state.gpu_hit_count equals `1`
   - Expected: completed.queue_state.queue_depth equals `0`
   - Expected: completed.queue_state.completed_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use profile-level completion after a queued GPU batch finishes")
val profile = web_gpu_profile_embedding("cuda", 1, 4)
val first_accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    128,
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding),
    200,
    "cpu-embed"
)
val accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    16,
    128,
    GpuWdbScheduleClass.Background,
    first_accumulated.accumulator_result.accumulator,
    200,
    "cpu-embed"
)
val flushed = web_gpu_profile_flush_accumulator_current_advancing(
    profile,
    accumulated.accumulator_result.accumulator
)
val completed = web_gpu_profile_complete_submission(
    flushed.profile,
    flushed.flush.submission
)
expect(completed.queue_state.submitted_count).to_equal(1)
expect(completed.queue_state.gpu_hit_count).to_equal(1)
expect(completed.queue_state.queue_depth).to_equal(0)
expect(completed.queue_state.completed_count).to_equal(1)
```

</details>

#### should flush stale web profile target generations to CPU fallback

- Use the profile registry generation guard before reporting GPU evidence
- gpu wdb batch accumulator
   - Expected: flushed.submission.dispatch_target equals `cpu_fallback`
   - Expected: flushed.reason equals `stale-generation`
   - Expected: flushed.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use the profile registry generation guard before reporting GPU evidence")
val profile = web_gpu_profile_embedding("cuda", 1, 4)
val accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/embed",
    WebGpuRouteKind.Embedding,
    32,
    128,
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding),
    200,
    "cpu-embed"
)
val flushed = web_gpu_profile_flush_accumulator_for_generation(
    profile,
    accumulated.accumulator_result.accumulator,
    2
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(false)
expect(flushed.submission.dispatch_target).to_equal("cpu_fallback")
expect(flushed.reason).to_equal("stale-generation")
expect(flushed.accumulator_after.item_count).to_equal(0)
```

</details>

#### should clear accumulated web profile work after CPU fallback handles it

- Avoid retrying handled work when the profile lacks a matching target
- gpu wdb batch accumulator
   - Expected: flushed.submission.dispatch_target equals `cpu_fallback`
   - Expected: flushed.reason equals `gpu-unavailable`
   - Expected: flushed.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid retrying handled work when the profile lacks a matching target")
val profile = web_gpu_profile_inference("cuda", 1, 4)
val accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/rank",
    WebGpuRouteKind.Rank,
    32,
    128,
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebRank),
    200,
    "cpu-rank"
)
val flushed = web_gpu_profile_flush_accumulator_current(
    profile,
    accumulated.accumulator_result.accumulator
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(false)
expect(flushed.submission.dispatch_target).to_equal("cpu_fallback")
expect(flushed.reason).to_equal("gpu-unavailable")
expect(flushed.accumulator_after.item_count).to_equal(0)
```

</details>

#### should retain accumulated web profile work after hard reject

- Keep rejected accumulated work visible when CPU fallback is disabled
- gpu wdb batch accumulator
   - Expected: flushed.submission.execution.decision.path equals `GpuWdbDecisionPath.Reject`
   - Expected: flushed.reason equals `cpu-fallback-required`
   - Expected: flushed.accumulator_after.item_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep rejected accumulated work visible when CPU fallback is disabled")
val profile = web_gpu_profile(
    "unsafe-web",
    "cuda",
    1,
    4,
    ["gpu_web_transform_batch"],
    GpuWdbBudget(
        max_queue_depth: 64,
        max_batch_bytes: 1024 * 1024,
        min_gpu_batch_bytes: 1024
    ),
    true,
    false
)
val accumulated = web_gpu_profile_execute_accumulating(
    profile,
    "/image/transform",
    WebGpuRouteKind.Transform,
    1,
    128,
    GpuWdbScheduleClass.Background,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebTransform),
    200,
    "cpu-transform"
)
val flushed = web_gpu_profile_flush_accumulator_current(
    profile,
    accumulated.accumulator_result.accumulator
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.execution.decision.path).to_equal(GpuWdbDecisionPath.Reject)
expect(flushed.reason).to_equal("cpu-fallback-required")
expect(flushed.accumulator_after.item_count).to_equal(1)
```

</details>

#### should keep proxy forwarding on CPU through all-web profiles

- Do not let profile registration offload HTTP proxy control-plane work
   - Expected: execution.submission.execution.decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: execution.submission.reason equals `control-plane-stays-on-cpu`
   - Expected: execution.profile.data_path equals `GpuWdbCoarseDataPath.CpuOnly`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not let profile registration offload HTTP proxy control-plane work")
val profile = web_gpu_profile_all("cuda", 1, 4)
val execution = web_gpu_profile_execute(
    profile,
    "/api/",
    WebGpuRouteKind.ProxyForwarding,
    16,
    256,
    502,
    "proxy-cpu"
)
expect(web_gpu_route_offload_used_gpu(execution)).to_be(false)
expect(execution.submission.execution.decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(execution.submission.reason).to_equal("control-plane-stays-on-cpu")
expect(execution.profile.data_path).to_equal(GpuWdbCoarseDataPath.CpuOnly)
expect(web_gpu_route_profile_allows_gpu(execution)).to_be(false)
expect(web_gpu_profile_execution_allows_gpu(execution)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
