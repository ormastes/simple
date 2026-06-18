# Web Framework GPU Route Offload

> These scenarios verify the controller-facing GPU route offload hook. Framework controllers can keep their normal CPU response as authoritative while submitting coarse GPU-worthy route batches through the shared web/db queue and registry.

<!-- sdn-diagram:id=gpu_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_offload_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Framework GPU Route Offload

These scenarios verify the controller-facing GPU route offload hook. Framework controllers can keep their normal CPU response as authoritative while submitting coarse GPU-worthy route batches through the shared web/db queue and registry.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/web_framework/gpu_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the controller-facing GPU route offload hook. Framework
controllers can keep their normal CPU response as authoritative while submitting
coarse GPU-worthy route batches through the shared web/db queue and registry.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Controller actions can opt into inference, embedding, rank, or transform GPU
  route kinds.
- Per-request `gpu_items` and `gpu_bytes_per_item` params may size a batch.
- Missing GPU targets must fall back to CPU.
- The HTTP response returned by the controller remains authoritative.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Create a `WebFrameworkGpuRouteConfig` for an action such as
`InferenceController#create`, compute the normal CPU response, then pass both to
`web_framework_gpu_route_execute`.

## Scenarios

### web framework GPU route offload

#### should match configured controller action

- Match a controller/action pair before applying offload policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match a controller/action pair before applying offload policy")
val config = web_framework_gpu_route_config("infer", "create", WebGpuRouteKind.Inference, 16, 256)
expect(web_framework_gpu_route_matches(config, "infer", "create")).to_be(true)
expect(web_framework_gpu_route_matches(config, "infer", "show")).to_be(false)
```

</details>

#### should size batches from request params when present

- Read GPU batch sizing params from the controller context
   - Expected: web_framework_gpu_item_count(ctx, config) equals `32`
   - Expected: web_framework_gpu_bytes_per_item(ctx, config) equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read GPU batch sizing params from the controller context")
val config = web_framework_gpu_route_config("infer", "create", WebGpuRouteKind.Inference, 16, 256)
val ctx = wf_context("/infer", {"gpu_items": "32", "gpu_bytes_per_item": "128"})
expect(web_framework_gpu_item_count(ctx, config)).to_equal(32)
expect(web_framework_gpu_bytes_per_item(ctx, config)).to_equal(128)
```

</details>

#### should dispatch registered inference controller work to GPU accounting

- Keep the controller response authoritative while recording GPU dispatch
- gpu wdb queue initial
- wf budget
   - Expected: execution.offload.submission.dispatch_target equals `gpu_web_inference_batch`
   - Expected: execution.response.status equals `200`
   - Expected: execution.response.body equals `{"ok":true}`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep the controller response authoritative while recording GPU dispatch")
val config = web_framework_gpu_route_config("infer", "create", WebGpuRouteKind.Inference, 16, 256)
val ctx = wf_context("/infer", {})
val response = build_json("{\"ok\":true}")
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_inference_batch"])
val execution = web_framework_gpu_route_execute(
    ctx,
    config,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    wf_budget(),
    response
)
expect(web_framework_gpu_route_used_gpu(execution)).to_be(true)
expect(execution.offload.submission.dispatch_target).to_equal("gpu_web_inference_batch")
expect(execution.response.status).to_equal(200)
expect(execution.response.body).to_equal("{\"ok\":true}")
expect(execution.offload.cpu_authoritative).to_be(true)
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(web_gpu_route_profile_allows_gpu(execution.offload)).to_be(true)
```

</details>

#### should fall back when framework route target is missing

- Avoid fake GPU evidence for unregistered framework route targets
- gpu wdb queue initial
- gpu wdb library empty
- wf budget
- build json
   - Expected: execution.offload.submission.dispatch_target equals `cpu_fallback`
   - Expected: execution.offload.submission.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid fake GPU evidence for unregistered framework route targets")
val config = web_framework_gpu_route_config("embed", "create", WebGpuRouteKind.Embedding, 16, 256)
val ctx = wf_context("/embed", {})
val execution = web_framework_gpu_route_execute(
    ctx,
    config,
    gpu_wdb_queue_initial(4),
    gpu_wdb_library_empty(),
    true,
    true,
    wf_budget(),
    build_json("{\"embedding\":[]}")
)
expect(web_framework_gpu_route_used_gpu(execution)).to_be(false)
expect(execution.offload.submission.dispatch_target).to_equal("cpu_fallback")
expect(execution.offload.submission.reason).to_equal("gpu-unavailable")
```

</details>

#### should defer scheduled framework route batches

- Let controller routes opt into scheduler-backed batch accumulation
- gpu wdb queue initial
- wf budget
- build json
   - Expected: execution.offload.schedule_action equals `GpuWdbScheduleAction.DeferForBatch`
   - Expected: execution.offload.submission.dispatch_target equals `gpu_batch_accumulator`
   - Expected: execution.response.status equals `200`
   - Expected: execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Let controller routes opt into scheduler-backed batch accumulation")
val config = web_framework_gpu_route_config("embed", "create", WebGpuRouteKind.Embedding, 1, 128)
val ctx = wf_context("/embed", {})
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_embedding_batch"])
val execution = web_framework_gpu_route_execute_scheduled(
    ctx,
    config,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    wf_budget(),
    GpuWdbScheduleClass.Batch,
    true,
    build_json("{\"embedding\":[]}")
)
expect(web_framework_gpu_route_used_gpu(execution)).to_be(false)
expect(execution.offload.schedule_action).to_equal(GpuWdbScheduleAction.DeferForBatch)
expect(execution.offload.submission.dispatch_target).to_equal("gpu_batch_accumulator")
expect(execution.response.status).to_equal(200)
expect(execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
```

</details>

#### should accumulate deferred framework route work

- Mutate the shared batch accumulator without replacing the controller response
- gpu wdb queue initial
- wf budget
- gpu wdb batch accumulator
- build json
   - Expected: execution.accumulated.execution.schedule_action equals `GpuWdbScheduleAction.DeferForBatch`
   - Expected: execution.accumulated.execution.submission.dispatch_target equals `gpu_batch_accumulator`
   - Expected: execution.accumulated.accumulator_result.accumulator.item_count equals `1`
   - Expected: execution.response.body equals `{"embedding":[]}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mutate the shared batch accumulator without replacing the controller response")
val config = web_framework_gpu_route_config("embed", "create", WebGpuRouteKind.Embedding, 1, 128)
val ctx = wf_context("/embed", {})
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_embedding_batch"])
val execution = web_framework_gpu_route_execute_accumulating(
    ctx,
    config,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    wf_budget(),
    GpuWdbScheduleClass.Batch,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding),
    build_json("{\"embedding\":[]}")
)
expect(web_framework_gpu_route_used_gpu(WebFrameworkGpuRouteExecution(
    controller_name: execution.controller_name,
    action_name: execution.action_name,
    request_path: execution.request_path,
    offload: execution.accumulated.execution,
    response: execution.response
))).to_be(false)
expect(execution.accumulated.execution.schedule_action).to_equal(GpuWdbScheduleAction.DeferForBatch)
expect(execution.accumulated.execution.submission.dispatch_target).to_equal("gpu_batch_accumulator")
expect(execution.accumulated.accumulator_result.accepted).to_be(true)
expect(execution.accumulated.accumulator_result.accumulator.item_count).to_equal(1)
expect(execution.response.body).to_equal("{\"embedding\":[]}")
```

</details>

#### should keep immediate framework GPU dispatch out of the accumulator

- Avoid double-queueing route work that is already large enough for GPU dispatch
- gpu wdb queue initial
- wf budget
- gpu wdb batch accumulator
- build json
   - Expected: execution.accumulated.execution.schedule_action equals `GpuWdbScheduleAction.DispatchGpu`
   - Expected: execution.accumulated.execution.submission.dispatch_target equals `gpu_web_inference_batch`
   - Expected: execution.accumulated.accumulator_result.reason equals `route-not-deferred`
   - Expected: execution.accumulated.accumulator_result.accumulator.item_count equals `0`
   - Expected: execution.response.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid double-queueing route work that is already large enough for GPU dispatch")
val config = web_framework_gpu_route_config("infer", "create", WebGpuRouteKind.Inference, 8, 512)
val ctx = wf_context("/infer", {})
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_inference_batch"])
val execution = web_framework_gpu_route_execute_accumulating(
    ctx,
    config,
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    wf_budget(),
    GpuWdbScheduleClass.Batch,
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebInference),
    build_json("{\"ok\":true}")
)
expect(execution.accumulated.execution.schedule_action).to_equal(GpuWdbScheduleAction.DispatchGpu)
expect(execution.accumulated.execution.submission.dispatch_target).to_equal("gpu_web_inference_batch")
expect(execution.accumulated.accumulator_result.accepted).to_be(false)
expect(execution.accumulated.accumulator_result.reason).to_equal("route-not-deferred")
expect(execution.accumulated.accumulator_result.accumulator.item_count).to_equal(0)
expect(execution.response.status).to_equal(200)
```

</details>

#### should adopt matched controller actions through registered GPU route configs

- Dispatch a controller/action pair through the configured GPU adoption table
- web framework gpu route config
- web framework gpu route config
- gpu wdb queue initial
- wf budget
- build json
   - Expected: adoption.reason equals `matched-gpu-route-config`
   - Expected: adoption.execution.offload.submission.dispatch_target equals `gpu_web_rank_batch`
   - Expected: adoption.execution.response.body equals `{"ranked":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a controller/action pair through the configured GPU adoption table")
val configs = [
    web_framework_gpu_route_config("embed", "create", WebGpuRouteKind.Embedding, 16, 256),
    web_framework_gpu_route_config("rank", "create", WebGpuRouteKind.Rank, 8, 512)
]
val ctx = wf_context("/rank", {})
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_rank_batch"])
val adoption = web_framework_gpu_route_execute_for_action(
    ctx,
    configs,
    "rank",
    "create",
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    wf_budget(),
    build_json("{\"ranked\":true}")
)
expect(adoption.matched).to_be(true)
expect(adoption.reason).to_equal("matched-gpu-route-config")
expect(web_framework_gpu_route_used_gpu(adoption.execution)).to_be(true)
expect(adoption.execution.offload.submission.dispatch_target).to_equal("gpu_web_rank_batch")
expect(adoption.execution.response.body).to_equal("{\"ranked\":true}")
expect(adoption.execution.offload.cpu_authoritative).to_be(true)
```

</details>

#### should keep unconfigured controller actions on CPU without fake GPU evidence

- Dispatch an unconfigured controller/action pair through a CPU-owned fallback
- web framework gpu route config
- gpu wdb queue initial
- wf budget
- build json
   - Expected: adoption.reason equals `no-gpu-route-config`
   - Expected: adoption.execution.offload.route_kind equals `WebGpuRouteKind.HttpControlPlane`
   - Expected: adoption.execution.offload.submission.dispatch_target equals `cpu_fallback`
   - Expected: adoption.execution.offload.submission.reason equals `control-plane-stays-on-cpu`
   - Expected: adoption.execution.offload.profile.data_path equals `GpuWdbCoarseDataPath.CpuOnly`
   - Expected: adoption.execution.response.body equals `{"status":"ok"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch an unconfigured controller/action pair through a CPU-owned fallback")
val configs = [
    web_framework_gpu_route_config("embed", "create", WebGpuRouteKind.Embedding, 16, 256)
]
val ctx = wf_context("/admin/health", {})
val registry = gpu_wdb_library_with_targets("cuda", 1, ["gpu_web_embedding_batch"])
val adoption = web_framework_gpu_route_execute_for_action(
    ctx,
    configs,
    "admin",
    "health",
    gpu_wdb_queue_initial(4),
    registry,
    true,
    true,
    wf_budget(),
    build_json("{\"status\":\"ok\"}")
)
expect(adoption.matched).to_be(false)
expect(adoption.reason).to_equal("no-gpu-route-config")
expect(web_framework_gpu_route_used_gpu(adoption.execution)).to_be(false)
expect(adoption.execution.offload.route_kind).to_equal(WebGpuRouteKind.HttpControlPlane)
expect(adoption.execution.offload.submission.dispatch_target).to_equal("cpu_fallback")
expect(adoption.execution.offload.submission.reason).to_equal("control-plane-stays-on-cpu")
expect(adoption.execution.offload.profile.data_path).to_equal(GpuWdbCoarseDataPath.CpuOnly)
expect(web_gpu_route_profile_allows_gpu(adoption.execution.offload)).to_be(false)
expect(adoption.execution.response.body).to_equal("{\"status\":\"ok\"}")
```

</details>

#### should replace framework route responses after native candidates match

- Expose web profile response validation to controller-facing routes
- web gpu profile inference
- gpu wdb device backend
- build json
- build json
   - Expected: execution.validated.validation_reason equals `production-gpu-web-response-match`
   - Expected: execution.response.body equals `{"ok":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose web profile response validation to controller-facing routes")
val config = web_framework_gpu_route_config("infer", "create", WebGpuRouteKind.Inference, 16, 512)
val ctx = wf_context("/infer", {})
val execution = web_framework_gpu_route_execute_device_validated(
    ctx,
    config,
    web_gpu_profile_inference("cuda", 5, 4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_web_inference_batch"], true, "cuda-device-0"),
    5,
    build_json("{\"ok\":true}"),
    100,
    180,
    43,
    "cuda-event",
    build_json("{\"ok\":true}")
)
expect(execution.validated.gpu_candidate_validated).to_be(true)
expect(execution.validated.validation_reason).to_equal("production-gpu-web-response-match")
expect(execution.validated.execution.cpu_authoritative).to_be(false)
expect(execution.validated.execution.gpu_dispatched).to_be(true)
expect(execution.response.body).to_equal("{\"ok\":true}")
expect(execution.validated.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep framework route responses CPU authoritative when candidates mismatch

- Reject framework response replacement when native candidate body differs
- web gpu profile inference
- gpu wdb device backend
- build json
- build json
   - Expected: execution.validated.validation_reason equals `production-gpu-web-response-mismatch`
   - Expected: execution.validated.execution.validation_reason equals `production-gpu-web-response-mismatch`
   - Expected: execution.response.body equals `{"ok":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject framework response replacement when native candidate body differs")
val config = web_framework_gpu_route_config("infer", "create", WebGpuRouteKind.Inference, 16, 512)
val ctx = wf_context("/infer", {})
val execution = web_framework_gpu_route_execute_device_validated(
    ctx,
    config,
    web_gpu_profile_inference("cuda", 5, 4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_web_inference_batch"], true, "cuda-device-0"),
    5,
    build_json("{\"ok\":false}"),
    100,
    180,
    43,
    "cuda-event",
    build_json("{\"ok\":true}")
)
expect(execution.validated.gpu_candidate_validated).to_be(false)
expect(execution.validated.validation_reason).to_equal("production-gpu-web-response-mismatch")
expect(execution.validated.execution.gpu_candidate_validated).to_be(false)
expect(execution.validated.execution.validation_reason).to_equal("production-gpu-web-response-mismatch")
expect(execution.validated.execution.cpu_authoritative).to_be(true)
expect(execution.validated.execution.gpu_dispatched).to_be(false)
expect(execution.response.body).to_equal("{\"ok\":true}")
expect(execution.validated.device_result.production_device_claim).to_be(true)
```

</details>

#### should keep perf-only framework device runs from replacing CPU responses

- Require production native timing before controller responses can be replaced
- web gpu profile inference
- gpu wdb device backend
- build json
- build json
   - Expected: execution.validated.validation_reason equals `production-device-not-measured`
   - Expected: execution.response.body equals `{"ok":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require production native timing before controller responses can be replaced")
val config = web_framework_gpu_route_config("infer", "create", WebGpuRouteKind.Inference, 16, 512)
val ctx = wf_context("/infer", {})
val execution = web_framework_gpu_route_execute_device_validated(
    ctx,
    config,
    web_gpu_profile_inference("cuda", 5, 4),
    gpu_wdb_device_backend("mock", 5, ["gpu_web_inference_batch"], false, "mock-device"),
    5,
    build_json("{\"ok\":true}"),
    100,
    180,
    43,
    "mock-clock",
    build_json("{\"ok\":true}")
)
expect(execution.validated.gpu_candidate_validated).to_be(false)
expect(execution.validated.validation_reason).to_equal("production-device-not-measured")
expect(execution.validated.execution.cpu_authoritative).to_be(true)
expect(execution.validated.execution.gpu_dispatched).to_be(false)
expect(execution.response.body).to_equal("{\"ok\":true}")
expect(execution.validated.device_result.production_device_claim).to_be(false)
```

</details>

#### should replace framework transform responses after native candidates match

- Expose non-inference response validation to controller-facing transform routes
- web gpu profile transform
- gpu wdb device backend
- build json
- build json
   - Expected: execution.validated.validation_reason equals `production-gpu-web-response-match`
   - Expected: execution.validated.execution.validation_reason equals `production-gpu-web-response-match`
   - Expected: execution.validated.device_result.submission.dispatch_target equals `gpu_web_transform_batch`
   - Expected: execution.response.body equals `{"transformed":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose non-inference response validation to controller-facing transform routes")
val config = web_framework_gpu_route_config("image", "transform", WebGpuRouteKind.Transform, 8, 2048)
val ctx = wf_context("/image/transform", {})
val execution = web_framework_gpu_route_execute_device_validated(
    ctx,
    config,
    web_gpu_profile_transform("cuda", 5, 4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_web_transform_batch"], true, "cuda-device-0"),
    5,
    build_json("{\"transformed\":true}"),
    100,
    180,
    43,
    "cuda-event",
    build_json("{\"transformed\":true}")
)
expect(execution.validated.gpu_candidate_validated).to_be(true)
expect(execution.validated.validation_reason).to_equal("production-gpu-web-response-match")
expect(execution.validated.execution.gpu_candidate_validated).to_be(true)
expect(execution.validated.execution.validation_reason).to_equal("production-gpu-web-response-match")
expect(execution.validated.execution.cpu_authoritative).to_be(false)
expect(execution.validated.execution.gpu_dispatched).to_be(true)
expect(execution.validated.device_result.submission.dispatch_target).to_equal("gpu_web_transform_batch")
expect(execution.response.body).to_equal("{\"transformed\":true}")
```

</details>

#### should keep framework transform responses CPU authoritative when candidates mismatch

- Reject non-inference framework response replacement when native transform output differs
- web gpu profile transform
- gpu wdb device backend
- build json
- build json
   - Expected: execution.validated.validation_reason equals `production-gpu-web-response-mismatch`
   - Expected: execution.validated.device_result.submission.dispatch_target equals `gpu_web_transform_batch`
   - Expected: execution.response.body equals `{"transformed":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject non-inference framework response replacement when native transform output differs")
val config = web_framework_gpu_route_config("image", "transform", WebGpuRouteKind.Transform, 8, 2048)
val ctx = wf_context("/image/transform", {})
val execution = web_framework_gpu_route_execute_device_validated(
    ctx,
    config,
    web_gpu_profile_transform("cuda", 5, 4),
    gpu_wdb_device_backend("cuda", 5, ["gpu_web_transform_batch"], true, "cuda-device-0"),
    5,
    build_json("{\"transformed\":false}"),
    100,
    180,
    43,
    "cuda-event",
    build_json("{\"transformed\":true}")
)
expect(execution.validated.gpu_candidate_validated).to_be(false)
expect(execution.validated.validation_reason).to_equal("production-gpu-web-response-mismatch")
expect(execution.validated.execution.cpu_authoritative).to_be(true)
expect(execution.validated.execution.gpu_dispatched).to_be(false)
expect(execution.validated.device_result.submission.dispatch_target).to_equal("gpu_web_transform_batch")
expect(execution.response.body).to_equal("{\"transformed\":true}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
