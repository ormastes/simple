# GPU Web/DB Offload Scheduler

> These scenarios verify the shared admission scheduler used before web and database callers mutate queue state. The scheduler is reliability-first: CPU fallback remains mandatory, proxy/control-plane work remains CPU-owned, and GPU dispatch requires a registered executable target.

<!-- sdn-diagram:id=gpu_web_db_offload_scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_web_db_offload_scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_web_db_offload_scheduler_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_web_db_offload_scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Web/DB Offload Scheduler

These scenarios verify the shared admission scheduler used before web and database callers mutate queue state. The scheduler is reliability-first: CPU fallback remains mandatory, proxy/control-plane work remains CPU-owned, and GPU dispatch requires a registered executable target.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | doc/01_research/domain/gpu_web_db_offload.md |
| Source | `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the shared admission scheduler used before web and
database callers mutate queue state. The scheduler is reliability-first: CPU
fallback remains mandatory, proxy/control-plane work remains CPU-owned, and GPU
dispatch requires a registered executable target.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Coarse web and database batches may use GPU execution when a registered
  target, queue budget, and runtime evidence all admit the work.
- Small background or batch work may be deferred to an accumulator so later
  work can flush as a larger GPU-worthy batch.
- Interactive tiny work keeps CPU latency fallback instead of waiting for an
  accumulator.
- Reverse proxy forwarding and HTTP control-plane work stay CPU-owned.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** doc/01_research/domain/gpu_web_db_offload.md

## Examples

Use `gpu_wdb_schedule_registered` before mutating a GPU queue. When it returns
`DeferForBatch`, add the request to a `GpuWdbBatchAccumulator`. Flush the
accumulator through `gpu_wdb_batch_accumulator_flush` only after
`should_flush == true`, then schedule the flushed batch as non-deferred work.

## Scenarios

### GPU web/db reusable offload scheduler

#### should dispatch registered vector work to the GPU

- Admit a large vector batch when CUDA target is registered
- ready snapshot
   - Expected: schedule.action equals `GpuWdbScheduleAction.DispatchGpu`
   - Expected: schedule.target equals `gpu_db_vector_search_batch`
   - Expected: schedule.queue_depth_after equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Admit a large vector batch when CUDA target is registered")
val budget = gpu_wdb_default_budget()
val registry = gpu_wdb_library_with_targets(
    "cuda",
    1,
    ["gpu_db_vector_search_batch"]
)
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 8,
    8,
    GpuWdbScheduleClass.Batch,
    true,
    ready_snapshot(2)
)
val schedule = gpu_wdb_schedule_registered(req, registry, budget)
expect(schedule.action).to_equal(GpuWdbScheduleAction.DispatchGpu)
expect(schedule.target).to_equal("gpu_db_vector_search_batch")
expect(schedule.queue_depth_after).to_equal(3)
```

</details>

#### should fall back to CPU when the GPU target is not registered

- Do not claim GPU evidence from a missing executable library
- ready snapshot
   - Expected: schedule.action equals `GpuWdbScheduleAction.RunCpuFallback`
   - Expected: schedule.target equals `cpu_fallback`
   - Expected: schedule.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Do not claim GPU evidence from a missing executable library")
val budget = gpu_wdb_default_budget()
val registry = gpu_wdb_library_with_targets("cuda", 1, [])
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 8,
    8,
    GpuWdbScheduleClass.Batch,
    true,
    ready_snapshot(0)
)
val schedule = gpu_wdb_schedule_registered(req, registry, budget)
expect(schedule.action).to_equal(GpuWdbScheduleAction.RunCpuFallback)
expect(schedule.target).to_equal("cpu_fallback")
expect(schedule.reason).to_equal("gpu-unavailable")
```

</details>

#### should defer small batchable work for a later GPU batch

- Accumulate small background work instead of forcing tiny kernels
- ready snapshot
   - Expected: schedule.action equals `GpuWdbScheduleAction.DeferForBatch`
   - Expected: schedule.target equals `gpu_batch_accumulator`
   - Expected: schedule.queue_depth_after equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accumulate small background work instead of forcing tiny kernels")
val budget = gpu_wdb_default_budget()
val registry = gpu_wdb_library_with_targets(
    "cuda",
    1,
    ["gpu_web_embedding_batch"]
)
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.WebEmbedding,
    budget.min_gpu_batch_bytes / 2,
    2,
    GpuWdbScheduleClass.Background,
    true,
    ready_snapshot(0)
)
val schedule = gpu_wdb_schedule_registered(req, registry, budget)
expect(schedule.action).to_equal(GpuWdbScheduleAction.DeferForBatch)
expect(schedule.target).to_equal("gpu_batch_accumulator")
expect(schedule.queue_depth_after).to_equal(0)
```

</details>

#### should accumulate deferred work until it reaches GPU batch size

- Combine small background work into a coarse GPU-worthy batch
   - Expected: partial.reason equals `batch-accumulating`
   - Expected: ready.accumulator.item_count equals `5`
   - Expected: ready.accumulator.pending_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Combine small background work into a coarse GPU-worthy batch")
val budget = gpu_wdb_default_budget()
val snapshot = ready_snapshot(0)
val first = gpu_wdb_schedule_request(
    GpuWdbWorkKind.WebEmbedding,
    budget.min_gpu_batch_bytes / 2,
    2,
    GpuWdbScheduleClass.Background,
    true,
    snapshot
)
val second = gpu_wdb_schedule_request(
    GpuWdbWorkKind.WebEmbedding,
    budget.min_gpu_batch_bytes / 2,
    3,
    GpuWdbScheduleClass.Background,
    true,
    snapshot
)
val start = gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding)
val partial = gpu_wdb_batch_accumulator_add(start, first, budget)
val ready = gpu_wdb_batch_accumulator_add(partial.accumulator, second, budget)
expect(partial.accepted).to_be(true)
expect(partial.should_flush).to_be(false)
expect(partial.reason).to_equal("batch-accumulating")
expect(ready.accepted).to_be(true)
expect(ready.should_flush).to_be(true)
expect(ready.accumulator.item_count).to_equal(5)
expect(ready.accumulator.pending_count).to_equal(2)
```

</details>

#### should flush accumulated work as a non-deferred batch request

- Convert accumulated small work into a normal batch scheduler request
- gpu wdb batch accumulator
   - Expected: flushed.kind equals `GpuWdbWorkKind.DbVectorSearch`
   - Expected: flushed.batch_bytes equals `budget.min_gpu_batch_bytes`
   - Expected: flushed.item_count equals `4`
   - Expected: reset.total_batch_bytes equals `0`
   - Expected: reset.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert accumulated small work into a normal batch scheduler request")
val budget = gpu_wdb_default_budget()
val snapshot = ready_snapshot(1)
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes,
    4,
    GpuWdbScheduleClass.Background,
    true,
    snapshot
)
val added = gpu_wdb_batch_accumulator_add(
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbVectorSearch),
    req,
    budget
)
val flushed = gpu_wdb_batch_accumulator_flush(added.accumulator, snapshot)
val reset = gpu_wdb_batch_accumulator_reset(added.accumulator)
expect(added.should_flush).to_be(true)
expect(flushed.kind).to_equal(GpuWdbWorkKind.DbVectorSearch)
expect(flushed.batch_bytes).to_equal(budget.min_gpu_batch_bytes)
expect(flushed.item_count).to_equal(4)
expect(flushed.allow_defer).to_be(false)
expect(reset.total_batch_bytes).to_equal(0)
expect(reset.item_count).to_equal(0)
```

</details>

#### should flush a ready accumulator through a registered GPU target

- Submit accumulated work through the shared queue and clear handled state
- gpu wdb batch accumulator
- gpu wdb queue initial
   - Expected: flushed.submission.dispatch_target equals `gpu_web_embedding_batch`
   - Expected: flushed.submission.stream_id equals `0`
   - Expected: flushed.accumulator_after.item_count equals `0`
   - Expected: flushed.accumulator_after.pending_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit accumulated work through the shared queue and clear handled state")
val budget = gpu_wdb_default_budget()
val snapshot = ready_snapshot(0)
val registry = gpu_wdb_library_with_targets(
    "cuda",
    1,
    ["gpu_web_embedding_batch"]
)
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.WebEmbedding,
    budget.min_gpu_batch_bytes,
    4,
    GpuWdbScheduleClass.Batch,
    true,
    snapshot
)
val added = gpu_wdb_batch_accumulator_add(
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding),
    req,
    budget
)
val flushed = gpu_wdb_batch_accumulator_flush_registered(
    added.accumulator,
    gpu_wdb_queue_initial(2),
    registry,
    snapshot,
    budget
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(true)
expect(flushed.submission.dispatch_target).to_equal("gpu_web_embedding_batch")
expect(flushed.submission.stream_id).to_equal(0)
expect(flushed.accumulator_after.item_count).to_equal(0)
expect(flushed.accumulator_after.pending_count).to_equal(0)
```

</details>

#### should clear flushed accumulator state after CPU fallback handles work

- Avoid retrying already handled accumulated work when GPU target is missing
- gpu wdb batch accumulator
- gpu wdb queue initial
- gpu wdb library empty
   - Expected: flushed.submission.dispatch_target equals `cpu_fallback`
   - Expected: flushed.reason equals `gpu-unavailable`
   - Expected: flushed.accumulator_after.item_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid retrying already handled accumulated work when GPU target is missing")
val budget = gpu_wdb_default_budget()
val snapshot = ready_snapshot(0)
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.DbDocumentFilter,
    budget.min_gpu_batch_bytes,
    3,
    GpuWdbScheduleClass.Batch,
    true,
    snapshot
)
val added = gpu_wdb_batch_accumulator_add(
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbDocumentFilter),
    req,
    budget
)
val flushed = gpu_wdb_batch_accumulator_flush_registered(
    added.accumulator,
    gpu_wdb_queue_initial(1),
    gpu_wdb_library_empty(),
    snapshot,
    budget
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(false)
expect(flushed.submission.dispatch_target).to_equal("cpu_fallback")
expect(flushed.reason).to_equal("gpu-unavailable")
expect(flushed.accumulator_after.item_count).to_equal(0)
```

</details>

#### should retain accumulator state when flushed work is rejected

- Keep rejected work visible so callers can report or retry it
- ready snapshot
- gpu wdb batch accumulator
- gpu wdb queue initial
- gpu wdb library with targets
   - Expected: flushed.submission.execution.decision.path equals `GpuWdbDecisionPath.Reject`
   - Expected: flushed.reason equals `cpu-fallback-required`
   - Expected: flushed.accumulator_after.item_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep rejected work visible so callers can report or retry it")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 0,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: false
)
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes,
    4,
    GpuWdbScheduleClass.Batch,
    true,
    ready_snapshot(0)
)
val added = gpu_wdb_batch_accumulator_add(
    gpu_wdb_batch_accumulator(GpuWdbWorkKind.DbVectorSearch),
    req,
    budget
)
val flushed = gpu_wdb_batch_accumulator_flush_registered(
    added.accumulator,
    gpu_wdb_queue_initial(1),
    gpu_wdb_library_with_targets("cuda", 1, ["gpu_db_vector_search_batch"]),
    snapshot,
    budget
)
expect(flushed.attempted).to_be(true)
expect(flushed.submission.accepted).to_be(false)
expect(flushed.submission.execution.decision.path).to_equal(GpuWdbDecisionPath.Reject)
expect(flushed.reason).to_equal("cpu-fallback-required")
expect(flushed.accumulator_after.item_count).to_equal(4)
```

</details>

#### should reject mixed or invalid accumulator additions

- Keep accumulator batches homogeneous and valid
   - Expected: mixed.reason equals `batch-accumulator-kind-mismatch`
   - Expected: invalid.reason equals `batch-item-count-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep accumulator batches homogeneous and valid")
val budget = gpu_wdb_default_budget()
val snapshot = ready_snapshot(0)
val accumulator = gpu_wdb_batch_accumulator(GpuWdbWorkKind.WebEmbedding)
val mixed = gpu_wdb_batch_accumulator_add(
    accumulator,
    gpu_wdb_schedule_request(
        GpuWdbWorkKind.DbVectorSearch,
        budget.min_gpu_batch_bytes / 2,
        1,
        GpuWdbScheduleClass.Background,
        true,
        snapshot
    ),
    budget
)
val invalid = gpu_wdb_batch_accumulator_add(
    accumulator,
    gpu_wdb_schedule_request(
        GpuWdbWorkKind.WebEmbedding,
        0,
        0,
        GpuWdbScheduleClass.Background,
        true,
        snapshot
    ),
    budget
)
expect(mixed.accepted).to_be(false)
expect(mixed.reason).to_equal("batch-accumulator-kind-mismatch")
expect(invalid.accepted).to_be(false)
expect(invalid.reason).to_equal("batch-item-count-invalid")
```

</details>

#### should run urgent small work on CPU fallback

- Keep interactive latency reliable when work is too small for GPU
- ready snapshot
   - Expected: schedule.action equals `GpuWdbScheduleAction.RunCpuFallback`
   - Expected: schedule.reason equals `batch-too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep interactive latency reliable when work is too small for GPU")
val budget = gpu_wdb_default_budget()
val registry = gpu_wdb_library_with_targets(
    "cuda",
    1,
    ["gpu_web_inference_batch"]
)
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.WebInference,
    budget.min_gpu_batch_bytes / 2,
    1,
    GpuWdbScheduleClass.Interactive,
    true,
    ready_snapshot(0)
)
val schedule = gpu_wdb_schedule_registered(req, registry, budget)
expect(schedule.action).to_equal(GpuWdbScheduleAction.RunCpuFallback)
expect(schedule.reason).to_equal("batch-too-small")
```

</details>

#### should reject work with no CPU fallback

- Require an authoritative CPU path for production reliability
   - Expected: schedule.action equals `GpuWdbScheduleAction.RejectWork`
   - Expected: schedule.reason equals `cpu-fallback-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require an authoritative CPU path for production reliability")
val budget = gpu_wdb_default_budget()
val registry = gpu_wdb_library_with_targets(
    "cuda",
    1,
    ["gpu_db_columnar_scan_batch"]
)
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 0,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: false
)
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.DbScanFilterProject,
    budget.min_gpu_batch_bytes * 2,
    2,
    GpuWdbScheduleClass.Batch,
    true,
    snapshot
)
val schedule = gpu_wdb_schedule_registered(req, registry, budget)
expect(schedule.action).to_equal(GpuWdbScheduleAction.RejectWork)
expect(schedule.reason).to_equal("cpu-fallback-required")
```

</details>

#### should keep proxy forwarding on CPU

- Never admit reverse proxy forwarding into GPU scheduling
- ready snapshot
   - Expected: schedule.action equals `GpuWdbScheduleAction.RunCpuFallback`
   - Expected: schedule.reason equals `control-plane-stays-on-cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Never admit reverse proxy forwarding into GPU scheduling")
val budget = gpu_wdb_default_budget()
val registry = gpu_wdb_library_with_targets("cuda", 1, ["cpu_proxy_stream"])
val req = gpu_wdb_schedule_request(
    GpuWdbWorkKind.ProxyForwarding,
    budget.min_gpu_batch_bytes * 2,
    2,
    GpuWdbScheduleClass.Batch,
    true,
    ready_snapshot(0)
)
val schedule = gpu_wdb_schedule_registered(req, registry, budget)
expect(schedule.action).to_equal(GpuWdbScheduleAction.RunCpuFallback)
expect(schedule.reason).to_equal("control-plane-stays-on-cpu")
```

</details>

#### should describe reusable coarse batch profiles for web and database paths

- Expose one shared profile contract for web, RAM DB, SSD DB, NoSQL, and vector batches
   - Expected: web.data_path equals `GpuWdbCoarseDataPath.PinnedHostBatch`
   - Expected: ram.data_path equals `GpuWdbCoarseDataPath.GpuResidentBatch`
   - Expected: ram.stream_count equals `4`
   - Expected: ssd.data_path equals `GpuWdbCoarseDataPath.SsdStagedBatch`
   - Expected: nosql.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`
   - Expected: vector.data_path equals `GpuWdbCoarseDataPath.GpuIndexBatch`
   - Expected: vector.stream_count equals `4`
   - Expected: proxy.data_path equals `GpuWdbCoarseDataPath.CpuOnly`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose one shared profile contract for web, RAM DB, SSD DB, NoSQL, and vector batches")
val web = gpu_wdb_web_payload_profile(GpuWdbWorkKind.WebEmbedding)
val ram = gpu_wdb_ram_db_profile()
val ssd = gpu_wdb_ssd_db_profile()
val nosql = gpu_wdb_nosql_db_profile()
val vector = gpu_wdb_vector_db_profile()
val proxy = gpu_wdb_web_payload_profile(GpuWdbWorkKind.ProxyForwarding)

expect(web.data_path).to_equal(GpuWdbCoarseDataPath.PinnedHostBatch)
expect(web.pinned_host_required).to_be(true)
expect(web.cpu_control_path).to_be(true)
expect(web.cpu_durability_path).to_be(false)

expect(ram.data_path).to_equal(GpuWdbCoarseDataPath.GpuResidentBatch)
expect(ram.gpu_resident_allowed).to_be(true)
expect(ram.stream_count).to_equal(4)

expect(ssd.data_path).to_equal(GpuWdbCoarseDataPath.SsdStagedBatch)
expect(ssd.cpu_durability_path).to_be(true)
expect(ssd.gpu_resident_allowed).to_be(false)

expect(nosql.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(nosql.cpu_durability_path).to_be(true)
expect(vector.data_path).to_equal(GpuWdbCoarseDataPath.GpuIndexBatch)
expect(vector.stream_count).to_equal(4)

expect(proxy.data_path).to_equal(GpuWdbCoarseDataPath.CpuOnly)
expect(proxy.pinned_host_required).to_be(false)
```

</details>

#### should admit GPU evidence only through non-control coarse profiles

- Tie GPU dispatch claims to the reusable coarse profile boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Tie GPU dispatch claims to the reusable coarse profile boundary")
val gpu_decision = gpu_wdb_gpu("gpu-evidence")
val cpu_decision = gpu_wdb_cpu("cpu-fallback")
val web = gpu_wdb_web_payload_profile(GpuWdbWorkKind.WebInference)
val proxy = gpu_wdb_web_payload_profile(GpuWdbWorkKind.ProxyForwarding)
val ssd = gpu_wdb_ssd_db_profile()

expect(gpu_wdb_profile_allows_gpu(web, gpu_decision)).to_be(true)
expect(gpu_wdb_profile_allows_gpu(ssd, gpu_decision)).to_be(true)
expect(gpu_wdb_profile_allows_gpu(proxy, gpu_decision)).to_be(false)
expect(gpu_wdb_profile_allows_gpu(web, cpu_decision)).to_be(false)
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
- **Research:** [doc/01_research/domain/gpu_web_db_offload.md](doc/01_research/domain/gpu_web_db_offload.md)


</details>
