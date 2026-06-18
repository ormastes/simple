# GPU Web/DB Offload Contract

> These scenarios define the reliability-first admission contract for coarse web/database GPU work. HTTP control-plane and proxy forwarding remain CPU-owned, while eligible batch work may reserve reusable GPU queue slots with pinned host buffer accounting, reusable execution evidence, and CPU fallback.

<!-- sdn-diagram:id=gpu_web_db_offload_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_web_db_offload_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_web_db_offload_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_web_db_offload_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Web/DB Offload Contract

These scenarios define the reliability-first admission contract for coarse web/database GPU work. HTTP control-plane and proxy forwarding remain CPU-owned, while eligible batch work may reserve reusable GPU queue slots with pinned host buffer accounting, reusable execution evidence, and CPU fallback.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | doc/01_research/local/gpu_web_db_offload.md |
| Source | `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios define the reliability-first admission contract for coarse
web/database GPU work. HTTP control-plane and proxy forwarding remain CPU-owned,
while eligible batch work may reserve reusable GPU queue slots with pinned host
buffer accounting, reusable execution evidence, and CPU fallback.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- CPU fallback remains mandatory for GPU-eligible web and database work.
- Proxy forwarding and HTTP control-plane work stay CPU-owned.
- Queue submissions expose reusable evidence for GPU hits and CPU fallbacks.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** doc/01_research/local/gpu_web_db_offload.md

## Examples

Use `gpu_wdb_decide` for admission, `gpu_wdb_submit_batch` for bounded queue
accounting, and `gpu_wdb_submission_evidence` when benchmark or caller code
needs a stable metrics record.

## Scenarios

### GPU web/db offload contract

#### should keep proxy forwarding on the CPU control plane

- Classify proxy forwarding as non-GPU control plane work
- request
- gpu wdb default budget
   - Expected: decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: decision.reason equals `control-plane-stays-on-cpu`
   - Expected: decision.cpu_fallback_count equals `1`
   - Expected: decision.gpu_hit_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify proxy forwarding as non-GPU control plane work")
val decision = gpu_wdb_decide(
    request(GpuWdbWorkKind.ProxyForwarding, 65536, 0, true, true, true),
    gpu_wdb_default_budget()
)
expect(decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(decision.reason).to_equal("control-plane-stays-on-cpu")
expect(decision.cpu_fallback_count).to_equal(1)
expect(decision.gpu_hit_count).to_equal(0)
```

</details>

#### should reject GPU work when CPU fallback is missing

- Submit eligible GPU work without a CPU fallback
- request
- gpu wdb default budget
   - Expected: decision.path equals `GpuWdbDecisionPath.Reject`
   - Expected: decision.reason equals `cpu-fallback-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit eligible GPU work without a CPU fallback")
val decision = gpu_wdb_decide(
    request(GpuWdbWorkKind.DbVectorSearch, 65536, 0, true, true, false),
    gpu_wdb_default_budget()
)
expect(decision.path).to_equal(GpuWdbDecisionPath.Reject)
expect(decision.reason).to_equal("cpu-fallback-required")
```

</details>

#### should fall back for stale database generations

- Submit stale DB work that must not use GPU results
- request
- gpu wdb default budget
   - Expected: decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: decision.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit stale DB work that must not use GPU results")
val decision = gpu_wdb_decide(
    request(GpuWdbWorkKind.DbScanFilterProject, 65536, 0, true, false, true),
    gpu_wdb_default_budget()
)
expect(decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(decision.reason).to_equal("stale-generation")
```

</details>

#### should fall back when the GPU queue is full

- Submit eligible work at the queue limit
- request
   - Expected: decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: decision.reason equals `gpu-queue-full`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit eligible work at the queue limit")
val budget = gpu_wdb_default_budget()
val decision = gpu_wdb_decide(
    request(GpuWdbWorkKind.WebEmbedding, 65536, budget.max_queue_depth, true, true, true),
    budget
)
expect(decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(decision.reason).to_equal("gpu-queue-full")
```

</details>

#### should reject tiny batches for GPU performance claims

- Submit a tiny vector batch
- request
   - Expected: decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: decision.reason equals `batch-too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a tiny vector batch")
val budget = gpu_wdb_default_budget()
val decision = gpu_wdb_decide(
    request(GpuWdbWorkKind.DbVectorSearch, budget.min_gpu_batch_bytes - 1, 0, true, true, true),
    budget
)
expect(decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(decision.reason).to_equal("batch-too-small")
```

</details>

#### should reject invalid queue and batch inputs before GPU admission

- Submit impossible runtime accounting values
- request
- request
   - Expected: negative_queue.path equals `GpuWdbDecisionPath.Reject`
   - Expected: negative_queue.reason equals `queue-depth-invalid`
   - Expected: empty_batch.path equals `GpuWdbDecisionPath.Reject`
   - Expected: empty_batch.reason equals `batch-bytes-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit impossible runtime accounting values")
val budget = gpu_wdb_default_budget()
val negative_queue = gpu_wdb_decide(
    request(GpuWdbWorkKind.WebRank, budget.min_gpu_batch_bytes, -1, true, true, true),
    budget
)
val empty_batch = gpu_wdb_decide(
    request(GpuWdbWorkKind.WebRank, 0, 0, true, true, true),
    budget
)
expect(negative_queue.path).to_equal(GpuWdbDecisionPath.Reject)
expect(negative_queue.reason).to_equal("queue-depth-invalid")
expect(empty_batch.path).to_equal(GpuWdbDecisionPath.Reject)
expect(empty_batch.reason).to_equal("batch-bytes-invalid")
```

</details>

#### should report GPU evidence for eligible coarse batches

- Submit a coarse eligible rank batch
- request
   - Expected: decision.path equals `GpuWdbDecisionPath.GpuEvidence`
   - Expected: decision.reason equals `gpu-evidence`
   - Expected: decision.gpu_hit_count equals `1`
   - Expected: decision.cpu_fallback_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a coarse eligible rank batch")
val budget = gpu_wdb_default_budget()
val decision = gpu_wdb_decide(
    request(GpuWdbWorkKind.WebRank, budget.min_gpu_batch_bytes, 0, true, true, true),
    budget
)
expect(decision.path).to_equal(GpuWdbDecisionPath.GpuEvidence)
expect(decision.reason).to_equal("gpu-evidence")
expect(decision.gpu_hit_count).to_equal(1)
expect(decision.cpu_fallback_count).to_equal(0)
```

</details>

#### should build reusable GPU library execution plans

- Convert a runtime snapshot into a shared execution plan
   - Expected: plan.decision.path equals `GpuWdbDecisionPath.GpuEvidence`
   - Expected: plan.target equals `gpu_db_vector_search_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert a runtime snapshot into a shared execution plan")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 0,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: true
)
val req = gpu_wdb_request(GpuWdbWorkKind.DbVectorSearch, budget.min_gpu_batch_bytes, snapshot)
val plan = gpu_wdb_execution_plan(req, budget)
expect(plan.decision.path).to_equal(GpuWdbDecisionPath.GpuEvidence)
expect(plan.target).to_equal("gpu_db_vector_search_batch")
```

</details>

#### should reserve one queue slot for an eligible reusable batch plan

- Plan a coarse DB vector batch through the shared queue accounting API
   - Expected: plan.execution.decision.path equals `GpuWdbDecisionPath.GpuEvidence`
   - Expected: plan.execution.target equals `gpu_db_vector_search_batch`
   - Expected: plan.average_item_bytes equals `budget.min_gpu_batch_bytes`
   - Expected: plan.queue_depth_after equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a coarse DB vector batch through the shared queue accounting API")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 3,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: true
)
val window = gpu_wdb_batch_window(GpuWdbWorkKind.DbVectorSearch, budget.min_gpu_batch_bytes * 4, 4, snapshot)
val plan = gpu_wdb_batch_plan(window, budget)
expect(plan.execution.decision.path).to_equal(GpuWdbDecisionPath.GpuEvidence)
expect(plan.execution.target).to_equal("gpu_db_vector_search_batch")
expect(plan.average_item_bytes).to_equal(budget.min_gpu_batch_bytes)
expect(plan.queue_depth_after).to_equal(4)
```

</details>

#### should release the queue slot when a reusable batch falls back

- Plan a tiny web batch that must remain on CPU
   - Expected: plan.execution.decision.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: plan.execution.decision.reason equals `batch-too-small`
   - Expected: plan.execution.target equals `cpu_fallback`
   - Expected: plan.queue_depth_after equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a tiny web batch that must remain on CPU")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 3,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: true
)
val window = gpu_wdb_batch_window(GpuWdbWorkKind.WebEmbedding, budget.min_gpu_batch_bytes - 1, 2, snapshot)
val plan = gpu_wdb_batch_plan(window, budget)
expect(plan.execution.decision.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(plan.execution.decision.reason).to_equal("batch-too-small")
expect(plan.execution.target).to_equal("cpu_fallback")
expect(plan.queue_depth_after).to_equal(3)
```

</details>

#### should reject reusable batch plans with no items

- Plan a malformed empty batch
   - Expected: plan.execution.decision.path equals `GpuWdbDecisionPath.Reject`
   - Expected: plan.execution.decision.reason equals `batch-item-count-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a malformed empty batch")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 0,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: true
)
val window = gpu_wdb_batch_window(GpuWdbWorkKind.WebRank, budget.min_gpu_batch_bytes, 0, snapshot)
val plan = gpu_wdb_batch_plan(window, budget)
expect(plan.execution.decision.path).to_equal(GpuWdbDecisionPath.Reject)
expect(plan.execution.decision.reason).to_equal("batch-item-count-invalid")
```

</details>

#### should require CPU-owned metadata filters in NoSQL mode

- Submit NoSQL work without CPU-owned metadata filtering
   - Expected: decision.path equals `GpuWdbDecisionPath.Reject`
   - Expected: decision.reason equals `metadata-filter-must-stay-cpu-owned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit NoSQL work without CPU-owned metadata filtering")
val decision = gpu_wdb_nosql_mode_admits(65536, false, gpu_wdb_default_budget())
expect(decision.path).to_equal(GpuWdbDecisionPath.Reject)
expect(decision.reason).to_equal("metadata-filter-must-stay-cpu-owned")
```

</details>

#### should submit eligible web work through reusable pinned GPU queue accounting

- Reserve one reusable GPU stream and pinned host batch buffer
   - Expected: submission.dispatch_target equals `gpu_web_embedding_batch`
   - Expected: submission.stream_id equals `0`
   - Expected: submission.pinned_host_bytes equals `budget.min_gpu_batch_bytes * 2`
   - Expected: submission.state.queue_depth equals `1`
   - Expected: submission.state.gpu_hit_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reserve one reusable GPU stream and pinned host batch buffer")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(4)
val submission = gpu_wdb_submit_batch(
    state,
    GpuWdbWorkKind.WebEmbedding,
    budget.min_gpu_batch_bytes * 2,
    2,
    true,
    true,
    true,
    budget
)
expect(submission.accepted).to_be(true)
expect(submission.dispatch_target).to_equal("gpu_web_embedding_batch")
expect(submission.stream_id).to_equal(0)
expect(submission.pinned_host_bytes).to_equal(budget.min_gpu_batch_bytes * 2)
expect(submission.state.queue_depth).to_equal(1)
expect(submission.state.gpu_hit_count).to_equal(1)
```

</details>

#### should expose reusable execution evidence for accepted GPU submissions

- Convert queue submission state into benchmark-ready evidence
- gpu wdb queue initial
   - Expected: evidence.work_kind equals `GpuWdbWorkKind.DbVectorSearch`
   - Expected: evidence.work_kind_name equals `db_vector_search`
   - Expected: evidence.batch_size equals `4`
   - Expected: evidence.batch_bytes equals `budget.min_gpu_batch_bytes * 4`
   - Expected: evidence.transfer_bytes equals `budget.min_gpu_batch_bytes * 4`
   - Expected: evidence.kernel_time_us equals `40`
   - Expected: evidence.completion_latency_us equals `40`
   - Expected: evidence.gpu_hits equals `1`
   - Expected: evidence.cpu_fallbacks equals `0`
   - Expected: evidence.stream_id equals `0`
   - Expected: evidence.fallback_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert queue submission state into benchmark-ready evidence")
val budget = gpu_wdb_default_budget()
val submission = gpu_wdb_submit_batch(
    gpu_wdb_queue_initial(4),
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 4,
    4,
    true,
    true,
    true,
    budget
)
val evidence = gpu_wdb_submission_evidence(
    submission,
    4,
    budget.min_gpu_batch_bytes * 4,
    100,
    140
)
expect(evidence.work_kind).to_equal(GpuWdbWorkKind.DbVectorSearch)
expect(evidence.work_kind_name).to_equal("db_vector_search")
expect(evidence.accepted).to_be(true)
expect(evidence.batch_size).to_equal(4)
expect(evidence.batch_bytes).to_equal(budget.min_gpu_batch_bytes * 4)
expect(evidence.transfer_bytes).to_equal(budget.min_gpu_batch_bytes * 4)
expect(evidence.kernel_time_us).to_equal(40)
expect(evidence.completion_latency_us).to_equal(40)
expect(evidence.gpu_hits).to_equal(1)
expect(evidence.cpu_fallbacks).to_equal(0)
expect(evidence.stream_id).to_equal(0)
expect(evidence.fallback_reason).to_equal("")
```

</details>

#### should complete reusable GPU queue submissions and release pinned bytes

- Release queue depth and pinned host bytes after GPU completion
   - Expected: completed.queue_depth equals `0`
   - Expected: completed.completed_count equals `1`
   - Expected: completed.pinned_host_bytes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Release queue depth and pinned host bytes after GPU completion")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val submission = gpu_wdb_submit_batch(
    state,
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 3,
    3,
    true,
    true,
    true,
    budget
)
val completed = gpu_wdb_complete_submission(submission.state, submission)
expect(completed.queue_depth).to_equal(0)
expect(completed.completed_count).to_equal(1)
expect(completed.pinned_host_bytes).to_equal(0)
```

</details>

#### should keep tiny reusable queue submissions on CPU without reserving streams

- Avoid GPU queue reservation for tiny batches
   - Expected: submission.dispatch_target equals `cpu_fallback`
   - Expected: submission.stream_id equals `-1`
   - Expected: submission.pinned_host_bytes equals `0`
   - Expected: submission.state.queue_depth equals `0`
   - Expected: submission.state.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Avoid GPU queue reservation for tiny batches")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val submission = gpu_wdb_submit_batch(
    state,
    GpuWdbWorkKind.WebRank,
    budget.min_gpu_batch_bytes - 1,
    1,
    true,
    true,
    true,
    budget
)
expect(submission.accepted).to_be(false)
expect(submission.dispatch_target).to_equal("cpu_fallback")
expect(submission.stream_id).to_equal(-1)
expect(submission.pinned_host_bytes).to_equal(0)
expect(submission.state.queue_depth).to_equal(0)
expect(submission.state.cpu_fallback_count).to_equal(1)
```

</details>

#### should expose fallback evidence without fake transfer or kernel time

- Convert CPU fallback submissions into explicit fallback evidence
- gpu wdb queue initial
   - Expected: evidence.batch_size equals `1`
   - Expected: evidence.batch_bytes equals `budget.min_gpu_batch_bytes - 1`
   - Expected: evidence.transfer_bytes equals `0`
   - Expected: evidence.kernel_time_us equals `0`
   - Expected: evidence.completion_latency_us equals `1`
   - Expected: evidence.gpu_hits equals `0`
   - Expected: evidence.cpu_fallbacks equals `1`
   - Expected: evidence.stream_id equals `-1`
   - Expected: evidence.fallback_reason equals `batch-too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert CPU fallback submissions into explicit fallback evidence")
val budget = gpu_wdb_default_budget()
val submission = gpu_wdb_submit_batch(
    gpu_wdb_queue_initial(2),
    GpuWdbWorkKind.WebRank,
    budget.min_gpu_batch_bytes - 1,
    1,
    true,
    true,
    true,
    budget
)
val evidence = gpu_wdb_submission_evidence(
    submission,
    1,
    budget.min_gpu_batch_bytes - 1,
    200,
    200
)
expect(evidence.accepted).to_be(false)
expect(evidence.batch_size).to_equal(1)
expect(evidence.batch_bytes).to_equal(budget.min_gpu_batch_bytes - 1)
expect(evidence.transfer_bytes).to_equal(0)
expect(evidence.kernel_time_us).to_equal(0)
expect(evidence.completion_latency_us).to_equal(1)
expect(evidence.gpu_hits).to_equal(0)
expect(evidence.cpu_fallbacks).to_equal(1)
expect(evidence.stream_id).to_equal(-1)
expect(evidence.fallback_reason).to_equal("batch-too-small")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)
- **Research:** [doc/01_research/local/gpu_web_db_offload.md](doc/01_research/local/gpu_web_db_offload.md)


</details>
