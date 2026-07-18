# Gpu Web Db Offload Contract Specification

> <details>

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
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Web Db Offload Contract Specification

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU web/db offload contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
