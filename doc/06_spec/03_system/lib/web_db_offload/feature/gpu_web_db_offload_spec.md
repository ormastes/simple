# Gpu Web Db Offload Specification

> <details>

<!-- sdn-diagram:id=gpu_web_db_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_web_db_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_web_db_offload_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_web_db_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Web Db Offload Specification

## Scenarios

### GPU web/db offload reliability-first system contract

#### should prove CPU fallback when GPU is unavailable

- Evaluate an unavailable GPU path
- system request
   - Expected: fallback.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: fallback.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evaluate an unavailable GPU path")
val budget = gpu_wdb_default_budget()
val fallback = gpu_wdb_decide(
    system_request(GpuWdbWorkKind.DbVectorSearch, budget.min_gpu_batch_bytes, 0, false, true, true),
    budget
)
expect(fallback.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(fallback.reason).to_equal("gpu-unavailable")
```

</details>

#### should prove GPU evidence when a coarse web path is eligible

- Evaluate an eligible coarse web rank batch
- system request
   - Expected: gpu_decision.path equals `GpuWdbDecisionPath.GpuEvidence`
   - Expected: gpu_decision.reason equals `gpu-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evaluate an eligible coarse web rank batch")
val budget = gpu_wdb_default_budget()
val gpu_decision = gpu_wdb_decide(
    system_request(GpuWdbWorkKind.WebRank, budget.min_gpu_batch_bytes, 0, true, true, true),
    budget
)
expect(gpu_decision.path).to_equal(GpuWdbDecisionPath.GpuEvidence)
expect(gpu_decision.reason).to_equal("gpu-evidence")
```

</details>

#### should route eligible work through a reusable GPU library plan

- Build a reusable plan for an eligible embedding batch
   - Expected: plan.decision.reason equals `gpu-evidence`
   - Expected: plan.target equals `gpu_web_embedding_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a reusable plan for an eligible embedding batch")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 0,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: true
)
val req = gpu_wdb_request(GpuWdbWorkKind.WebEmbedding, budget.min_gpu_batch_bytes, snapshot)
val plan = gpu_wdb_execution_plan(req, budget)
expect(plan.decision.reason).to_equal("gpu-evidence")
expect(plan.target).to_equal("gpu_web_embedding_batch")
```

</details>

#### should batch DB vector work through shared GPU queue accounting

- Build a reusable DB vector batch plan
   - Expected: plan.execution.decision.reason equals `gpu-evidence`
   - Expected: plan.execution.target equals `gpu_db_vector_search_batch`
   - Expected: plan.queue_depth_after equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a reusable DB vector batch plan")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 1,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: true
)
val window = gpu_wdb_batch_window(GpuWdbWorkKind.DbVectorSearch, budget.min_gpu_batch_bytes * 8, 8, snapshot)
val plan = gpu_wdb_batch_plan(window, budget)
expect(plan.execution.decision.reason).to_equal("gpu-evidence")
expect(plan.execution.target).to_equal("gpu_db_vector_search_batch")
expect(plan.queue_depth_after).to_equal(2)
```

</details>

#### should enforce RAM mode stale generation safety

- RAM mode rejects stale generation
   - Expected: ram.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("RAM mode rejects stale generation")
val budget = gpu_wdb_default_budget()
val ram = gpu_wdb_ram_mode_admits(budget.min_gpu_batch_bytes, false, budget)
expect(ram.reason).to_equal("stale-generation")
```

</details>

#### should enforce SSD mode WAL generation safety

- SSD mode rejects stale WAL generation
   - Expected: ssd.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("SSD mode rejects stale WAL generation")
val budget = gpu_wdb_default_budget()
val ssd = gpu_wdb_ssd_mode_admits(budget.min_gpu_batch_bytes, false, budget)
expect(ssd.reason).to_equal("stale-generation")
```

</details>

#### should enforce NoSQL CPU metadata filter ownership

- NoSQL mode rejects GPU-owned metadata filtering
   - Expected: nosql.reason equals `metadata-filter-must-stay-cpu-owned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("NoSQL mode rejects GPU-owned metadata filtering")
val budget = gpu_wdb_default_budget()
val nosql = gpu_wdb_nosql_mode_admits(budget.min_gpu_batch_bytes, false, budget)
expect(nosql.reason).to_equal("metadata-filter-must-stay-cpu-owned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU web/db offload reliability-first system contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
