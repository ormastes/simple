# GPU Web/DB Offload Target Registry

> The GPU web/DB offload library is the reusable safety boundary shared by web route batches, DB query batches, NoSQL document filters, and vector search adapters. It records GPU evidence only when a named executable target exists, the loaded target generation is current, and CPU fallback remains available for non-GPU-safe work.

<!-- sdn-diagram:id=gpu_web_db_offload_library_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_web_db_offload_library_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_web_db_offload_library_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_web_db_offload_library_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Web/DB Offload Target Registry

The GPU web/DB offload library is the reusable safety boundary shared by web route batches, DB query batches, NoSQL document filters, and vector search adapters. It records GPU evidence only when a named executable target exists, the loaded target generation is current, and CPU fallback remains available for non-GPU-safe work.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md |
| Source | `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_library_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The GPU web/DB offload library is the reusable safety boundary shared by web
route batches, DB query batches, NoSQL document filters, and vector search
adapters. It records GPU evidence only when a named executable target exists,
the loaded target generation is current, and CPU fallback remains available for
non-GPU-safe work.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- GPU target registration is required before queue evidence can claim GPU use.
- Stale target generations fall back to CPU before dispatch accounting.
- HTTP proxy forwarding remains CPU-owned control-plane work.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md

## Examples

Use `gpu_wdb_submit_registered_batch_for_generation` when the caller knows the
expected loaded GPU target generation. Use the lower-level
`gpu_wdb_submit_registered_batch` only when the caller has already computed a
freshness boolean from authoritative storage or model-generation evidence.

## Scenarios

### GPU web/db offload target registry

#### should refuse GPU evidence when vector target is not registered

- Keep vector search on CPU when no executable GPU target exists
   - Expected: submission.dispatch_target equals `cpu_fallback`
   - Expected: submission.reason equals `gpu-unavailable`
   - Expected: submission.state.gpu_hit_count equals `0`
   - Expected: submission.state.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep vector search on CPU when no executable GPU target exists")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_empty()
val submission = gpu_wdb_submit_registered_batch(
    state,
    registry,
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 4,
    4,
    true,
    true,
    true,
    budget
)
expect(gpu_wdb_library_kind_available(registry, GpuWdbWorkKind.DbVectorSearch)).to_be(false)
expect(submission.accepted).to_be(false)
expect(submission.dispatch_target).to_equal("cpu_fallback")
expect(submission.reason).to_equal("gpu-unavailable")
expect(submission.state.gpu_hit_count).to_equal(0)
expect(submission.state.cpu_fallback_count).to_equal(1)
```

</details>

#### should allow GPU queue evidence when vector target is registered

- Submit vector search to the reusable GPU target registry
   - Expected: submission.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: submission.state.queue_depth equals `1`
   - Expected: submission.state.gpu_hit_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit vector search to the reusable GPU target registry")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_with_targets(
    "cuda",
    1,
    ["gpu_db_vector_search_batch"]
)
val submission = gpu_wdb_submit_registered_batch(
    state,
    registry,
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 4,
    4,
    true,
    true,
    true,
    budget
)
expect(gpu_wdb_library_kind_available(registry, GpuWdbWorkKind.DbVectorSearch)).to_be(true)
expect(submission.accepted).to_be(true)
expect(submission.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(submission.state.queue_depth).to_equal(1)
expect(submission.state.gpu_hit_count).to_equal(1)
```

</details>

#### should build registry snapshots with explicit generation freshness

- Centralize GPU library generation checks for web and DB adapters


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Centralize GPU library generation checks for web and DB adapters")
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_with_targets(
    "cuda",
    7,
    ["gpu_db_vector_search_batch"]
)
val current = gpu_wdb_library_snapshot(state, registry, 7, true, true)
val stale = gpu_wdb_library_snapshot(state, registry, 8, true, true)
val empty = gpu_wdb_library_snapshot(state, gpu_wdb_library_empty(), 0, true, true)
expect(gpu_wdb_library_generation_current(registry, 7)).to_be(true)
expect(gpu_wdb_library_generation_current(registry, 8)).to_be(false)
expect(current.gpu_available).to_be(true)
expect(current.generation_current).to_be(true)
expect(stale.generation_current).to_be(false)
expect(empty.gpu_available).to_be(false)
```

</details>

#### should keep stale registered GPU libraries on CPU fallback

- Reject GPU evidence when the loaded target generation is stale
   - Expected: submission.dispatch_target equals `cpu_fallback`
   - Expected: submission.reason equals `stale-generation`
   - Expected: submission.state.gpu_hit_count equals `0`
   - Expected: submission.state.cpu_fallback_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject GPU evidence when the loaded target generation is stale")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_with_targets(
    "cuda",
    7,
    ["gpu_db_vector_search_batch"]
)
val submission = gpu_wdb_submit_registered_batch_for_generation(
    state,
    registry,
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 4,
    4,
    true,
    8,
    true,
    budget
)
expect(submission.accepted).to_be(false)
expect(submission.dispatch_target).to_equal("cpu_fallback")
expect(submission.reason).to_equal("stale-generation")
expect(submission.state.gpu_hit_count).to_equal(0)
expect(submission.state.cpu_fallback_count).to_equal(1)
```

</details>

#### should not allow proxy forwarding as a GPU target even if named

- Keep HTTP proxy forwarding out of GPU library dispatch
   - Expected: submission.dispatch_target equals `cpu_fallback`
   - Expected: submission.reason equals `control-plane-stays-on-cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep HTTP proxy forwarding out of GPU library dispatch")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(2)
val registry = gpu_wdb_library_with_targets(
    "cuda",
    1,
    ["cpu_proxy_stream"]
)
val submission = gpu_wdb_submit_registered_batch(
    state,
    registry,
    GpuWdbWorkKind.ProxyForwarding,
    budget.min_gpu_batch_bytes * 4,
    4,
    true,
    true,
    true,
    budget
)
expect(submission.accepted).to_be(false)
expect(submission.dispatch_target).to_equal("cpu_fallback")
expect(submission.reason).to_equal("control-plane-stays-on-cpu")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)
- **Research:** [doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md](doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md)


</details>
