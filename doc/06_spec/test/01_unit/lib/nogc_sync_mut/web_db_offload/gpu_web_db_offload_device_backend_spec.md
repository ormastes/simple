# GPU Web/DB Device Backend Runner

> These scenarios protect the strict production backend boundary below the shared web/DB offload queue. A production device claim requires a native execution backend, a current target generation, a registered GPU target, and measured device timing.

<!-- sdn-diagram:id=gpu_web_db_offload_device_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_web_db_offload_device_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_web_db_offload_device_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_web_db_offload_device_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Web/DB Device Backend Runner

These scenarios protect the strict production backend boundary below the shared web/DB offload queue. A production device claim requires a native execution backend, a current target generation, a registered GPU target, and measured device timing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | doc/01_research/local/gpu_web_db_offload.md |
| Source | `test/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_device_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios protect the strict production backend boundary below the shared
web/DB offload queue. A production device claim requires a native execution
backend, a current target generation, a registered GPU target, and measured
device timing.

The runner is intentionally stricter than the host-safe registry helpers. Mock
and deterministic perf-only registries may still exercise planning and queue
accounting, but they cannot produce `production_device_claim=true`. Production
claims are reserved for native backends that can report a real device timer,
such as CUDA event timing.

## Examples

Use `gpu_wdb_run_device_batch` after a DB or web adapter has selected a batch
kind and the caller knows the expected loaded target generation. The result
returns both the queue submission and normalized execution evidence, so report
writers can distinguish CPU fallback, accepted queue dispatch, and measured
native-device execution without parsing ad hoc perf-driver output.

The strict runner keeps proxy and HTTP control-plane work on CPU through the
same shared contract checks used by the queue. It also keeps stale generations
on CPU before dispatch accounting, preventing old GPU code from producing fresh
production evidence.

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md
**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md
**Design:** doc/05_design/gpu_web_db_offload.md
**Research:** doc/01_research/local/gpu_web_db_offload.md

## Scenarios

### GPU web/db device backend runner

#### should accept measured native columnar scan backend evidence

- Run a registered scan/filter/project batch through a strict native device backend
   - Expected: result.submission.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: result.reason equals `production-device-measured`
   - Expected: result.evidence.device_time_us equals `37`
   - Expected: result.evidence.device_timing_source equals `cuda-event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a registered scan/filter/project batch through a strict native device backend")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(4)
val backend = gpu_wdb_device_backend(
    "cuda",
    3,
    ["gpu_db_columnar_scan_batch"],
    true,
    "cuda-device-0"
)
val result = gpu_wdb_run_device_batch(
    state,
    backend,
    GpuWdbWorkKind.DbScanFilterProject,
    budget.min_gpu_batch_bytes * 8,
    8,
    3,
    true,
    budget,
    100,
    180,
    37,
    "cuda-event"
)
expect(result.submission.accepted).to_be(true)
expect(result.submission.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(result.production_device_claim).to_be(true)
expect(result.reason).to_equal("production-device-measured")
expect(result.evidence.backend_timing_valid).to_be(true)
expect(result.evidence.device_time_us).to_equal(37)
expect(result.evidence.device_timing_source).to_equal("cuda-event")
```

</details>

#### should keep mock or perf-only backends from making production device claims

- Require native execution capability before the strict runner accepts GPU dispatch
   - Expected: result.submission.dispatch_target equals `cpu_fallback`
   - Expected: result.reason equals `gpu-unavailable`
   - Expected: result.evidence.device_time_us equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require native execution capability before the strict runner accepts GPU dispatch")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(4)
val backend = gpu_wdb_device_backend(
    "host-safe-mock",
    1,
    ["gpu_db_vector_search_batch"],
    false,
    "mock-device"
)
val result = gpu_wdb_run_device_batch(
    state,
    backend,
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 8,
    8,
    1,
    true,
    budget,
    100,
    180,
    37,
    "mock-timer"
)
expect(result.submission.accepted).to_be(false)
expect(result.submission.dispatch_target).to_equal("cpu_fallback")
expect(result.production_device_claim).to_be(false)
expect(result.reason).to_equal("gpu-unavailable")
expect(result.evidence.backend_timing_valid).to_be(false)
expect(result.evidence.device_time_us).to_equal(0)
```

</details>

#### should fall back before dispatch when the native target generation is stale

- Bind production device dispatch to the expected loaded target generation
   - Expected: result.submission.dispatch_target equals `cpu_fallback`
   - Expected: result.submission.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind production device dispatch to the expected loaded target generation")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(4)
val backend = gpu_wdb_device_backend(
    "cuda",
    3,
    ["gpu_db_vector_search_batch"],
    true,
    "cuda-device-0"
)
val result = gpu_wdb_run_device_batch(
    state,
    backend,
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 8,
    8,
    4,
    true,
    budget,
    100,
    180,
    37,
    "cuda-event"
)
expect(result.submission.accepted).to_be(false)
expect(result.submission.dispatch_target).to_equal("cpu_fallback")
expect(result.submission.reason).to_equal("stale-generation")
expect(result.production_device_claim).to_be(false)
expect(result.evidence.backend_timing_valid).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)
- **Research:** [doc/01_research/local/gpu_web_db_offload.md](doc/01_research/local/gpu_web_db_offload.md)


</details>
