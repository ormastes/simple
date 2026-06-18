# GPU Web/DB Native Device Probe

> These scenarios protect the fail-closed native device probe used before GPU Web/DB performance reports may claim hardware execution. Runtime backend availability is evidence only for whether a backend can be seen by the runtime; throughput claims still require measured device timing rows.

<!-- sdn-diagram:id=gpu_web_db_offload_native_device_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_web_db_offload_native_device_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_web_db_offload_native_device_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_web_db_offload_native_device_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Web/DB Native Device Probe

These scenarios protect the fail-closed native device probe used before GPU Web/DB performance reports may claim hardware execution. Runtime backend availability is evidence only for whether a backend can be seen by the runtime; throughput claims still require measured device timing rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/nfr/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | doc/01_research/local/gpu_web_db_offload.md |
| Source | `test/05_perf/web_db_offload/gpu_web_db_offload_native_device_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios protect the fail-closed native device probe used before GPU
Web/DB performance reports may claim hardware execution. Runtime backend
availability is evidence only for whether a backend can be seen by the runtime;
throughput claims still require measured device timing rows.

## Examples

Use the probe driver output to decide whether the report should say
`unavailable`, `available_unmeasured`, or `measured`.

**Requirements:** doc/02_requirements/nfr/gpu_web_db_offload.md
**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md
**Design:** doc/05_design/gpu_web_db_offload.md
**Research:** doc/01_research/local/gpu_web_db_offload.md

## Scenarios

### GPU web/db native device backend probe

#### should expose runtime backend availability without throughput claims

- Read CUDA and Vulkan backend availability from runtime externs
   - Expected: probe.cuda_device_handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read CUDA and Vulkan backend availability from runtime externs")
val probe = gpu_wdb_native_backend_probe()
expect(probe.cuda_available).to_be_greater_than(-1)
expect(probe.cuda_device_count).to_be_greater_than(-1)
expect(probe.cuda_device_handle).to_equal(0)
expect(probe.cuda_compute_capability).to_be_greater_than(-4)
expect(probe.vk_available).to_be_greater_than(-1)
expect(probe.vulkan_available).to_be_greater_than(-1)
expect(probe.vulkan_device_count).to_be_greater_than(-1)
```

</details>

#### should report only availability or unavailability before measured rows

- Classify runtime backend availability as non-throughput evidence
   - Expected: status equals `available_unmeasured`
   - Expected: status equals `unavailable`
   - Expected: probe.cuda_device_name equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify runtime backend availability as non-throughput evidence")
val probe = gpu_wdb_native_backend_probe()
val status = gpu_wdb_native_backend_probe_status(probe)
if status == "available_unmeasured":
    expect(status).to_equal("available_unmeasured")
else:
    expect(status).to_equal("unavailable")
    expect(probe.cuda_device_name).to_equal("unavailable")
```

</details>

#### should accept only positive GPU device timing rows as measured

- Validate measured row fields before report generation may claim native GPU execution
   - Expected: vector_status equals `measured`
   - Expected: columnar_status equals `measured`
   - Expected: web_inference_status equals `measured`
   - Expected: web_embedding_status equals `measured`
   - Expected: web_rank_status equals `measured`
   - Expected: web_transform_status equals `measured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate measured row fields before report generation may claim native GPU execution")
val vector_status = gpu_wdb_native_measured_row_status("measured", "gpu_db_vector_search_batch", 168, 168, 8, "native-device-measured")
val columnar_status = gpu_wdb_native_measured_row_status("measured", "gpu_db_columnar_scan_batch", 168, 168, 8, "native-device-measured")
val web_inference_status = gpu_wdb_native_measured_row_status("measured", "gpu_web_inference_batch", 168, 168, 8, "native-device-measured")
val web_embedding_status = gpu_wdb_native_measured_row_status("measured", "gpu_web_embedding_batch", 168, 168, 8, "native-device-measured")
val web_rank_status = gpu_wdb_native_measured_row_status("measured", "gpu_web_rank_batch", 168, 168, 8, "native-device-measured")
val web_transform_status = gpu_wdb_native_measured_row_status("measured", "gpu_web_transform_batch", 168, 168, 8, "native-device-measured")
expect(vector_status).to_equal("measured")
expect(columnar_status).to_equal("measured")
expect(web_inference_status).to_equal("measured")
expect(web_embedding_status).to_equal("measured")
expect(web_rank_status).to_equal("measured")
expect(web_transform_status).to_equal("measured")
```

</details>

#### should reject fallback or zero-time rows as measured evidence

- Reject report rows that have fallback targets or missing measured timing
   - Expected: fallback_status equals `invalid_measured`
   - Expected: zero_status equals `invalid_measured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject report rows that have fallback targets or missing measured timing")
val fallback_status = gpu_wdb_native_measured_row_status("measured", "cpu_fallback", 168, 168, 8, "native-device-measured")
val zero_status = gpu_wdb_native_measured_row_status("measured", "gpu_db_vector_search_batch", 0, 168, 8, "native-device-measured")
expect(fallback_status).to_equal("invalid_measured")
expect(zero_status).to_equal("invalid_measured")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/gpu_web_db_offload.md](doc/02_requirements/nfr/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)
- **Research:** [doc/01_research/local/gpu_web_db_offload.md](doc/01_research/local/gpu_web_db_offload.md)


</details>
