# GPU Web/DB Offload Benchmark Evidence

> This host-safe performance spec verifies that the reusable GPU Web/DB offload facades emit the metrics required before any production GPU speedup claim. It does not require GPU hardware and does not claim native throughput; it proves the report shape for CPU fallback, GPU-hit accounting, queue pressure, batch size, transfer bytes, kernel time, completion latency, and tiny-batch rejection.

<!-- sdn-diagram:id=gpu_web_db_offload_bench_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_web_db_offload_bench_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_web_db_offload_bench_spec -> std
gpu_web_db_offload_bench_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_web_db_offload_bench_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Web/DB Offload Benchmark Evidence

This host-safe performance spec verifies that the reusable GPU Web/DB offload facades emit the metrics required before any production GPU speedup claim. It does not require GPU hardware and does not claim native throughput; it proves the report shape for CPU fallback, GPU-hit accounting, queue pressure, batch size, transfer bytes, kernel time, completion latency, and tiny-batch rejection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/nfr/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | doc/01_research/local/gpu_web_db_offload.md |
| Source | `test/05_perf/web_db_offload/gpu_web_db_offload_bench_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This host-safe performance spec verifies that the reusable GPU Web/DB offload
facades emit the metrics required before any production GPU speedup claim. It
does not require GPU hardware and does not claim native throughput; it proves
the report shape for CPU fallback, GPU-hit accounting, queue pressure, batch
size, transfer bytes, kernel time, completion latency, and tiny-batch rejection.

## Examples

Use this spec as the deterministic benchmark-report contract for future native
or hardware-backed proxy and database benchmark runners.

**Requirements:** doc/02_requirements/nfr/gpu_web_db_offload.md
**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md
**Design:** doc/05_design/gpu_web_db_offload.md
**Research:** doc/01_research/local/gpu_web_db_offload.md

## Scenarios

### GPU web/db offload benchmark evidence

#### should report GPU hit metrics for coarse vector batches

- Create a host-safe GPU-hit metrics row for a coarse vector batch
   - Expected: row.name equals `db_vector_gpu_hit`
   - Expected: row.backend equals `host-safe-mock`
   - Expected: row.dataset equals `oracle_vectors_1024x128`
   - Expected: row.row_count equals `1024`
   - Expected: row.vector_dimensions equals `128`
   - Expected: row.batch_size equals `8`
   - Expected: row.batch_bytes equals `gpu_wdb_default_budget().min_gpu_batch_bytes * 8`
   - Expected: row.transfer_bytes equals `row.batch_bytes`
   - Expected: row.queue_depth equals `1`
   - Expected: row.gpu_hits equals `1`
   - Expected: row.cpu_fallbacks equals `0`
   - Expected: row.timeout_count equals `0`
   - Expected: row.error_count equals `0`
   - Expected: row.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: row.device_time_us equals `0`
   - Expected: row.device_timing_source equals `host-derived`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a host-safe GPU-hit metrics row for a coarse vector batch")
val row = make_gpu_vector_row()
expect(row.name).to_equal("db_vector_gpu_hit")
expect(row.backend).to_equal("host-safe-mock")
expect(row.dataset).to_equal("oracle_vectors_1024x128")
expect(row.row_count).to_equal(1024)
expect(row.vector_dimensions).to_equal(128)
expect(row.batch_size).to_equal(8)
expect(row.batch_bytes).to_equal(gpu_wdb_default_budget().min_gpu_batch_bytes * 8)
expect(row.transfer_bytes).to_equal(row.batch_bytes)
expect(row.kernel_time_us).to_be_greater_than(0)
expect(row.completion_latency_us).to_be_greater_than(0)
expect(row.p50_us).to_be_greater_than(0)
expect(row.p95_us).to_be_greater_than(0)
expect(row.p99_us).to_be_greater_than(0)
expect(row.max_rss_kb).to_be_greater_than(0)
expect(row.queue_depth).to_equal(1)
expect(row.gpu_hits).to_equal(1)
expect(row.cpu_fallbacks).to_equal(0)
expect(row.timeout_count).to_equal(0)
expect(row.error_count).to_equal(0)
expect(row.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(row.device_time_us).to_equal(0)
expect(row.device_timing_source).to_equal("host-derived")
expect(row.backend_timing_valid).to_be(false)
```

</details>

#### should reject tiny batches for performance claims and report fallback reason

- Create a fallback metrics row for a tiny web embedding batch
   - Expected: row.name equals `web_embedding_tiny_cpu_fallback`
   - Expected: row.document_count equals `1`
   - Expected: row.batch_size equals `1`
   - Expected: row.batch_bytes equals `0`
   - Expected: row.transfer_bytes equals `0`
   - Expected: row.kernel_time_us equals `0`
   - Expected: row.queue_depth equals `0`
   - Expected: row.gpu_hits equals `0`
   - Expected: row.cpu_fallbacks equals `1`
   - Expected: row.fallback_reason equals `batch-too-small`
   - Expected: row.dispatch_target equals `cpu_fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a fallback metrics row for a tiny web embedding batch")
val row = make_cpu_tiny_batch_row()
expect(row.name).to_equal("web_embedding_tiny_cpu_fallback")
expect(row.document_count).to_equal(1)
expect(row.batch_size).to_equal(1)
expect(row.batch_bytes).to_equal(0)
expect(row.transfer_bytes).to_equal(0)
expect(row.kernel_time_us).to_equal(0)
expect(row.completion_latency_us).to_be_greater_than(0)
expect(row.queue_depth).to_equal(0)
expect(row.gpu_hits).to_equal(0)
expect(row.cpu_fallbacks).to_equal(1)
expect(row.fallback_reason).to_equal("batch-too-small")
expect(row.dispatch_target).to_equal("cpu_fallback")
expect(row.backend_timing_valid).to_be(false)
```

</details>

#### should report validated production web inference device evidence

- Create a web inference metrics row only after CPU and GPU candidate responses match
   - Expected: row.name equals `web_inference_device_validated_contract`
   - Expected: row.backend equals `cuda`
   - Expected: row.dataset equals `web_inference_16x512_response_match`
   - Expected: row.document_count equals `16`
   - Expected: row.batch_size equals `16`
   - Expected: row.call_count equals `1`
   - Expected: row.batch_bytes equals `16 * 512`
   - Expected: row.transfer_bytes equals `row.batch_bytes`
   - Expected: row.dispatch_target equals `gpu_web_inference_batch`
   - Expected: row.gpu_hits equals `1`
   - Expected: row.cpu_fallbacks equals `0`
   - Expected: row.error_count equals `0`
   - Expected: row.device_time_us equals `41`
   - Expected: row.device_timing_source equals `cuda-event-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a web inference metrics row only after CPU and GPU candidate responses match")
val row = make_web_inference_device_validated_row()
expect(row.name).to_equal("web_inference_device_validated_contract")
expect(row.backend).to_equal("cuda")
expect(row.dataset).to_equal("web_inference_16x512_response_match")
expect(row.document_count).to_equal(16)
expect(row.batch_size).to_equal(16)
expect(row.call_count).to_equal(1)
expect(row.batch_bytes).to_equal(16 * 512)
expect(row.transfer_bytes).to_equal(row.batch_bytes)
expect(row.dispatch_target).to_equal("gpu_web_inference_batch")
expect(row.gpu_hits).to_equal(1)
expect(row.cpu_fallbacks).to_equal(0)
expect(row.error_count).to_equal(0)
expect(row.device_time_us).to_equal(41)
expect(row.device_timing_source).to_equal("cuda-event-contract")
expect(row.backend_timing_valid).to_be(true)
```

</details>

#### should report validated production web embedding and rank device evidence

- Create web embedding and rank metrics rows only after CPU and GPU candidate responses match
   - Expected: embedding.name equals `web_embedding_device_validated_contract`
   - Expected: embedding.dataset equals `web_embedding_16x512_response_match`
   - Expected: embedding.document_count equals `16`
   - Expected: embedding.call_count equals `1`
   - Expected: embedding.batch_bytes equals `16 * 512`
   - Expected: embedding.dispatch_target equals `gpu_web_embedding_batch`
   - Expected: embedding.gpu_hits equals `1`
   - Expected: embedding.cpu_fallbacks equals `0`
   - Expected: embedding.device_time_us equals `43`
   - Expected: embedding.device_timing_source equals `cuda-event-contract`
   - Expected: rank.name equals `web_rank_device_validated_contract`
   - Expected: rank.dataset equals `web_rank_32x256_response_match`
   - Expected: rank.document_count equals `32`
   - Expected: rank.call_count equals `1`
   - Expected: rank.batch_bytes equals `32 * 256`
   - Expected: rank.dispatch_target equals `gpu_web_rank_batch`
   - Expected: rank.gpu_hits equals `1`
   - Expected: rank.cpu_fallbacks equals `0`
   - Expected: rank.device_time_us equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create web embedding and rank metrics rows only after CPU and GPU candidate responses match")
val embedding = make_web_embedding_device_validated_row()
val rank = make_web_rank_device_validated_row()
expect(embedding.name).to_equal("web_embedding_device_validated_contract")
expect(embedding.dataset).to_equal("web_embedding_16x512_response_match")
expect(embedding.document_count).to_equal(16)
expect(embedding.call_count).to_equal(1)
expect(embedding.batch_bytes).to_equal(16 * 512)
expect(embedding.dispatch_target).to_equal("gpu_web_embedding_batch")
expect(embedding.gpu_hits).to_equal(1)
expect(embedding.cpu_fallbacks).to_equal(0)
expect(embedding.device_time_us).to_equal(43)
expect(embedding.device_timing_source).to_equal("cuda-event-contract")
expect(embedding.backend_timing_valid).to_be(true)
expect(rank.name).to_equal("web_rank_device_validated_contract")
expect(rank.dataset).to_equal("web_rank_32x256_response_match")
expect(rank.document_count).to_equal(32)
expect(rank.call_count).to_equal(1)
expect(rank.batch_bytes).to_equal(32 * 256)
expect(rank.dispatch_target).to_equal("gpu_web_rank_batch")
expect(rank.gpu_hits).to_equal(1)
expect(rank.cpu_fallbacks).to_equal(0)
expect(rank.device_time_us).to_equal(47)
expect(rank.backend_timing_valid).to_be(true)
```

</details>

#### should report validated production web transform device evidence

- Create a web transform metrics row only after CPU and GPU candidate responses match
   - Expected: transform.name equals `web_transform_device_validated_contract`
   - Expected: transform.dataset equals `web_transform_8x2048_response_match`
   - Expected: transform.document_count equals `8`
   - Expected: transform.batch_size equals `8`
   - Expected: transform.call_count equals `1`
   - Expected: transform.batch_bytes equals `8 * 2048`
   - Expected: transform.transfer_bytes equals `transform.batch_bytes`
   - Expected: transform.dispatch_target equals `gpu_web_transform_batch`
   - Expected: transform.gpu_hits equals `1`
   - Expected: transform.cpu_fallbacks equals `0`
   - Expected: transform.device_time_us equals `51`
   - Expected: transform.device_timing_source equals `cuda-event-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a web transform metrics row only after CPU and GPU candidate responses match")
val transform = make_web_transform_device_validated_row()
expect(transform.name).to_equal("web_transform_device_validated_contract")
expect(transform.dataset).to_equal("web_transform_8x2048_response_match")
expect(transform.document_count).to_equal(8)
expect(transform.batch_size).to_equal(8)
expect(transform.call_count).to_equal(1)
expect(transform.batch_bytes).to_equal(8 * 2048)
expect(transform.transfer_bytes).to_equal(transform.batch_bytes)
expect(transform.dispatch_target).to_equal("gpu_web_transform_batch")
expect(transform.gpu_hits).to_equal(1)
expect(transform.cpu_fallbacks).to_equal(0)
expect(transform.device_time_us).to_equal(51)
expect(transform.device_timing_source).to_equal("cuda-event-contract")
expect(transform.backend_timing_valid).to_be(true)
```

</details>

#### should report production-facing validated web transform throughput evidence

- Measure repeated transform validation through the strict web profile backend boundary
   - Expected: throughput.name equals `web_transform_validated_profile_throughput_contract`
   - Expected: throughput.dataset equals `web_transform_4x8x2048_response_match`
   - Expected: throughput.document_count equals `32`
   - Expected: throughput.batch_size equals `32`
   - Expected: throughput.call_count equals `4`
   - Expected: throughput.batch_bytes equals `32 * 2048`
   - Expected: throughput.dispatch_target equals `gpu_web_transform_batch`
   - Expected: throughput.gpu_hits equals `4`
   - Expected: throughput.cpu_fallbacks equals `0`
   - Expected: throughput.error_count equals `0`
   - Expected: throughput.device_time_us equals `204`
   - Expected: throughput.device_timing_source equals `cuda-event-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure repeated transform validation through the strict web profile backend boundary")
val throughput = make_web_transform_validated_throughput_row()
expect(throughput.name).to_equal("web_transform_validated_profile_throughput_contract")
expect(throughput.dataset).to_equal("web_transform_4x8x2048_response_match")
expect(throughput.document_count).to_equal(32)
expect(throughput.batch_size).to_equal(32)
expect(throughput.call_count).to_equal(4)
expect(throughput.batch_bytes).to_equal(32 * 2048)
expect(throughput.dispatch_target).to_equal("gpu_web_transform_batch")
expect(throughput.gpu_hits).to_equal(4)
expect(throughput.cpu_fallbacks).to_equal(0)
expect(throughput.error_count).to_equal(0)
expect(throughput.device_time_us).to_equal(204)
expect(throughput.device_timing_source).to_equal("cuda-event-contract")
expect(throughput.backend_timing_valid).to_be(true)
```

</details>

#### should report validated SSD materialized scan evidence from a DBFS fixture

- Materialize persisted DBFS pages before crossing the strict DB device backend boundary
   - Expected: row.name equals `db_ssd_materialized_scan_device_validated_contract`
   - Expected: row.backend equals `cuda`
   - Expected: row.dataset equals `dbfs_ssd_materialized_scan_2x1024_row_match`
   - Expected: row.row_count equals `2`
   - Expected: row.batch_size equals `2`
   - Expected: row.call_count equals `1`
   - Expected: row.batch_bytes equals `2 * 1024`
   - Expected: row.transfer_bytes equals `row.batch_bytes`
   - Expected: row.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: row.gpu_hits equals `1`
   - Expected: row.cpu_fallbacks equals `0`
   - Expected: row.error_count equals `0`
   - Expected: row.device_time_us equals `37`
   - Expected: row.device_timing_source equals `cuda-event-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Materialize persisted DBFS pages before crossing the strict DB device backend boundary")
val row = make_db_ssd_materialized_scan_device_validated_row()
expect(row.name).to_equal("db_ssd_materialized_scan_device_validated_contract")
expect(row.backend).to_equal("cuda")
expect(row.dataset).to_equal("dbfs_ssd_materialized_scan_2x1024_row_match")
expect(row.row_count).to_equal(2)
expect(row.batch_size).to_equal(2)
expect(row.call_count).to_equal(1)
expect(row.batch_bytes).to_equal(2 * 1024)
expect(row.transfer_bytes).to_equal(row.batch_bytes)
expect(row.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(row.gpu_hits).to_equal(1)
expect(row.cpu_fallbacks).to_equal(0)
expect(row.error_count).to_equal(0)
expect(row.device_time_us).to_equal(37)
expect(row.device_timing_source).to_equal("cuda-event-contract")
expect(row.backend_timing_valid).to_be(true)
```

</details>

#### should report repeated SSD materialized scan validation through the DB profile

- Measure repeated DBFS-backed SSD scan validation through the reusable DB profile boundary
   - Expected: throughput.name equals `db_ssd_materialized_scan_profile_throughput_contract`
   - Expected: throughput.dataset equals `dbfs_ssd_materialized_scan_3x2x1024_row_match`
   - Expected: throughput.row_count equals `6`
   - Expected: throughput.batch_size equals `6`
   - Expected: throughput.call_count equals `3`
   - Expected: throughput.batch_bytes equals `3 * 2 * 1024`
   - Expected: throughput.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: throughput.gpu_hits equals `3`
   - Expected: throughput.cpu_fallbacks equals `0`
   - Expected: throughput.error_count equals `0`
   - Expected: throughput.device_time_us equals `111`
   - Expected: throughput.device_timing_source equals `cuda-event-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure repeated DBFS-backed SSD scan validation through the reusable DB profile boundary")
val throughput = make_db_ssd_materialized_scan_profile_throughput_row()
expect(throughput.name).to_equal("db_ssd_materialized_scan_profile_throughput_contract")
expect(throughput.dataset).to_equal("dbfs_ssd_materialized_scan_3x2x1024_row_match")
expect(throughput.row_count).to_equal(6)
expect(throughput.batch_size).to_equal(6)
expect(throughput.call_count).to_equal(3)
expect(throughput.batch_bytes).to_equal(3 * 2 * 1024)
expect(throughput.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(throughput.gpu_hits).to_equal(3)
expect(throughput.cpu_fallbacks).to_equal(0)
expect(throughput.error_count).to_equal(0)
expect(throughput.device_time_us).to_equal(111)
expect(throughput.device_timing_source).to_equal("cuda-event-contract")
expect(throughput.backend_timing_valid).to_be(true)
```

</details>

#### should report SSD materialized scan throughput with runtime queue timing

- Feed host GPU runtime queue timing into repeated DBFS-backed SSD scan validation
   - Expected: throughput.name equals `db_ssd_materialized_scan_runtime_queue_throughput_contract`
   - Expected: throughput.backend equals `native-device-probe`
   - Expected: throughput.dataset equals `dbfs_ssd_materialized_scan_2x2x1024_runtime_queue`
   - Expected: throughput.row_count equals `4`
   - Expected: throughput.batch_size equals `4`
   - Expected: throughput.call_count equals `2`
   - Expected: throughput.batch_bytes equals `2 * 2 * 1024`
   - Expected: throughput.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: throughput.gpu_hits equals `2`
   - Expected: throughput.cpu_fallbacks equals `0`
   - Expected: throughput.error_count equals `0`
   - Expected: throughput.device_timing_source equals `rt_host_gpu_queue_last_device_time_us`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Feed host GPU runtime queue timing into repeated DBFS-backed SSD scan validation")
val throughput = make_db_ssd_materialized_scan_runtime_queue_throughput_row()
expect(throughput.name).to_equal("db_ssd_materialized_scan_runtime_queue_throughput_contract")
expect(throughput.backend).to_equal("native-device-probe")
expect(throughput.dataset).to_equal("dbfs_ssd_materialized_scan_2x2x1024_runtime_queue")
expect(throughput.row_count).to_equal(4)
expect(throughput.batch_size).to_equal(4)
expect(throughput.call_count).to_equal(2)
expect(throughput.batch_bytes).to_equal(2 * 2 * 1024)
expect(throughput.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(throughput.gpu_hits).to_equal(2)
expect(throughput.cpu_fallbacks).to_equal(0)
expect(throughput.error_count).to_equal(0)
expect(throughput.device_time_us).to_be_greater_than(0)
expect(throughput.device_timing_source).to_equal("rt_host_gpu_queue_last_device_time_us")
expect(throughput.backend_timing_valid).to_be(true)
```

</details>

#### should report framework route inference validation with runtime queue timing

- Feed host GPU runtime queue timing into controller-facing web route validation
   - Expected: row.name equals `web_framework_inference_runtime_queue_validated_contract`
   - Expected: row.backend equals `native-device-probe`
   - Expected: row.dataset equals `web_framework_inference_16x512_runtime_queue_response_match`
   - Expected: row.document_count equals `16`
   - Expected: row.batch_size equals `16`
   - Expected: row.call_count equals `1`
   - Expected: row.batch_bytes equals `16 * 512`
   - Expected: row.dispatch_target equals `gpu_web_inference_batch`
   - Expected: row.gpu_hits equals `1`
   - Expected: row.cpu_fallbacks equals `0`
   - Expected: row.error_count equals `0`
   - Expected: row.device_timing_source equals `rt_host_gpu_queue_last_device_time_us`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Feed host GPU runtime queue timing into controller-facing web route validation")
val row = make_web_framework_runtime_queue_inference_row()
expect(row.name).to_equal("web_framework_inference_runtime_queue_validated_contract")
expect(row.backend).to_equal("native-device-probe")
expect(row.dataset).to_equal("web_framework_inference_16x512_runtime_queue_response_match")
expect(row.document_count).to_equal(16)
expect(row.batch_size).to_equal(16)
expect(row.call_count).to_equal(1)
expect(row.batch_bytes).to_equal(16 * 512)
expect(row.dispatch_target).to_equal("gpu_web_inference_batch")
expect(row.gpu_hits).to_equal(1)
expect(row.cpu_fallbacks).to_equal(0)
expect(row.error_count).to_equal(0)
expect(row.device_time_us).to_be_greater_than(0)
expect(row.device_timing_source).to_equal("rt_host_gpu_queue_last_device_time_us")
expect(row.backend_timing_valid).to_be(true)
```

</details>

#### should report combined production DB and web throughput with runtime queue timing

- Aggregate DBFS SSD scan and web framework inference runtime queue evidence into one production-facing row
   - Expected: row.name equals `production_db_web_runtime_queue_throughput_contract`
   - Expected: row.backend equals `native-device-probe`
   - Expected: row.dataset equals `dbfs_ssd_and_web_framework_runtime_queue_response_match`
   - Expected: row.row_count equals `4`
   - Expected: row.document_count equals `16`
   - Expected: row.batch_size equals `20`
   - Expected: row.call_count equals `3`
   - Expected: row.batch_bytes equals `(2 * 2 * 1024) + (16 * 512)`
   - Expected: row.dispatch_target equals `gpu_db_columnar_scan_batch+gpu_web_inference_batch`
   - Expected: row.gpu_hits equals `3`
   - Expected: row.cpu_fallbacks equals `0`
   - Expected: row.error_count equals `0`
   - Expected: row.device_timing_source equals `rt_host_gpu_queue_last_device_time_us`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Aggregate DBFS SSD scan and web framework inference runtime queue evidence into one production-facing row")
val row = make_production_db_web_runtime_queue_throughput_row()
expect(row.name).to_equal("production_db_web_runtime_queue_throughput_contract")
expect(row.backend).to_equal("native-device-probe")
expect(row.dataset).to_equal("dbfs_ssd_and_web_framework_runtime_queue_response_match")
expect(row.row_count).to_equal(4)
expect(row.document_count).to_equal(16)
expect(row.batch_size).to_equal(20)
expect(row.call_count).to_equal(3)
expect(row.batch_bytes).to_equal((2 * 2 * 1024) + (16 * 512))
expect(row.dispatch_target).to_equal("gpu_db_columnar_scan_batch+gpu_web_inference_batch")
expect(row.gpu_hits).to_equal(3)
expect(row.cpu_fallbacks).to_equal(0)
expect(row.error_count).to_equal(0)
expect(row.device_time_us).to_be_greater_than(0)
expect(row.device_timing_source).to_equal("rt_host_gpu_queue_last_device_time_us")
expect(row.backend_timing_valid).to_be(true)
```

</details>

#### should report DB batch admission policy before dispatch

- Admit coarse DB batches, fallback on full queues, and keep tiny document batches on CPU
- var full state = gpu wdb queue initial
   - Expected: admitted.action equals `dispatch-gpu`
   - Expected: admitted.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: admitted.batch_bytes equals `1024 * 64`
   - Expected: admitted.queue_depth_after equals `1`
   - Expected: full.action equals `run-cpu-fallback`
   - Expected: full.reason equals `gpu-queue-full`
   - Expected: tiny.action equals `run-cpu-fallback`
   - Expected: tiny.reason equals `batch-too-small`
   - Expected: row.name equals `db_batch_admission_policy_contract`
   - Expected: row.gpu_hits equals `1`
   - Expected: row.cpu_fallbacks equals `2`
   - Expected: row.error_count equals `0`
   - Expected: row.fallback_reason equals `queue-full+batch-too-small-covered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Admit coarse DB batches, fallback on full queues, and keep tiny document batches on CPU")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(4)
val admitted = gpu_wdb_db_batch_admission(
    state,
    GpuWdbWorkKind.DbScanFilterProject,
    1024,
    0,
    0,
    64,
    true,
    true,
    true,
    budget
)
var full_state = gpu_wdb_queue_initial(4)
full_state.queue_depth = budget.max_queue_depth
val full = gpu_wdb_db_batch_admission(
    full_state,
    GpuWdbWorkKind.DbJoinAggregate,
    1024,
    0,
    0,
    96,
    true,
    true,
    true,
    budget
)
val tiny = gpu_wdb_db_batch_admission(
    state,
    GpuWdbWorkKind.DbDocumentFilter,
    0,
    1,
    0,
    256,
    true,
    true,
    true,
    budget
)
val row = make_db_batch_admission_policy_row()
expect(admitted.accepted).to_be(true)
expect(admitted.action).to_equal("dispatch-gpu")
expect(admitted.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(admitted.batch_bytes).to_equal(1024 * 64)
expect(admitted.queue_depth_after).to_equal(1)
expect(full.accepted).to_be(false)
expect(full.action).to_equal("run-cpu-fallback")
expect(full.reason).to_equal("gpu-queue-full")
expect(tiny.accepted).to_be(false)
expect(tiny.action).to_equal("run-cpu-fallback")
expect(tiny.reason).to_equal("batch-too-small")
expect(row.name).to_equal("db_batch_admission_policy_contract")
expect(row.gpu_hits).to_equal(1)
expect(row.cpu_fallbacks).to_equal(2)
expect(row.error_count).to_equal(0)
expect(row.fallback_reason).to_equal("queue-full+batch-too-small-covered")
```

</details>

#### should report GPU transfer amortization policy before speedup claims

- Compare naive per-call transfer overhead with one coalesced batch transfer
   - Expected: policy.logical_call_count equals `4`
   - Expected: policy.item_count equals `32`
   - Expected: policy.payload_bytes equals `32 * 2048`
   - Expected: policy.naive_transfer_bytes equals `(32 * 2048) + (4 * 1024)`
   - Expected: policy.amortized_transfer_bytes equals `(32 * 2048) + 1024`
   - Expected: policy.saved_transfer_bytes equals `3 * 1024`
   - Expected: policy.bytes_per_logical_call equals `8 * 2048`
   - Expected: row.name equals `gpu_transfer_amortization_policy_contract`
   - Expected: row.backend equals `host-safe-transfer-policy`
   - Expected: row.dataset equals `gpu_transfer_amortization_4x8x2048_batch`
   - Expected: row.document_count equals `32`
   - Expected: row.call_count equals `4`
   - Expected: row.batch_bytes equals `32 * 2048`
   - Expected: row.transfer_bytes equals `(32 * 2048) + 1024`
   - Expected: row.gpu_hits equals `1`
   - Expected: row.cpu_fallbacks equals `0`
   - Expected: row.error_count equals `0`
   - Expected: row.fallback_reason equals `amortized-transfer-saved:3072`
   - Expected: row.device_timing_source equals `transfer-amortization-policy-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare naive per-call transfer overhead with one coalesced batch transfer")
val policy = gpu_wdb_transfer_amortization(4, 8, 2048, 1024, gpu_wdb_default_budget())
val row = make_gpu_transfer_amortization_policy_row()
expect(policy.accepted).to_be(true)
expect(policy.logical_call_count).to_equal(4)
expect(policy.item_count).to_equal(32)
expect(policy.payload_bytes).to_equal(32 * 2048)
expect(policy.naive_transfer_bytes).to_equal((32 * 2048) + (4 * 1024))
expect(policy.amortized_transfer_bytes).to_equal((32 * 2048) + 1024)
expect(policy.saved_transfer_bytes).to_equal(3 * 1024)
expect(policy.bytes_per_logical_call).to_equal(8 * 2048)
expect(row.name).to_equal("gpu_transfer_amortization_policy_contract")
expect(row.backend).to_equal("host-safe-transfer-policy")
expect(row.dataset).to_equal("gpu_transfer_amortization_4x8x2048_batch")
expect(row.document_count).to_equal(32)
expect(row.call_count).to_equal(4)
expect(row.batch_bytes).to_equal(32 * 2048)
expect(row.transfer_bytes).to_equal((32 * 2048) + 1024)
expect(row.gpu_hits).to_equal(1)
expect(row.cpu_fallbacks).to_equal(0)
expect(row.error_count).to_equal(0)
expect(row.fallback_reason).to_equal("amortized-transfer-saved:3072")
expect(row.device_timing_source).to_equal("transfer-amortization-policy-contract")
expect(row.backend_timing_valid).to_be(false)
```

</details>

#### should report external DB baseline status rows before DB speedup claims

- Record unavailable ClickHouse, DuckDB, PostgreSQL, MongoDB, and Redis/Valkey baseline tools as explicit report rows
   - Expected: clickhouse.name equals `db_clickbench_clickhouse_external_baseline_status`
   - Expected: clickhouse.backend equals `external-db-baseline`
   - Expected: clickhouse.dataset equals `clickbench_hits_scan_filter_project_1024_row_match`
   - Expected: clickhouse.dispatch_target equals `clickhouse_scan_filter_project`
   - Expected: clickhouse.fallback_reason equals `external-db-baseline-unavailable:clickhouse-not-installed`
   - Expected: clickhouse.device_timing_source equals `external-db-baseline-status`
   - Expected: clickhouse.gpu_hits equals `0`
   - Expected: duckdb.name equals `db_tpch_duckdb_external_baseline_status`
   - Expected: duckdb.dispatch_target equals `duckdb_tpch_q3_join_aggregate`
   - Expected: duckdb.fallback_reason equals `external-db-baseline-unavailable:duckdb-not-installed`
   - Expected: postgresql.name equals `db_tpch_postgresql_external_baseline_status`
   - Expected: postgresql.dispatch_target equals `postgresql_tpch_q3_join_aggregate`
   - Expected: postgresql.fallback_reason equals `external-db-baseline-unavailable:postgresql-not-installed`
   - Expected: mongo.name equals `db_ycsb_mongo_external_baseline_status`
   - Expected: mongo.dispatch_target equals `mongo_ycsb_document_filter`
   - Expected: mongo.fallback_reason equals `external-db-baseline-unavailable:mongo-not-installed`
   - Expected: redis_valkey.name equals `db_key_value_redis_valkey_external_baseline_status`
   - Expected: redis_valkey.dataset equals `redis_valkey_getset_1024_key_match`
   - Expected: redis_valkey.dispatch_target equals `redis_valkey_key_value_getset`
   - Expected: redis_valkey.fallback_reason equals `external-db-baseline-unavailable:redis-valkey-not-installed`
   - Expected: redis_valkey.device_timing_source equals `external-db-baseline-status`
   - Expected: redis_valkey.gpu_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record unavailable ClickHouse, DuckDB, PostgreSQL, MongoDB, and Redis/Valkey baseline tools as explicit report rows")
val clickhouse = make_clickhouse_clickbench_external_baseline_status_row()
val duckdb = make_duckdb_tpch_external_baseline_status_row()
val postgresql = make_postgresql_tpch_external_baseline_status_row()
val mongo = make_mongo_ycsb_external_baseline_status_row()
val redis_valkey = make_redis_valkey_external_baseline_status_row()
expect(clickhouse.name).to_equal("db_clickbench_clickhouse_external_baseline_status")
expect(clickhouse.backend).to_equal("external-db-baseline")
expect(clickhouse.dataset).to_equal("clickbench_hits_scan_filter_project_1024_row_match")
expect(clickhouse.dispatch_target).to_equal("clickhouse_scan_filter_project")
expect(clickhouse.fallback_reason).to_equal("external-db-baseline-unavailable:clickhouse-not-installed")
expect(clickhouse.device_timing_source).to_equal("external-db-baseline-status")
expect(clickhouse.backend_timing_valid).to_be(false)
expect(clickhouse.gpu_hits).to_equal(0)
expect(duckdb.name).to_equal("db_tpch_duckdb_external_baseline_status")
expect(duckdb.dispatch_target).to_equal("duckdb_tpch_q3_join_aggregate")
expect(duckdb.fallback_reason).to_equal("external-db-baseline-unavailable:duckdb-not-installed")
expect(postgresql.name).to_equal("db_tpch_postgresql_external_baseline_status")
expect(postgresql.dispatch_target).to_equal("postgresql_tpch_q3_join_aggregate")
expect(postgresql.fallback_reason).to_equal("external-db-baseline-unavailable:postgresql-not-installed")
expect(mongo.name).to_equal("db_ycsb_mongo_external_baseline_status")
expect(mongo.dispatch_target).to_equal("mongo_ycsb_document_filter")
expect(mongo.fallback_reason).to_equal("external-db-baseline-unavailable:mongo-not-installed")
expect(redis_valkey.name).to_equal("db_key_value_redis_valkey_external_baseline_status")
expect(redis_valkey.dataset).to_equal("redis_valkey_getset_1024_key_match")
expect(redis_valkey.dispatch_target).to_equal("redis_valkey_key_value_getset")
expect(redis_valkey.fallback_reason).to_equal("external-db-baseline-unavailable:redis-valkey-not-installed")
expect(redis_valkey.device_timing_source).to_equal("external-db-baseline-status")
expect(redis_valkey.backend_timing_valid).to_be(false)
expect(redis_valkey.gpu_hits).to_equal(0)
```

</details>

#### should mark installed external DB baselines ready but unmeasured

- Convert available DB tools into ready-unmeasured rows without inventing throughput
   - Expected: clickhouse.backend equals `external-db-baseline`
   - Expected: clickhouse.fallback_reason equals `external-db-baseline-ready-unmeasured:clickhouse_scan_filter_project`
   - Expected: clickhouse.gpu_hits equals `0`
   - Expected: clickhouse.cpu_fallbacks equals `0`
   - Expected: clickhouse.device_time_us equals `0`
   - Expected: duckdb.fallback_reason equals `external-db-baseline-ready-unmeasured:duckdb_tpch_q3_join_aggregate`
   - Expected: duckdb.batch_size equals `0`
   - Expected: duckdb.call_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert available DB tools into ready-unmeasured rows without inventing throughput")
val clickhouse = make_external_db_baseline_status_row(
    "db_clickbench_clickhouse_external_baseline_status",
    "clickbench_hits_scan_filter_project_1024_row_match",
    "clickhouse_scan_filter_project",
    true,
    "external-db-baseline-unavailable:clickhouse-not-installed"
)
val duckdb = make_external_db_baseline_status_row(
    "db_tpch_duckdb_external_baseline_status",
    "tpch_q3_join_aggregate_group_count_1024_row_match",
    "duckdb_tpch_q3_join_aggregate",
    true,
    "external-db-baseline-unavailable:duckdb-not-installed"
)
expect(clickhouse.backend).to_equal("external-db-baseline")
expect(clickhouse.fallback_reason).to_equal("external-db-baseline-ready-unmeasured:clickhouse_scan_filter_project")
expect(clickhouse.gpu_hits).to_equal(0)
expect(clickhouse.cpu_fallbacks).to_equal(0)
expect(clickhouse.device_time_us).to_equal(0)
expect(clickhouse.backend_timing_valid).to_be(false)
expect(duckdb.fallback_reason).to_equal("external-db-baseline-ready-unmeasured:duckdb_tpch_q3_join_aggregate")
expect(duckdb.batch_size).to_equal(0)
expect(duckdb.call_count).to_equal(0)
```

</details>

#### should report standard-shape DB benchmark rows before external DB baselines are installed

- Map DB offload targets to ClickBench, TPC-H, BenchBase/YCSB, and ANN-style benchmark shapes
   - Expected: clickbench.name equals `db_clickbench_olap_scan_shape_contract`
   - Expected: clickbench.dataset equals `clickbench_hits_scan_filter_project_1024_row_match`
   - Expected: clickbench.dispatch_target equals `gpu_db_columnar_scan_batch`
   - Expected: clickbench.row_count equals `1024`
   - Expected: clickbench.cpu_fallbacks equals `1`
   - Expected: clickbench.fallback_reason equals `standard-baseline-unavailable:clickhouse-duckdb-postgresql`
   - Expected: clickbench.device_timing_source equals `standard-shape-contract`
   - Expected: tpch.name equals `db_tpch_join_aggregate_shape_contract`
   - Expected: tpch.dataset equals `tpch_q3_join_aggregate_group_count_1024_row_match`
   - Expected: tpch.dispatch_target equals `gpu_db_join_aggregate_batch`
   - Expected: tpch.row_count equals `1024`
   - Expected: tpch.fallback_reason equals `standard-baseline-unavailable:tpch-duckdb-postgresql`
   - Expected: ycsb.name equals `db_benchbase_ycsb_document_shape_contract`
   - Expected: ycsb.dataset equals `benchbase_ycsb_document_filter_1024_doc_match`
   - Expected: ycsb.dispatch_target equals `gpu_db_document_filter_batch`
   - Expected: ycsb.document_count equals `1024`
   - Expected: ycsb.fallback_reason equals `standard-baseline-unavailable:benchbase-ycsb-mongo`
   - Expected: ann.name equals `db_ann_vector_search_shape_contract`
   - Expected: ann.dataset equals `ann_vector_topk_1024x128_recall_id_match`
   - Expected: ann.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: ann.vector_dimensions equals `128`
   - Expected: ann.fallback_reason equals `standard-baseline-unavailable:ann-fixture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Map DB offload targets to ClickBench, TPC-H, BenchBase/YCSB, and ANN-style benchmark shapes")
val clickbench = make_clickbench_olap_scan_shape_row()
val tpch = make_tpch_join_aggregate_shape_row()
val ycsb = make_benchbase_ycsb_document_shape_row()
val ann = make_ann_vector_search_shape_row()
expect(clickbench.name).to_equal("db_clickbench_olap_scan_shape_contract")
expect(clickbench.dataset).to_equal("clickbench_hits_scan_filter_project_1024_row_match")
expect(clickbench.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
expect(clickbench.row_count).to_equal(1024)
expect(clickbench.cpu_fallbacks).to_equal(1)
expect(clickbench.fallback_reason).to_equal("standard-baseline-unavailable:clickhouse-duckdb-postgresql")
expect(clickbench.device_timing_source).to_equal("standard-shape-contract")
expect(clickbench.backend_timing_valid).to_be(false)
expect(tpch.name).to_equal("db_tpch_join_aggregate_shape_contract")
expect(tpch.dataset).to_equal("tpch_q3_join_aggregate_group_count_1024_row_match")
expect(tpch.dispatch_target).to_equal("gpu_db_join_aggregate_batch")
expect(tpch.row_count).to_equal(1024)
expect(tpch.fallback_reason).to_equal("standard-baseline-unavailable:tpch-duckdb-postgresql")
expect(ycsb.name).to_equal("db_benchbase_ycsb_document_shape_contract")
expect(ycsb.dataset).to_equal("benchbase_ycsb_document_filter_1024_doc_match")
expect(ycsb.dispatch_target).to_equal("gpu_db_document_filter_batch")
expect(ycsb.document_count).to_equal(1024)
expect(ycsb.fallback_reason).to_equal("standard-baseline-unavailable:benchbase-ycsb-mongo")
expect(ann.name).to_equal("db_ann_vector_search_shape_contract")
expect(ann.dataset).to_equal("ann_vector_topk_1024x128_recall_id_match")
expect(ann.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(ann.vector_dimensions).to_equal(128)
expect(ann.fallback_reason).to_equal("standard-baseline-unavailable:ann-fixture")
```

</details>

#### should carry native backend device timing provenance when supplied

- Create a vector metrics row with runtime queue device timing
- rt host gpu queue reset
   - Expected: rt_host_gpu_queue_emit(2, 1, budget.min_gpu_batch_bytes * 8, 7) equals `1`
   - Expected: rt_host_gpu_queue_submit(1) equals `1`
   - Expected: rt_host_gpu_queue_complete(1) equals `1`
   - Expected: row.name equals `db_vector_native_timing_probe`
   - Expected: row.backend equals `native-device-probe`
   - Expected: row.dispatch_target equals `gpu_db_vector_search_batch`
   - Expected: row.gpu_hits equals `1`
   - Expected: row.cpu_fallbacks equals `0`
   - Expected: row.kernel_time_us equals `runtime_device_time`
   - Expected: row.device_time_us equals `runtime_device_time`
   - Expected: row.device_timing_source equals `rt_host_gpu_queue_last_device_time_us`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a vector metrics row with runtime queue device timing")
val budget = gpu_wdb_default_budget()
val state = gpu_wdb_queue_initial(4)
val registry = gpu_wdb_library_with_targets("native-device-probe", 2, ["gpu_db_vector_search_batch"])
rt_host_gpu_queue_reset()
val started = rt_time_now_unix_micros()
expect(rt_host_gpu_queue_emit(2, 1, budget.min_gpu_batch_bytes * 8, 7)).to_equal(1)
expect(rt_host_gpu_queue_submit(1)).to_equal(1)
expect(rt_host_gpu_queue_complete(1)).to_equal(1)
val runtime_device_time = rt_host_gpu_queue_last_device_time_us()
val submission = gpu_wdb_submit_registered_batch(
    state,
    registry,
    GpuWdbWorkKind.DbVectorSearch,
    budget.min_gpu_batch_bytes * 8,
    8,
    true,
    true,
    true,
    budget
)
val finished = started + 100
val row = native_timed_bench_row_from_submission(
    "db_vector_native_timing_probe",
    registry.backend,
    "oracle_vectors_1024x128",
    1024,
    0,
    128,
    8,
    submission,
    started,
    finished,
    runtime_device_time,
    "rt_host_gpu_queue_last_device_time_us"
)
expect(row.name).to_equal("db_vector_native_timing_probe")
expect(row.backend).to_equal("native-device-probe")
expect(row.dispatch_target).to_equal("gpu_db_vector_search_batch")
expect(row.gpu_hits).to_equal(1)
expect(row.cpu_fallbacks).to_equal(0)
expect(runtime_device_time).to_be_greater_than(0)
expect(row.kernel_time_us).to_equal(runtime_device_time)
expect(row.device_time_us).to_equal(runtime_device_time)
expect(row.device_timing_source).to_equal("rt_host_gpu_queue_last_device_time_us")
expect(row.backend_timing_valid).to_be(true)
```

</details>

#### should accept measured CUDA benchmark rows only for validated GPU DB targets

- Validate measured CUDA row shape before the benchmark report may claim native device execution
   - Expected: vector_status equals `measured`
   - Expected: columnar_status equals `measured`
   - Expected: join_aggregate_status equals `measured`
   - Expected: ssd_materialized_status equals `measured`
   - Expected: ssd_materialized_throughput_status equals `measured`
   - Expected: ssd_materialized_runtime_queue_status equals `measured`
   - Expected: framework_runtime_queue_status equals `measured`
   - Expected: production_db_web_runtime_queue_status equals `measured`
   - Expected: join_aggregate_wrong_dataset_status equals `invalid_measured`
   - Expected: document_filter_status equals `measured`
   - Expected: document_filter_wrong_target_status equals `invalid_measured`
   - Expected: web_inference_status equals `measured`
   - Expected: web_inference_wrong_target_status equals `invalid_measured`
   - Expected: web_embedding_status equals `measured`
   - Expected: web_embedding_wrong_target_status equals `invalid_measured`
   - Expected: web_rank_status equals `measured`
   - Expected: web_rank_wrong_dataset_status equals `invalid_measured`
   - Expected: web_transform_status equals `measured`
   - Expected: web_transform_wrong_dataset_status equals `invalid_measured`
   - Expected: columnar_reused_vector_status equals `invalid_measured`
   - Expected: fallback_status equals `invalid_measured`
   - Expected: zero_status equals `invalid_measured`
   - Expected: clickhouse_external_status equals `measured`
   - Expected: duckdb_external_status equals `measured`
   - Expected: postgresql_external_status equals `measured`
   - Expected: mongo_external_status equals `measured`
   - Expected: redis_valkey_external_status equals `measured`
   - Expected: external_wrong_source_status equals `invalid_measured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 253 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate measured CUDA row shape before the benchmark report may claim native device execution")
val vector_status = gpu_wdb_benchmark_measured_row_status(
    "db_vector_cuda_measured",
    "oracle_vectors_1024x128",
    "gpu_db_vector_search_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val columnar_status = gpu_wdb_benchmark_measured_row_status(
    "db_columnar_scan_cuda_measured",
    "pure_sql_scan_filter_project",
    "gpu_db_columnar_scan_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val join_aggregate_status = gpu_wdb_benchmark_measured_row_status(
    "db_join_aggregate_cuda_measured",
    "pure_sql_join_aggregate_group_count",
    "gpu_db_join_aggregate_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val ssd_materialized_status = gpu_wdb_benchmark_measured_row_status(
    "db_ssd_materialized_scan_device_validated_contract",
    "dbfs_ssd_materialized_scan_2x1024_row_match",
    "gpu_db_columnar_scan_batch",
    37,
    "cuda-event-contract",
    "production-device-validated-contract"
)
val ssd_materialized_throughput_status = gpu_wdb_benchmark_measured_row_status(
    "db_ssd_materialized_scan_profile_throughput_contract",
    "dbfs_ssd_materialized_scan_3x2x1024_row_match",
    "gpu_db_columnar_scan_batch",
    111,
    "cuda-event-contract",
    "production-device-validated-throughput-contract"
)
val ssd_materialized_runtime_queue_status = gpu_wdb_benchmark_measured_row_status(
    "db_ssd_materialized_scan_runtime_queue_throughput_contract",
    "dbfs_ssd_materialized_scan_2x2x1024_runtime_queue",
    "gpu_db_columnar_scan_batch",
    1,
    "rt_host_gpu_queue_last_device_time_us",
    "runtime-queue-measured-throughput-contract"
)
val framework_runtime_queue_status = gpu_wdb_benchmark_measured_row_status(
    "web_framework_inference_runtime_queue_validated_contract",
    "web_framework_inference_16x512_runtime_queue_response_match",
    "gpu_web_inference_batch",
    1,
    "rt_host_gpu_queue_last_device_time_us",
    "runtime-queue-measured-framework-contract"
)
val production_db_web_runtime_queue_status = gpu_wdb_benchmark_measured_row_status(
    "production_db_web_runtime_queue_throughput_contract",
    "dbfs_ssd_and_web_framework_runtime_queue_response_match",
    "gpu_db_columnar_scan_batch+gpu_web_inference_batch",
    1,
    "rt_host_gpu_queue_last_device_time_us",
    "runtime-queue-production-db-web-throughput-contract"
)
val join_aggregate_wrong_dataset_status = gpu_wdb_benchmark_measured_row_status(
    "db_join_aggregate_cuda_measured",
    "pure_sql_scan_filter_project",
    "gpu_db_join_aggregate_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val document_filter_status = gpu_wdb_benchmark_measured_row_status(
    "db_document_filter_cuda_measured",
    "nosql_document_filter_metadata",
    "gpu_db_document_filter_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val document_filter_wrong_target_status = gpu_wdb_benchmark_measured_row_status(
    "db_document_filter_cuda_measured",
    "nosql_document_filter_metadata",
    "gpu_db_join_aggregate_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val web_inference_status = gpu_wdb_benchmark_measured_row_status(
    "web_inference_cuda_measured",
    "web_inference_16x512_response_match",
    "gpu_web_inference_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val web_inference_wrong_target_status = gpu_wdb_benchmark_measured_row_status(
    "web_inference_cuda_measured",
    "web_inference_16x512_response_match",
    "gpu_db_document_filter_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val web_embedding_status = gpu_wdb_benchmark_measured_row_status(
    "web_embedding_cuda_measured",
    "web_embedding_16x512_response_match",
    "gpu_web_embedding_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val web_embedding_wrong_target_status = gpu_wdb_benchmark_measured_row_status(
    "web_embedding_cuda_measured",
    "web_embedding_16x512_response_match",
    "gpu_web_rank_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val web_rank_status = gpu_wdb_benchmark_measured_row_status(
    "web_rank_cuda_measured",
    "web_rank_32x256_response_match",
    "gpu_web_rank_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val web_rank_wrong_dataset_status = gpu_wdb_benchmark_measured_row_status(
    "web_rank_cuda_measured",
    "web_embedding_16x512_response_match",
    "gpu_web_rank_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val web_transform_status = gpu_wdb_benchmark_measured_row_status(
    "web_transform_cuda_measured",
    "web_transform_8x2048_response_match",
    "gpu_web_transform_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val web_transform_wrong_dataset_status = gpu_wdb_benchmark_measured_row_status(
    "web_transform_cuda_measured",
    "web_inference_16x512_response_match",
    "gpu_web_transform_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val columnar_reused_vector_status = gpu_wdb_benchmark_measured_row_status(
    "db_columnar_scan_cuda_measured",
    "oracle_vectors_1024x128",
    "gpu_db_columnar_scan_batch",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val fallback_status = gpu_wdb_benchmark_measured_row_status(
    "db_vector_cuda_measured",
    "oracle_vectors_1024x128",
    "cpu_fallback",
    176,
    "cuda-measured-driver",
    "native-device-measured"
)
val zero_status = gpu_wdb_benchmark_measured_row_status(
    "db_vector_cuda_measured",
    "oracle_vectors_1024x128",
    "gpu_db_vector_search_batch",
    0,
    "cuda-measured-driver",
    "native-device-measured"
)
val clickhouse_external_status = gpu_wdb_benchmark_measured_row_status(
    "db_clickbench_clickhouse_external_measured",
    "clickbench_hits_scan_filter_project_1024_row_match",
    "clickhouse_scan_filter_project",
    901,
    "external-db-baseline-driver",
    "external-db-baseline-measured"
)
val duckdb_external_status = gpu_wdb_benchmark_measured_row_status(
    "db_tpch_duckdb_external_measured",
    "tpch_q3_join_aggregate_group_count_1024_row_match",
    "duckdb_tpch_q3_join_aggregate",
    902,
    "external-db-baseline-driver",
    "external-db-baseline-measured"
)
val postgresql_external_status = gpu_wdb_benchmark_measured_row_status(
    "db_tpch_postgresql_external_measured",
    "tpch_q3_join_aggregate_group_count_1024_row_match",
    "postgresql_tpch_q3_join_aggregate",
    903,
    "external-db-baseline-driver",
    "external-db-baseline-measured"
)
val mongo_external_status = gpu_wdb_benchmark_measured_row_status(
    "db_ycsb_mongo_external_measured",
    "benchbase_ycsb_document_filter_1024_doc_match",
    "mongo_ycsb_document_filter",
    904,
    "external-db-baseline-driver",
    "external-db-baseline-measured"
)
val redis_valkey_external_status = gpu_wdb_benchmark_measured_row_status(
    "db_key_value_redis_valkey_external_measured",
    "redis_valkey_getset_1024_key_match",
    "redis_valkey_key_value_getset",
    905,
    "external-db-baseline-driver",
    "external-db-baseline-measured"
)
val external_wrong_source_status = gpu_wdb_benchmark_measured_row_status(
    "db_tpch_duckdb_external_measured",
    "tpch_q3_join_aggregate_group_count_1024_row_match",
    "duckdb_tpch_q3_join_aggregate",
    902,
    "cuda-measured-driver",
    "external-db-baseline-measured"
)
expect(vector_status).to_equal("measured")
expect(columnar_status).to_equal("measured")
expect(join_aggregate_status).to_equal("measured")
expect(ssd_materialized_status).to_equal("measured")
expect(ssd_materialized_throughput_status).to_equal("measured")
expect(ssd_materialized_runtime_queue_status).to_equal("measured")
expect(framework_runtime_queue_status).to_equal("measured")
expect(production_db_web_runtime_queue_status).to_equal("measured")
expect(join_aggregate_wrong_dataset_status).to_equal("invalid_measured")
expect(document_filter_status).to_equal("measured")
expect(document_filter_wrong_target_status).to_equal("invalid_measured")
expect(web_inference_status).to_equal("measured")
expect(web_inference_wrong_target_status).to_equal("invalid_measured")
expect(web_embedding_status).to_equal("measured")
expect(web_embedding_wrong_target_status).to_equal("invalid_measured")
expect(web_rank_status).to_equal("measured")
expect(web_rank_wrong_dataset_status).to_equal("invalid_measured")
expect(web_transform_status).to_equal("measured")
expect(web_transform_wrong_dataset_status).to_equal("invalid_measured")
expect(columnar_reused_vector_status).to_equal("invalid_measured")
expect(fallback_status).to_equal("invalid_measured")
expect(zero_status).to_equal("invalid_measured")
expect(clickhouse_external_status).to_equal("measured")
expect(duckdb_external_status).to_equal("measured")
expect(postgresql_external_status).to_equal("measured")
expect(mongo_external_status).to_equal("measured")
expect(redis_valkey_external_status).to_equal("measured")
expect(external_wrong_source_status).to_equal("invalid_measured")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/gpu_web_db_offload.md](doc/02_requirements/nfr/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)
- **Research:** [doc/01_research/local/gpu_web_db_offload.md](doc/01_research/local/gpu_web_db_offload.md)


</details>
