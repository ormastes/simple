# processing_ir_offload_break_even_spec

> Purpose: consume (and, when absent, produce with the native gate) a real CUDA

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_ir_offload_break_even_spec

Purpose: consume (and, when absent, produce with the native gate) a real CUDA

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: consume (and, when absent, produce with the native gate) a real CUDA
ProcessingIR offload break-even receipt, then hold every measured row to the
policy contract: exact device readback, coherent timing decomposition, and a
CPU decision for every batch where the GPU round trip is slower.
Audience: simpleos_gpu_host maintainers and GPU offload policy owners.

## Scenarios

### ProcessingIR GPU offload break-even evidence

#### keeps the offload receipt validator honest

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- keeps the offload receipt validator honest
   - Expected: file_exists(OFFLOAD_CHECK) is true
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the offload receipt validator honest")
expect(file_exists(OFFLOAD_CHECK)).to_equal(true)
val (_stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["-c", "sh " + OFFLOAD_CHECK + " --self-test"]
)
expect(code).to_equal(0)  # oracle: self-test must exit green
```

</details>

#### requires measured rows and rejects slower GPU offload below break-even

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- produces the native receipt on demand, then checks every measured row
- receipt missing; producing it with the native CUDA gate
   - Expected: produce_code equals `0`
   - Expected: file_exists(path) is true
   - Expected: validator_code equals `0`
   - Expected: value_of(receipt, "processing_ir_offload_status") equals `pass`
   - Expected: value_of(receipt, "processing_ir_offload_schema") equals `processing-ir-offload-v1`
   - Expected: value_of(receipt, "processing_ir_offload_execution") equals `processing_ir`
   - Expected: backend == "cuda" or backend == "vulkan" or backend == "cuda+vulkan" is true
   - Expected: value_of(receipt, "processing_ir_offload_evidence_kind") equals `live`
   - Expected: value_of(receipt, "processing_ir_offload_aggregate") equals `median`
   - Expected: value_of(receipt, "processing_ir_offload_timing_unit") equals `us`
   - Expected: value_of(receipt, "processing_ir_offload_rss_source") equals `procfs`
   - Expected: cpu_workload equals `gpu_workload`
   - Expected: cpu_workload == "alpha_u32_v1" or output_only is true
   - Expected: value_of(receipt, "processing_ir_offload_workload_kind") equals `output_only`
   - Expected: value_of(receipt, "processing_ir_offload_break_even_found") equals `false`
   - Expected: value_of(receipt, "processing_ir_offload_executor_timing") equals `allocation_us+launch_sync_us+readback_us+conversion_cleanup_us`
   - Expected: value_of(receipt, "processing_ir_offload_device_uuid").len() equals `32`
   - Expected: value_of(receipt, "processing_ir_offload_source_sha256").len() equals `64`
   - Expected: value_of(receipt, "processing_ir_offload_artifact_sha256").len() equals `64`
   - Expected: value_of(receipt, "processing_ir_offload_raw_samples_sha256").len() equals `64`
   - Expected: value_of(receipt, "processing_ir_offload_provenance_manifest_sha256").len() equals `64`
   - Expected: workload equals `cpu_workload`
   - Expected: transfer equals `upload + readback`
   - Expected: readback_source equals `device_readback`
   - Expected: readback_exact equals `true`
   - Expected: mismatch_count equals `0`
   - Expected: upload equals `0`
   - Expected: upload_bytes equals `0`
   - Expected: submission_mode equals `output_only`
   - Expected: row_number(receipt, i, "executor_total_us") equals `total`
   - Expected: submission_mode == "batched" or submission_mode == "per_command" is true
   - Expected: submission_mode == previous_mode is false
   - Expected: decision equals `cpu`
   - Expected: output_only is false
   - Expected: decision equals `gpu`
   - Expected: slower_rows equals `rows`
   - Expected: faster_rows equals `0`
   - Expected: measured_break_even equals `0`
   - Expected: number_of(receipt, "processing_ir_offload_coverage_max_batch") equals `row_number(receipt, rows - 1, "batch")`
   - Expected: measured_break_even equals `first_fast_batch`
   - Expected: varied_transfer_size is true
   - Expected: varied_command_count is true
   - Expected: saw_batched is true
   - Expected: saw_per_command is true
   - Expected: total >= cpu is true
   - Expected: row_text(receipt, i, "decision") equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 183 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces the native receipt on demand, then checks every measured row")
val path = receipt_path()
if not file_exists(path):
    # Evidence consumer: no fabricated fallback — produce the real
    # receipt with the native gate, and fail if production fails.
    step("receipt missing; producing it with the native CUDA gate")
    val (_out, _err, produce_code) = process_run("/bin/sh", [OFFLOAD_CHECK])
    expect(produce_code).to_equal(0)  # oracle: gate exit 0 == receipt produced and validated
    expect(file_exists(path)).to_equal(true)  # oracle: receipt must exist after production
    if not file_exists(path):
        return
val (_validator_out, _validator_err, validator_code) = process_run(
    "/bin/sh",
    [OFFLOAD_CHECK, "--validate", path]
)
expect(validator_code).to_equal(0)  # oracle: receipt must pass the native validator
val receipt = file_read(path)

expect(value_of(receipt, "processing_ir_offload_status")).to_equal("pass")
expect(value_of(receipt, "processing_ir_offload_schema")).to_equal("processing-ir-offload-v1")
expect(value_of(receipt, "processing_ir_offload_execution")).to_equal("processing_ir")
val backend = value_of(receipt, "processing_ir_offload_backend")
expect(backend == "cuda" or backend == "vulkan" or backend == "cuda+vulkan").to_equal(true)
expect(value_of(receipt, "processing_ir_offload_evidence_kind")).to_equal("live")
expect(value_of(receipt, "processing_ir_offload_aggregate")).to_equal("median")
expect(value_of(receipt, "processing_ir_offload_timing_unit")).to_equal("us")
expect(value_of(receipt, "processing_ir_offload_rss_source")).to_equal("procfs")

val cpu_workload = value_of(receipt, "processing_ir_offload_cpu_workload_id")
val gpu_workload = value_of(receipt, "processing_ir_offload_gpu_workload_id")
expect(cpu_workload.len()).to_be_greater_than(0)
expect(cpu_workload).to_equal(gpu_workload)
val output_only = cpu_workload == "fill_u32_v1"
expect(cpu_workload == "alpha_u32_v1" or output_only).to_equal(true)
if output_only:
    expect(value_of(receipt, "processing_ir_offload_workload_kind")).to_equal("output_only")
    expect(value_of(receipt, "processing_ir_offload_break_even_found")).to_equal("false")
    expect(value_of(receipt, "processing_ir_offload_executor_timing")).to_equal("allocation_us+launch_sync_us+readback_us+conversion_cleanup_us")
    expect(value_of(receipt, "processing_ir_offload_device_name").len()).to_be_greater_than(0)
    expect(value_of(receipt, "processing_ir_offload_device_uuid").len()).to_equal(32)  # oracle: UUID is 32 hex chars
    expect(number_of(receipt, "processing_ir_offload_device_identity")).to_be_greater_than(0)  # oracle: at least one identity token
    expect(value_of(receipt, "processing_ir_offload_source_sha256").len()).to_equal(64)  # oracle: sha256 hex digest length
    expect(value_of(receipt, "processing_ir_offload_artifact_sha256").len()).to_equal(64)  # oracle: sha256 hex digest length
    expect(value_of(receipt, "processing_ir_offload_raw_samples_sha256").len()).to_equal(64)  # oracle: sha256 hex digest length
    expect(value_of(receipt, "processing_ir_offload_provenance_manifest_path").len()).to_be_greater_than(0)
    expect(value_of(receipt, "processing_ir_offload_provenance_manifest_sha256").len()).to_equal(64)  # oracle: sha256 hex digest length
    expect(number_of(receipt, "processing_ir_offload_coverage_max_batch")).to_be_greater_than(1048575)  # oracle: coverage reaches the 1 Mi-element batch (2^20)

val warmup = number_of(receipt, "processing_ir_offload_warmup_samples")
val samples = number_of(receipt, "processing_ir_offload_measured_samples")
val rows = number_of(receipt, "processing_ir_offload_row_count")
expect(warmup).to_be_greater_than(2)  # oracle: warmup drops at least the first samples
expect(samples).to_be_greater_than(4)  # oracle: median needs more than four measured samples
if output_only:
    expect(rows).to_be_greater_than(2)  # oracle: monotone search needs three or more batch rows
else:
    expect(rows).to_be_greater_than(3)  # oracle: break-even search needs four or more batch rows

val cpu_rss = number_of(receipt, "processing_ir_offload_cpu_rss_kb")
val gpu_rss = number_of(receipt, "processing_ir_offload_gpu_rss_kb")
val peak_rss = number_of(receipt, "processing_ir_offload_peak_rss_kb")
val communication = number_of(receipt, "processing_ir_offload_communication_overhead_us")
expect(cpu_rss).to_be_greater_than(0)  # oracle: a real process has non-zero RSS
expect(gpu_rss).to_be_greater_than(0)  # oracle: a real process has non-zero RSS
expect(peak_rss).to_be_greater_than(0)  # oracle: a real process has non-zero RSS
expect(communication).to_be_greater_than(-1)  # oracle: overhead key resolves to a real number (sentinel -1 rejected)

var previous_batch: i64 = -1
var first_fast_batch: i64 = -1
var slower_rows: i64 = 0
var faster_rows: i64 = 0
var first_transfer_bytes: i64 = -1
var first_command_count: i64 = -1
var varied_transfer_size = false
var varied_command_count = false
var saw_batched = false
var saw_per_command = false
var previous_mode = ""
var i: i64 = 0
while i < rows:
    val batch = row_number(receipt, i, "batch")
    val workload = row_text(receipt, i, "workload_id")
    val cpu = row_number(receipt, i, "cpu_us")
    val upload = row_number(receipt, i, "upload_us")
    val device = row_number(receipt, i, "device_us")
    val readback = row_number(receipt, i, "readback_us")
    val transfer = row_number(receipt, i, "transfer_us")
    val total = row_number(receipt, i, "total_us")
    val upload_bytes = row_number(receipt, i, "upload_bytes")
    val readback_bytes = row_number(receipt, i, "readback_bytes")
    val command_count = row_number(receipt, i, "command_count")
    val decision = row_text(receipt, i, "decision")
    val submission_mode = row_text(receipt, i, "submission_mode")
    val readback_source = row_text(receipt, i, "readback_source")
    val readback_exact = row_text(receipt, i, "readback_exact")
    val mismatch_count = row_number(receipt, i, "readback_mismatch_count")

    expect(workload).to_equal(cpu_workload)
    expect(cpu).to_be_greater_than(0)
    expect(device).to_be_greater_than(0)
    expect(readback).to_be_greater_than(0)
    expect(transfer).to_be_greater_than(0)
    expect(total).to_be_greater_than(0)
    expect(readback_bytes).to_be_greater_than(0)
    expect(command_count).to_be_greater_than(0)
    expect(transfer).to_equal(upload + readback)
    expect(readback_source).to_equal("device_readback")
    expect(readback_exact).to_equal("true")
    expect(mismatch_count).to_equal(0)  # oracle: device readback is byte-exact
    if output_only:
        expect(upload).to_equal(0)  # oracle: output-only workloads upload nothing
        expect(upload_bytes).to_equal(0)  # oracle: output-only workloads upload nothing
        expect(submission_mode).to_equal("output_only")
        expect(row_number(receipt, i, "executor_allocation_us")).to_be_greater_than(0)
        expect(row_number(receipt, i, "executor_launch_sync_us")).to_be_greater_than(0)
        expect(row_number(receipt, i, "executor_conversion_cleanup_us")).to_be_greater_than(0)
        expect(row_number(receipt, i, "executor_total_us")).to_equal(total)
    else:
        expect(upload).to_be_greater_than(0)
        expect(upload_bytes).to_be_greater_than(0)
        expect(submission_mode == "batched" or submission_mode == "per_command").to_equal(true)
    if not output_only and batch == previous_batch:
        expect(submission_mode == previous_mode).to_equal(false)
    else:
        expect(batch).to_be_greater_than(previous_batch)

    if not output_only and first_transfer_bytes < 0:
        first_transfer_bytes = upload_bytes + readback_bytes
    elif not output_only and first_transfer_bytes != upload_bytes + readback_bytes:
        varied_transfer_size = true
    if not output_only and first_command_count < 0:
        first_command_count = command_count
    elif not output_only and first_command_count != command_count:
        varied_command_count = true
    if not output_only and submission_mode == "batched":
        saw_batched = true
    elif not output_only:
        saw_per_command = true

    if total >= cpu:
        slower_rows = slower_rows + 1
        expect(decision).to_equal("cpu")
    else:
        expect(output_only).to_equal(false)
        faster_rows = faster_rows + 1
        if first_fast_batch < 0:
            first_fast_batch = batch
        expect(decision).to_equal("gpu")
    previous_batch = batch
    previous_mode = submission_mode
    i = i + 1

val measured_break_even = number_of(receipt, "processing_ir_offload_break_even_batch")
if output_only:
    expect(slower_rows).to_equal(rows)
    expect(faster_rows).to_equal(0)  # oracle: output-only never beats the CPU baseline
    expect(measured_break_even).to_equal(0)  # oracle: output-only has no break-even batch
    expect(number_of(receipt, "processing_ir_offload_coverage_max_batch")).to_equal(row_number(receipt, rows - 1, "batch"))
else:
    expect(slower_rows).to_be_greater_than(0)
    expect(faster_rows).to_be_greater_than(0)
    expect(measured_break_even).to_equal(first_fast_batch)
    expect(varied_transfer_size).to_equal(true)
    expect(varied_command_count).to_equal(true)
    expect(saw_batched).to_equal(true)
    expect(saw_per_command).to_equal(true)

# A policy must never choose GPU for a measured round-trip that is
# slower than its CPU baseline; total_us includes every measured phase.
if not output_only:
    var below_threshold: i64 = 0
    i = 0
    while i < rows:
        val batch = row_number(receipt, i, "batch")
        val total = row_number(receipt, i, "total_us")
        val cpu = row_number(receipt, i, "cpu_us")
        if batch < measured_break_even:
            below_threshold = below_threshold + 1
            expect(total >= cpu).to_equal(true)
            expect(row_text(receipt, i, "decision")).to_equal("cpu")
        i = i + 1
    expect(below_threshold).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3dc3b3fc3d47a8c2aabb3de86551b96e8d2763f1c476981e0018221a788e9f26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3dc3b3fc3d47a8c2aabb3de86551b96e8d2763f1c476981e0018221a788e9f26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3dc3b3fc3d47a8c2aabb3de86551b96e8d2763f1c476981e0018221a788e9f26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
