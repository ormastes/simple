# Processing Ir Offload Break Even Specification

> Tests covering ProcessingIR GPU offload break-even evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Ir Offload Break Even Specification

## Scenarios

### ProcessingIR GPU offload break-even evidence

#### requires a Linux CUDA/Vulkan measurement host

- requires a Linux CUDA/Vulkan measurement host


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires a Linux CUDA/Vulkan measurement host")
pending("Linux ProcessingIR offload measurement is postponed to the Linux host")
```

</details>

#### keeps the offload receipt validator honest

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
expect(code).to_equal(0)
```

</details>

#### requires measured rows and rejects slower GPU offload below break-even

- requires measured rows and rejects slower GPU offload below break-even
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

Runnable source: 177 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires measured rows and rejects slower GPU offload below break-even")
val path = receipt_path()
if not file_exists(path):
    fail_test("missing native ProcessingIR offload receipt: " + path)
    return
val (_validator_out, _validator_err, validator_code) = process_run(
    "/bin/sh",
    [OFFLOAD_CHECK, "--validate", path]
)
expect(validator_code).to_equal(0)
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
    expect(value_of(receipt, "processing_ir_offload_device_uuid").len()).to_equal(32)
    expect(number_of(receipt, "processing_ir_offload_device_identity")).to_be_greater_than(0)
    expect(value_of(receipt, "processing_ir_offload_source_sha256").len()).to_equal(64)
    expect(value_of(receipt, "processing_ir_offload_artifact_sha256").len()).to_equal(64)
    expect(value_of(receipt, "processing_ir_offload_raw_samples_sha256").len()).to_equal(64)
    expect(value_of(receipt, "processing_ir_offload_provenance_manifest_path").len()).to_be_greater_than(0)
    expect(value_of(receipt, "processing_ir_offload_provenance_manifest_sha256").len()).to_equal(64)
    expect(number_of(receipt, "processing_ir_offload_coverage_max_batch")).to_be_greater_than(1048575)

val warmup = number_of(receipt, "processing_ir_offload_warmup_samples")
val samples = number_of(receipt, "processing_ir_offload_measured_samples")
val rows = number_of(receipt, "processing_ir_offload_row_count")
expect(warmup).to_be_greater_than(2)
expect(samples).to_be_greater_than(4)
if output_only:
    expect(rows).to_be_greater_than(2)
else:
    expect(rows).to_be_greater_than(3)

val cpu_rss = number_of(receipt, "processing_ir_offload_cpu_rss_kb")
val gpu_rss = number_of(receipt, "processing_ir_offload_gpu_rss_kb")
val peak_rss = number_of(receipt, "processing_ir_offload_peak_rss_kb")
val communication = number_of(receipt, "processing_ir_offload_communication_overhead_us")
expect(cpu_rss).to_be_greater_than(0)
expect(gpu_rss).to_be_greater_than(0)
expect(peak_rss).to_be_greater_than(0)
expect(communication).to_be_greater_than(-1)

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
    expect(mismatch_count).to_equal(0)
    if output_only:
        expect(upload).to_equal(0)
        expect(upload_bytes).to_equal(0)
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
    expect(faster_rows).to_equal(0)
    expect(measured_break_even).to_equal(0)
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ProcessingIR GPU offload break-even evidence.
- ProcessingIR GPU offload break-even evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `0210df98bdae039dc00fdd8fe076bba9fdee055fa304c4efb96d4aaeee3a50b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0210df98bdae039dc00fdd8fe076bba9fdee055fa304c4efb96d4aaeee3a50b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0210df98bdae039dc00fdd8fe076bba9fdee055fa304c4efb96d4aaeee3a50b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a Linux CUDA/Vulkan measurement host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the offload receipt validator honest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires measured rows and rejects slower GPU offload below break-even' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
