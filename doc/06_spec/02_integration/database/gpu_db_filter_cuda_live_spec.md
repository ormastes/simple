# gpu_db_filter_cuda_live_spec

> Physical CUDA DB filter execution and strict production admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_db_filter_cuda_live_spec

Physical CUDA DB filter execution and strict production admission.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/database/gpu_db_filter_cuda_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Physical CUDA DB filter execution and strict production admission.

## Scenarios

### physical CUDA DB filter ProcessingIR

#### should reject a small batch before CUDA initialization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject a small batch before CUDA initialization
   - Expected: result.device.completed is false
   - Expected: executor.device_input equals `0`
   - Expected: executor.device_output equals `0`
   - Expected: result.admission.execution.submission.accepted is false
   - Expected: result.admission.execution.gpu_dispatched is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should reject a small batch before CUDA initialization")
val ir = processing_ir_db_filter_u32(
    [2u32, 7u32, 9u32, 10u32], 7u32, 10u32)
var executor = ProcessingDbCudaExecutor.create()
val state = gpu_wdb_queue_initial(2)
val backend = gpu_wdb_device_backend(
    "cuda", 7, ["gpu_db_columnar_scan_batch"], true, "physical-cuda")
val result = processing_db_filter_cuda_execute_and_admit(
    executor, ir, DbGpuMode.RamOnly, state, backend,
    true, 7, true, gpu_wdb_default_budget())
expect(result.device.completed).to_equal(false)
expect(result.device.reason).to_equal(
    "cuda-db-not-dispatched:batch-too-small")
expect(executor.device_input).to_equal(0)
expect(executor.device_output).to_equal(0)
expect(result.admission.execution.submission.accepted).to_equal(false)
expect(result.admission.execution.gpu_dispatched).to_equal(false)
executor.shutdown()
```

</details>

#### should reject malformed large IR before GPU admission

- should reject malformed large IR before GPU admission
   - Expected: result.device.completed is false
   - Expected: result.device.reason equals `db-filter-range-invalid`
   - Expected: executor.device_input equals `0`
   - Expected: result.admission.execution.submission.accepted is false
   - Expected: result.admission.execution.gpu_dispatched is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should reject malformed large IR before GPU admission")
val ir = processing_ir_db_filter_u32(
    representative_db_values(2048), 200u32, 100u32)
var executor = ProcessingDbCudaExecutor.create()
val result = processing_db_filter_cuda_execute_and_admit(
    executor, ir, DbGpuMode.RamOnly, gpu_wdb_queue_initial(2),
    gpu_wdb_device_backend(
        "cuda", 7, ["gpu_db_columnar_scan_batch"], true,
        "physical-cuda"),
    true, 7, true, gpu_wdb_default_budget())
expect(result.device.completed).to_equal(false)
expect(result.device.reason).to_equal("db-filter-range-invalid")
expect(executor.device_input).to_equal(0)
expect(result.admission.execution.submission.accepted).to_equal(false)
expect(result.admission.execution.gpu_dispatched).to_equal(false)
executor.shutdown()
```

</details>

#### should handle an odd launch tail and unsigned extrema exactly

- should handle an odd launch tail and unsigned extrema exactly
   - Expected: result.completed is true
   - Expected: result.mask.len() equals `257`
   - Expected: result.row_ids equals `[0, 256]`
   - Expected: result.receipt.mismatch_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should handle an odd launch tail and unsigned extrema exactly")
var values = representative_db_values(257)
values[0] = 0xffffffffu32
values[256] = 0xffffffffu32
val ir = processing_ir_db_filter_u32(
    values, 0xffffffffu32, 0xffffffffu32)
var executor = ProcessingDbCudaExecutor.create()
val result = processing_db_filter_u32_execute_cuda_with_executor(
    executor, ir)
expect(result.completed).to_equal(true)
expect(result.mask.len()).to_equal(257)
expect(result.row_ids).to_equal([0, 256])
expect(result.receipt.mismatch_count).to_equal(0)
expect(result.receipt.actual_checksum).to_equal(
    result.receipt.expected_checksum)
executor.shutdown()
```

</details>

#### should return the exact CPU-oracle mask and retain warm buffers

- should return the exact CPU-oracle mask and retain warm buffers
- Build a representative data-bearing filter
- Dispatch twice on one CUDA executor
- Verify exact readback and stable allocation
   - Expected: first.completed is true
   - Expected: first.mask equals `[0u32, 1u32, 1u32, 1u32, 0u32]`
   - Expected: first.row_ids equals `[1, 2, 3]`
   - Expected: second.mask equals `first.mask`
   - Expected: second.device_identity equals `first.device_identity`
   - Expected: executor.device_input equals `input_buffer`
   - Expected: executor.device_output equals `output_buffer`
   - Expected: first.receipt.mismatch_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should return the exact CPU-oracle mask and retain warm buffers")
step("Build a representative data-bearing filter")
val ir = processing_ir_db_filter_u32(
    [2u32, 7u32, 9u32, 10u32, 15u32], 7u32, 10u32)
var executor = ProcessingDbCudaExecutor.create()

step("Dispatch twice on one CUDA executor")
val first = processing_db_filter_u32_execute_cuda_with_executor(executor, ir)
val input_buffer = executor.device_input
val output_buffer = executor.device_output
val second = processing_db_filter_u32_execute_cuda_with_executor(executor, ir)

step("Verify exact readback and stable allocation")
expect(first.completed).to_equal(true)
expect(first.mask).to_equal([0u32, 1u32, 1u32, 1u32, 0u32])
expect(first.row_ids).to_equal([1, 2, 3])
expect(second.mask).to_equal(first.mask)
expect(second.device_identity).to_equal(first.device_identity)
expect(executor.device_input).to_equal(input_buffer)
expect(executor.device_output).to_equal(output_buffer)
expect(first.receipt.mismatch_count).to_equal(0)
executor.shutdown()
```

</details>

#### should admit one real large CUDA batch with one queue submission

- should admit one real large CUDA batch with one queue submission
- Create a batch above the GPU admission threshold
- Execute device work and submit its measured receipt
- Require exact evidence and single accounting
   - Expected: result.device.completed is true
   - Expected: result.exact_row_ids is true
   - Expected: result.device.row_ids.len() equals `1024`
   - Expected: result.admission.device_result.production_device_claim is true
   - Expected: result.admission.execution.submission.accepted is true
   - Expected: result.admission.execution.state_after.submitted_count equals `1`
   - Expected: result.admission.execution.state_after.completed_count equals `1`
   - Expected: result.admission.execution.state_after.queue_depth equals `0`
   - Expected: result.admission.device_result.receipt.mismatch_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should admit one real large CUDA batch with one queue submission")
step("Create a batch above the GPU admission threshold")
val ir = processing_ir_db_filter_u32(
    representative_db_values(2048), 64u32, 191u32)
var executor = ProcessingDbCudaExecutor.create()
val state = gpu_wdb_queue_initial(2)
val backend = gpu_wdb_device_backend(
    "cuda", 7, ["gpu_db_columnar_scan_batch"], true, "physical-cuda")

step("Execute device work and submit its measured receipt")
val result = processing_db_filter_cuda_execute_and_admit(
    executor, ir, DbGpuMode.RamOnly, state, backend,
    true, 7, true, gpu_wdb_default_budget())

step("Require exact evidence and single accounting")
expect(result.device.completed).to_equal(true)
expect(result.exact_row_ids).to_equal(true)
expect(result.device.row_ids.len()).to_equal(1024)
expect(result.admission.device_result.production_device_claim).to_equal(true)
expect(result.admission.execution.submission.accepted).to_equal(true)
expect(result.admission.execution.state_after.submitted_count).to_equal(1)
expect(result.admission.execution.state_after.completed_count).to_equal(1)
expect(result.admission.execution.state_after.queue_depth).to_equal(0)
expect(result.admission.device_result.receipt.mismatch_count).to_equal(0)
expect(result.device.ir_prepare_us).to_be_greater_than(0)
expect(result.device.upload_us).to_be_greater_than(0)
expect(result.device.kernel_us).to_be_greater_than(0)
expect(result.device.readback_us).to_be_greater_than(0)
expect(result.device.oracle_us).to_be_greater_than(0)
expect(result.device.total_us).to_be_greater_than(0)
expect(result.device.device_time_us).to_equal(
    result.device.upload_us + result.device.kernel_us +
    result.device.readback_us)
executor.shutdown()
```

</details>

#### should fail closed on readback fault and recover on the same executor

- should fail closed on readback fault and recover on the same executor
- Prime one valid CUDA DB filter execution
   - Expected: env_set("SIMPLE_GPU_TEST", "1") is true
   - Expected: env_set("SIMPLE_GPU_FAULT_INJECT", "") is true
- Inject one typed readback failure
   - Expected: env_set("SIMPLE_GPU_FAULT_INJECT", "cuda:readback") is true
   - Expected: env_set("SIMPLE_GPU_FAULT_INJECT", "") is true
- Recover without replacing the executor
   - Expected: env_set("SIMPLE_GPU_TEST", "") is true
   - Expected: before.completed is true
   - Expected: failed.completed is false
   - Expected: failed.reason equals `cuda-readback-failed`
   - Expected: failed.mask equals `[]`
   - Expected: failed.backend_handle equals `0`
   - Expected: recovered.completed is true
   - Expected: recovered.mask equals `before.mask`
   - Expected: recovered.backend_handle equals `before.backend_handle`
   - Expected: recovered.device_identity equals `before.device_identity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should fail closed on readback fault and recover on the same executor")
step("Prime one valid CUDA DB filter execution")
val ir = processing_ir_db_filter_u32(
    [2u32, 7u32, 9u32, 10u32, 15u32], 7u32, 10u32)
var executor = ProcessingDbCudaExecutor.create()
expect(env_set("SIMPLE_GPU_TEST", "1")).to_equal(true)
expect(env_set("SIMPLE_GPU_FAULT_INJECT", "")).to_equal(true)
val before = processing_db_filter_u32_execute_cuda_with_executor(executor, ir)

step("Inject one typed readback failure")
expect(env_set("SIMPLE_GPU_FAULT_INJECT", "cuda:readback")).to_equal(true)
val failed = processing_db_filter_u32_execute_cuda_with_executor(executor, ir)
expect(env_set("SIMPLE_GPU_FAULT_INJECT", "")).to_equal(true)

step("Recover without replacing the executor")
val recovered = processing_db_filter_u32_execute_cuda_with_executor(executor, ir)
expect(env_set("SIMPLE_GPU_TEST", "")).to_equal(true)
expect(before.completed).to_equal(true)
expect(failed.completed).to_equal(false)
expect(failed.reason).to_equal("cuda-readback-failed")
expect(failed.mask).to_equal([])
expect(failed.backend_handle).to_equal(0)
expect(recovered.completed).to_equal(true)
expect(recovered.mask).to_equal(before.mask)
expect(recovered.backend_handle).to_equal(before.backend_handle)
expect(recovered.device_identity).to_equal(before.device_identity)
executor.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-GPU-DYN-007`
- `REQ-GPU-DYN-010`
- `REQ-GPU-DYN-011`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e51e485847b684281967814c7becbd2a4708e755d517d58cb5403e6c79f8be79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e51e485847b684281967814c7becbd2a4708e755d517d58cb5403e6c79f8be79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e51e485847b684281967814c7becbd2a4708e755d517d58cb5403e6c79f8be79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/database/gpu_db_filter_cuda_live_spec.spl
mirror: doc/06_spec/02_integration/database/gpu_db_filter_cuda_live_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/02_integration/database/gpu_db_filter_cuda_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/database/gpu_db_filter_cuda_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a small batch before CUDA initialization' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a small batch before CUDA initialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed large IR before GPU admission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject malformed large IR before GPU admission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle an odd launch tail and unsigned extrema exactly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle an odd launch tail and unsigned extrema exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return the exact CPU-oracle mask and retain warm buffers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:122:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit one real large CUDA batch with one queue submission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/database/gpu_db_filter_cuda_live_spec.spl:159:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed on readback fault and recover on the same executor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
