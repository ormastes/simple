# processing_cuda_hal_live_spec

> Purpose: This spec proves physical CUDA HAL ProcessingIR transport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_cuda_hal_live_spec

Purpose: This spec proves physical CUDA HAL ProcessingIR transport.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/processing_cuda_hal_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves physical CUDA HAL ProcessingIR transport.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### physical CUDA HAL ProcessingIR transport

#### should upload CPU input and return exact PTX device readback

- Select representative renderer processing kernels
   - Expected: session.init() equals `CUDA_SUCCESS`
   - Expected: session.activate() equals `CUDA_SUCCESS`
- Lower shared ProcessingIR for the selected backend
   - Expected: upload_status equals `CUDA_SUCCESS`
- Compile and validate the backend artifact
   - Expected: session.module_cache equals `module`
- Submit native work and capture device readback
   - Expected: session.launch_kernel_args("processing_hal_add_u32", 1, 1, 1, 32, 1, 1, args) equals `CUDA_SUCCESS`
   - Expected: session.sync() equals `CUDA_SUCCESS`
   - Expected: cuda_memcpy_dtoh(host_output, device_output, bytes) equals `CUDA_SUCCESS`
- Compare device readback with the CPU oracle
   - Expected: raw_read_i32(host_output, 0) as i64 equals `8`
   - Expected: raw_read_i32(host_output, 4) as i64 equals `9`
   - Expected: raw_read_i32(host_output, 8) as i64 equals `17`
   - Expected: raw_read_i32(host_output, 12) as i64 equals `107`


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-013
# @req: REQ-014
step("Select representative renderer processing kernels")
var session = CudaSession.create()
expect(session.init()).to_equal(CUDA_SUCCESS)
expect(session.activate()).to_equal(CUDA_SUCCESS)
val identity = cuda_device_identity(session.device)
expect(identity).to_be_greater_than(0)
val module = session.load_module(HAL_PTX)
expect(module).to_be_greater_than(0)

step("Lower shared ProcessingIR for the selected backend")
val count: i64 = 4
val bytes: i64 = 16
val host_input = raw_alloc(bytes)
val host_output = raw_alloc(bytes)
val values = raw_alloc(24)
val args = raw_alloc(24)
val device_input = session.alloc(bytes)
val device_output = session.alloc(bytes)
expect(host_input).to_be_greater_than(0)
expect(host_output).to_be_greater_than(0)
expect(device_input).to_be_greater_than(0)
expect(device_output).to_be_greater_than(0)

# CPU oracle input: [1, 2, 10, 100], packed as two little-endian pairs.
raw_write_i64(host_input, 0, 0x0000000200000001)
raw_write_i64(host_input, 8, 0x000000640000000A)
val upload_status = cuda_memcpy_htod(device_input, host_input, bytes)
expect(upload_status).to_equal(CUDA_SUCCESS)
write_args(values, args, device_output, device_input, count)

step("Compile and validate the backend artifact")
expect(session.module_cache).to_equal(module)

step("Submit native work and capture device readback")
expect(session.launch_kernel_args("processing_hal_add_u32", 1, 1, 1, 32, 1, 1, args)).to_equal(CUDA_SUCCESS)
expect(session.sync()).to_equal(CUDA_SUCCESS)
expect(cuda_memcpy_dtoh(host_output, device_output, bytes)).to_equal(CUDA_SUCCESS)

step("Compare device readback with the CPU oracle")
expect(raw_read_i32(host_output, 0) as i64).to_equal(8)
expect(raw_read_i32(host_output, 4) as i64).to_equal(9)
expect(raw_read_i32(host_output, 8) as i64).to_equal(17)
expect(raw_read_i32(host_output, 12) as i64).to_equal(107)
val happy = "PROCESSING_CUDA_HAL_HAPPY status=pass backend=cuda device_origin=true cpu_upload=true ptx_dispatch=true device_download=true oracle_match=true identity={identity} context={session.ctx} module={module} output=8,9,17,107 cpu_fallback=false\n"
expect(dir_create_all(CUDA_RECEIPT_DIR)).to_be(true)
expect(file_write(CUDA_RECEIPT, happy)).to_be(true)
print(happy)
session.free(device_output)
session.free(device_input)
raw_free(args, 24)
raw_free(values, 24)
raw_free(host_output, bytes)
raw_free(host_input, bytes)
session.shutdown()
```

</details>

#### should preserve device identity and executor handle across repeated dispatches

- Select representative renderer processing kernels
- Lower shared ProcessingIR for the selected backend
- Submit native work and capture device readback
- Compare device readback with the CPU oracle
   - Expected: first.completed is true
   - Expected: second.completed is true
   - Expected: first.values.len() equals `64`
   - Expected: second.values equals `first.values`
   - Expected: second.backend_handle equals `first.backend_handle`
   - Expected: second.device_identity equals `first.device_identity`
   - Expected: executor.device_buffer equals `first_device_buffer`
   - Expected: executor.host_buffer equals `first_host_buffer`
   - Expected: first_capacity equals `256`
   - Expected: executor.buffer_capacity equals `first_capacity`
   - Expected: executor.device_buffer equals `0`
   - Expected: executor.host_buffer equals `0`
   - Expected: executor.buffer_capacity equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select representative renderer processing kernels")
val ir = processing_ir_fill_u32(64, 0x01020304u32)
var executor = ProcessingCudaExecutor.create()

step("Lower shared ProcessingIR for the selected backend")
val first = processing_ir_execute_cuda_with_executor(executor, ir)
val first_device_buffer = executor.device_buffer
val first_host_buffer = executor.host_buffer
val first_capacity = executor.buffer_capacity

step("Submit native work and capture device readback")
val second = processing_ir_execute_cuda_with_executor(executor, ir)

step("Compare device readback with the CPU oracle")
expect(first.completed).to_equal(true)
expect(second.completed).to_equal(true)
expect(first.values.len()).to_equal(64)
expect(second.values).to_equal(first.values)
expect(first.backend_handle).to_be_greater_than(0)
expect(second.backend_handle).to_equal(first.backend_handle)
expect(first.device_identity).to_be_greater_than(0)
expect(second.device_identity).to_equal(first.device_identity)
expect(first_device_buffer).to_be_greater_than(0)
expect(executor.device_buffer).to_equal(first_device_buffer)
expect(first_host_buffer).to_be_greater_than(0)
expect(executor.host_buffer).to_equal(first_host_buffer)
expect(first_capacity).to_equal(256)
expect(executor.buffer_capacity).to_equal(first_capacity)
executor.shutdown()
expect(executor.device_buffer).to_equal(0)
expect(executor.host_buffer).to_equal(0)
expect(executor.buffer_capacity).to_equal(0)
val repeated = "PROCESSING_CUDA_HAL_REPEAT status=pass backend=cuda device_origin=true repeated_dispatches=2 stable_identity=true stable_handle=true identity={first.device_identity} handle={first.backend_handle} cpu_fallback=false\n"
expect(file_append_text(CUDA_RECEIPT, repeated)).to_be(true)
print(repeated)
```

</details>

#### should reject invalid host-to-device and device-to-host transfers exactly

- Select representative renderer processing kernels
   - Expected: session.init() equals `CUDA_SUCCESS`
   - Expected: session.activate() equals `CUDA_SUCCESS`
- Submit native work and capture device readback
- Compare device readback with the CPU oracle
   - Expected: invalid_upload_status equals `CUDA_ERROR_INVALID_VALUE`
   - Expected: invalid_download_status equals `CUDA_ERROR_INVALID_VALUE`
- Record unavailable native host evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select representative renderer processing kernels")
var session = CudaSession.create()
expect(session.init()).to_equal(CUDA_SUCCESS)
expect(session.activate()).to_equal(CUDA_SUCCESS)
val host = raw_alloc(16)
val device = session.alloc(16)
expect(host).to_be_greater_than(0)
expect(device).to_be_greater_than(0)

step("Submit native work and capture device readback")
val invalid_upload_status = cuda_memcpy_htod(0, host, 16)
val invalid_download_status = cuda_memcpy_dtoh(host, 0, 16)

step("Compare device readback with the CPU oracle")
expect(invalid_upload_status).to_equal(CUDA_ERROR_INVALID_VALUE)
expect(invalid_download_status).to_equal(CUDA_ERROR_INVALID_VALUE)
val rejected = "PROCESSING_CUDA_HAL_ERROR status=pass backend=cuda invalid_upload_status={invalid_upload_status} invalid_download_status={invalid_download_status} expected={CUDA_ERROR_INVALID_VALUE} fail_closed=true cpu_fallback=false\n"
expect(file_append_text(CUDA_RECEIPT, rejected)).to_be(true)
print(rejected)

step("Record unavailable native host evidence")
session.free(device)
raw_free(host, 16)
session.shutdown()
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-013`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f40449982d4ebda7ce6500aa1af1aadd3a64e48cd4361feb9d74a08b2217ec54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f40449982d4ebda7ce6500aa1af1aadd3a64e48cd4361feb9d74a08b2217ec54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f40449982d4ebda7ce6500aa1af1aadd3a64e48cd4361feb9d74a08b2217ec54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **81/100**; blockers: **0**.

SSpec documentization score: 81/100
source: test/02_integration/rendering/processing_cuda_hal_live_spec.spl
mirror: doc/06_spec/02_integration/rendering/processing_cuda_hal_live_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/processing_cuda_hal_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/processing_cuda_hal_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should upload CPU input and return exact PTX device readback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should upload CPU input and return exact PTX device readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve device identity and executor handle across repeated dispatches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve device identity and executor handle across repeated dispatches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:132:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid host-to-device and device-to-host transfers exactly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/rendering/processing_cuda_hal_live_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject invalid host-to-device and device-to-host transfers exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
