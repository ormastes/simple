# Processing Cpu Fallback Policy Contract Specification

> Tests covering SimpleOS processing CPU fallback policy contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Cpu Fallback Policy Contract Specification

## Scenarios

### SimpleOS processing CPU fallback policy contract

#### defaults the CLI to none and accepts only none or cpu

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults the CLI to none and accepts only none or cpu
   - Expected: file_exists(HOST) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults the CLI to none and accepts only none or cpu")
val source = file_read(HOST)
expect(file_exists(HOST)).to_equal(true)
expect(source).to_contain("val processing_fallback = if requested_processing_fallback == \"\": \"none\" else: requested_processing_fallback")
expect(source).to_contain("if processing_fallback != \"none\" and processing_fallback != \"cpu\":")
expect(source).to_contain("--processing-fallback must be none or cpu")
expect(source).to_contain("val processing_fallback_cpu = processing_fallback == \"cpu\"")
```

</details>

#### passes the fallback boolean into both processing requests

- passes the fallback boolean into both processing requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes the fallback boolean into both processing requests")
val source = file_read(HOST)
expect(source).to_contain("_process_request(platform, base, processing_selector, processing_fallback_cpu, processing_verify_cpu, processing_min_offload_elements, [])")
expect(source).to_contain("_process_request(platform, base, processing_selector, processing_fallback_cpu, processing_verify_cpu, processing_min_offload_elements, retained)")
expect(source).to_contain("fn _process_request(platform: SimpleOsGpuHostPlatform, base: i64, processing_selector: text, processing_fallback_cpu: bool, processing_verify_cpu: bool, processing_min_offload_elements: i64")
```

</details>

#### uses measured backend defaults and preserves explicit overrides

- uses measured backend defaults and preserves explicit overrides
   - Expected: simpleos_gpu_processing_min_offload_elements("cuda", -1) equals `536870912`
   - Expected: simpleos_gpu_processing_min_offload_elements("vulkan", -1) equals `65536`
   - Expected: simpleos_gpu_processing_min_offload_elements("metal", -1) equals `536870912`
   - Expected: simpleos_gpu_processing_min_offload_elements("cuda", 0) equals `0`
   - Expected: simpleos_gpu_processing_min_offload_elements("cuda", 123) equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses measured backend defaults and preserves explicit overrides")
val source = file_read(HOST)
expect(simpleos_gpu_processing_min_offload_elements("cuda", -1)).to_equal(536870912)
expect(simpleos_gpu_processing_min_offload_elements("vulkan", -1)).to_equal(65536)
expect(simpleos_gpu_processing_min_offload_elements("metal", -1)).to_equal(536870912)
expect(simpleos_gpu_processing_min_offload_elements("cuda", 0)).to_equal(0)
expect(simpleos_gpu_processing_min_offload_elements("cuda", 123)).to_equal(123)
expect(source).to_contain("val effective_min_offload_elements = simpleos_gpu_processing_min_offload_elements(backend, processing_min_offload_elements)")
expect(source).to_contain("use std.common.text." + "{" + "parse_i64" + "}")
expect(source).to_contain("parse_i64(requested_processing_min_offload_elements)")
expect(source).to_contain("not args.contains(\"--processing-min-offload-elements=\")")
expect(source).to_contain("processing_min_offload_elements.to_text() == requested_processing_min_offload_elements")
expect(source).to_contain("if not processing_min_offload_elements_valid:")
expect(source).to_contain("--processing-min-offload-elements must be a non-negative integer")
```

</details>

#### keeps fallback wire codes distinct and exported

- keeps fallback wire codes distinct and exported
   - Expected: file_exists(PROTOCOL) is true
   - Expected: SIMPLEOS_HOST_GPU_STATUS_FALLBACK equals `4`
   - Expected: SIMPLEOS_HOST_GPU_READBACK_CPU equals `2`
   - Expected: SIMPLEOS_HOST_GPU_STATUS_FALLBACK != SIMPLEOS_HOST_GPU_READBACK_CPU is true
   - Expected: SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps fallback wire codes distinct and exported")
val source = file_read(PROTOCOL)
expect(file_exists(PROTOCOL)).to_equal(true)
expect(SIMPLEOS_HOST_GPU_STATUS_FALLBACK).to_equal(4)
expect(SIMPLEOS_HOST_GPU_READBACK_CPU).to_equal(2)
expect(SIMPLEOS_HOST_GPU_STATUS_FALLBACK != SIMPLEOS_HOST_GPU_READBACK_CPU).to_equal(true)
expect(source).to_contain("val SIMPLEOS_HOST_GPU_STATUS_FALLBACK: i64 = 4")
expect(source).to_contain("val SIMPLEOS_HOST_GPU_READBACK_CPU: i64 = 2")
expect(source).to_contain("export SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_READBACK_DEVICE, SIMPLEOS_HOST_GPU_READBACK_CPU")
expect(SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD).to_equal(18)
expect(source).to_contain("val SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD: i64 = 18")
expect(source).to_contain("export SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD")
```

</details>

#### writes the CPU oracle with zero native provenance and fallback status

- writes the CPU oracle with zero native provenance and fallback status


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes the CPU oracle with zero native provenance and fallback status")
val source = file_read(HOST)
expect(source).to_contain("val checksum = _write_pixels(base, oracle, ir.element_count)")
expect(source).to_contain("_finish(base, generation, SIMPLEOS_HOST_GPU_STATUS_FALLBACK, reason, 0,")
expect(source).to_contain("SIMPLEOS_HOST_GPU_READBACK_CPU, 0)")
expect(source).to_contain("fn _processing_cpu_fallback(base: i64, generation: i64, reason: i64, ir: ProcessingIr)")
expect(source).to_contain("val oracle = processing_ir_cpu_execute(ir)")
```

</details>

#### bypasses device work only for calibrated CPU fallback

- bypasses device work only for calibrated CPU fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bypasses device work only for calibrated CPU fallback")
val source = file_read(HOST)
val policy = source.index_of("if processing_fallback_cpu and effective_min_offload_elements > 0 and element_count < effective_min_offload_elements:")
val device = source.index_of("val device_started = time_now_nanos()")
expect(policy).to_be_greater_than(0)
expect(policy).to_be_less_than(device)
expect(source).to_contain("_processing_cpu_fallback(base, generation, SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD")
expect(source).to_contain("effective_min_offload_elements > 0")
expect(source).to_contain("element_count < effective_min_offload_elements")
```

</details>

#### keeps executor failure and mismatch fallback behavior

- keeps executor failure and mismatch fallback behavior


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps executor failure and mismatch fallback behavior")
val source = file_read(HOST)
expect(source).to_contain("if not completed or backend_handle <= 0 or device_identity <= 0:\n            val failure_reason = simpleos_host_gpu_processing_reason(executor_reason)\n            if processing_fallback_cpu:\n                return _loop_state(if _processing_cpu_fallback")
expect(source).to_contain("if processing_verify_cpu and not processing_ir_outputs_equal(values, oracle):\n            if processing_fallback_cpu:\n                return _loop_state(if _processing_cpu_fallback")
expect(source).to_contain("val checksum = _write_fill_pixels(base, values, element_count, ir.value)")
expect(source).to_contain("if checksum <= 0:\n            if processing_fallback_cpu:")
expect(source).to_contain("_finish(base, generation, SIMPLEOS_HOST_GPU_STATUS_FAIL, failure_reason, 0, 0, 0, 1, 0, 0)")
expect(source).to_contain("_finish(base, generation, SIMPLEOS_HOST_GPU_STATUS_FAIL, SIMPLEOS_HOST_GPU_REASON_CHECKSUM_MISMATCH, 0, 0, 0, 1, 0, 0)")
```

</details>

#### fuses production FillU32 validation with the wire copy

- fuses production FillU32 validation with the wire copy
   - Expected: source does not contain `processing_ir_output_matches`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fuses production FillU32 validation with the wire copy")
val source = file_read(HOST)
val raw = file_read(RAW)
val runtime = file_read(RAW_RUNTIME)
expect(source.contains("processing_ir_output_matches")).to_equal(false)
expect(source).to_contain("raw_write_fill_u32s_checksum")
expect(raw).to_contain("rt_write_fill_u32s_to_raw_checksum")
expect(runtime).to_contain("count != rt_array_len(values)")
expect(runtime).to_contain("expected > i64::from(u32::MAX)")
expect(runtime).to_contain("exact &= value == expected")
expect(runtime).to_contain("if !exact")
expect(runtime).to_contain("test_write_fill_u32s_to_raw_checksum_fuses_exact_validation")
```

</details>

#### runs the CPU oracle only for fallback or explicit verification

- runs the CPU oracle only for fallback or explicit verification
   - Expected: source does not contain `processing_ir_output_matches`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the CPU oracle only for fallback or explicit verification")
val source = file_read(HOST)
val wrapper = file_read(QEMU_WRAPPER)
val request = source.slice(
    source.index_of("fn _process_request("),
    source.index_of("fn _arg_value("))
val verify = request.index_of("if processing_verify_cpu:")
val cpu = request.index_of("processing_ir_cpu_execute(ir)")
expect(source).to_contain("val processing_verify_cpu = args.contains(\"--processing-verify-cpu\")")
expect(source).to_contain("if processing_verify_cpu:\n            val cpu_started = time_now_nanos()")
expect(source).to_contain("if processing_verify_cpu:\n            val preference = _processing_preference")
expect(source.contains("processing_ir_output_matches")).to_equal(false)
expect(wrapper).to_contain("set -- \"$@\" --processing-verify-cpu")
expect(verify).to_be_greater_than(0)
expect(cpu).to_be_greater_than(verify)
expect(request.slice(cpu + 1, request.len()).contains(
    "processing_ir_cpu_execute(ir)")).to_equal(false)
```

</details>

#### exports a correlated fallback validator and rejects forged provenance

- exports a correlated fallback validator and rejects forged provenance
   - Expected: file_exists(GUEST_BRIDGE) is true
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(good, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is true
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(wrong_status, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(native_handle, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(wrong_source, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(wrong_correlation, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports a correlated fallback validator and rejects forged provenance")
val source = file_read(GUEST_BRIDGE)
expect(file_exists(GUEST_BRIDGE)).to_equal(true)
expect(source).to_contain("fn host_gpu_ivshmem_fallback_receipt_valid")
expect(source).to_contain("receipt.status == SIMPLEOS_HOST_GPU_STATUS_FALLBACK and receipt.reason > 0")
expect(source).to_contain("receipt.native_handle == 0 and receipt.device_identity == 0")
expect(source).to_contain("receipt.readback_source == SIMPLEOS_HOST_GPU_READBACK_CPU")
expect(source).to_contain("receipt.run_id_hash == expected_run_id_hash and receipt.frame_id == expected_frame_id")
expect(source).to_contain("export host_gpu_ivshmem_device_receipt_valid, host_gpu_ivshmem_fallback_receipt_valid")

val good = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 0, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 31, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(good, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(true)
val wrong_status = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FAIL, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 0, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 31, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(wrong_status, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)
val native_handle = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 41, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 31, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(native_handle, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)
val wrong_source = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 0, 0, 1, 31, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(wrong_source, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)
val wrong_correlation = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 0, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(wrong_correlation, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS processing CPU fallback policy contract.
- SimpleOS processing CPU fallback policy contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `db0be3c804b240496abd2e4b51b573ff0920f2332b1180e93a04358fa2b251f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db0be3c804b240496abd2e4b51b573ff0920f2332b1180e93a04358fa2b251f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db0be3c804b240496abd2e4b51b573ff0920f2332b1180e93a04358fa2b251f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults the CLI to none and accepts only none or cpu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes the fallback boolean into both processing requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses measured backend defaults and preserves explicit overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
