# Processing Ir Executor Reason Mapping Contract Specification

> Tests covering ProcessingIR executor failure wire-code mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Ir Executor Reason Mapping Contract Specification

## Scenarios

### ProcessingIR executor failure wire-code mapping

#### exports stable submit and readback reason constants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports stable submit and readback reason constants
   - Expected: file_exists(PROTOCOL) is true
   - Expected: SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports stable submit and readback reason constants")
val source = file_read(PROTOCOL)
expect(file_exists(PROTOCOL)).to_equal(true)
expect(source).to_contain("val SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED: i64 = 16")
expect(source).to_contain("val SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED: i64 = 17")
expect(SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD).to_equal(18)
expect(source).to_contain("val SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD: i64 = 18")
expect(source).to_contain(
    "export SIMPLEOS_HOST_GPU_REASON_UNKNOWN_IMAGE_RESOURCE, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED")
expect(source).to_contain(
    "export SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD")
expect(source).to_contain("export simpleos_host_gpu_processing_reason")
```

</details>

#### maps typed executor reasons without changing checksum fallback

- maps typed executor reasons without changing checksum fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps typed executor reasons without changing checksum fallback")
val source = file_read(PROTOCOL)
expect(source).to_contain("if reason == \"checksum-mismatch\":\n        return SIMPLEOS_HOST_GPU_REASON_CHECKSUM_MISMATCH")
expect(source).to_contain("reason.ends_with(\"-submit-failed\")")
expect(source).to_contain("reason.ends_with(\"-dispatch-failed\")")
expect(source).to_contain("reason.ends_with(\"-readback-failed\")")
expect(source).to_contain("reason == \"readback-size-mismatch\"")
expect(source).to_contain("SIMPLEOS_HOST_GPU_REASON_NON_DEVICE_READBACK")
```

</details>

#### executes the typed mapping for every backend reason shape

- executes the typed mapping for every backend reason shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes the typed mapping for every backend reason shape")
for reason in [
    "cuda-submit-failed", "cuda-dispatch-failed",
    "vulkan-submit-failed", "vulkan-dispatch-failed",
    "vulkan-dispatch-completion-unknown", "vulkan-dispatch-ineligible",
    "metal-submit-failed", "metal-dispatch-failed"
]:
    expect(simpleos_host_gpu_processing_reason(reason)).to_equal(
        SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED)
for reason in [
    "cuda-readback-failed", "vulkan-readback-failed",
    "metal-readback-failed", "metal-readback-size-mismatch"
]:
    expect(simpleos_host_gpu_processing_reason(reason)).to_equal(
        SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED)
expect(simpleos_host_gpu_processing_reason("checksum-mismatch")).to_equal(
    SIMPLEOS_HOST_GPU_REASON_CHECKSUM_MISMATCH)
for reason in [
    "cuda-unavailable", "cuda-init-failed", "cuda-device-get-failed",
    "cuda-context-create-failed", "cuda-module-load-failed",
    "cuda-allocation-failed", "cuda-device-identity-unavailable",
    "vulkan-unavailable", "vulkan-init-failed",
    "vulkan-dependency-quarantine-pending", "vulkan-allocation-failed",
    "vulkan-shader-compile-failed", "vulkan-pipeline-create-failed",
    "vulkan-device-identity-unavailable",
    "metal-unavailable", "metal-init-failed",
    "metal-device-identity-unavailable", "metal-device-create-failed",
    "metal-command-queue-create-failed", "metal-shader-compile-failed",
    "metal-pipeline-create-failed", "metal-allocation-failed"
]:
    expect(simpleos_host_gpu_processing_reason(reason)).to_equal(
        SIMPLEOS_HOST_GPU_REASON_NON_DEVICE_READBACK)
```

</details>

#### keeps native driver prose behind stable executor reason tokens

- keeps native driver prose behind stable executor reason tokens
   - Expected: file_exists(CUDA) is true
   - Expected: file_exists(VULKAN) is true
   - Expected: file_exists(METAL) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps native driver prose behind stable executor reason tokens")
val cuda = file_read(CUDA)
val vulkan = file_read(VULKAN)
val metal = file_read(METAL)
expect(file_exists(CUDA)).to_equal(true)
expect(file_exists(VULKAN)).to_equal(true)
expect(file_exists(METAL)).to_equal(true)
expect(cuda).to_not_contain("cuda_last_error")
expect(vulkan).to_not_contain("vulkan_last_error")
expect(metal).to_not_contain("metal_last_error")
for reason in [
    "vulkan-init-failed", "vulkan-allocation-failed",
    "vulkan-shader-compile-failed", "vulkan-pipeline-create-failed"
]:
    expect(vulkan).to_contain("\"" + reason + "\"")
for reason in [
    "metal-init-failed", "metal-device-create-failed",
    "metal-command-queue-create-failed", "metal-shader-compile-failed",
    "metal-pipeline-create-failed", "metal-allocation-failed",
    "metal-dispatch-failed", "metal-readback-failed"
]:
    expect(metal).to_contain("\"" + reason + "\"")
```

</details>

#### retains every executor result reason and finishes with the mapper

- retains every executor result reason and finishes with the mapper
   - Expected: file_exists(HOST) is true
   - Expected: file_exists(PLATFORM) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retains every executor result reason and finishes with the mapper")
expect(file_exists(HOST)).to_equal(true)
val source = file_read(HOST)
val providers = file_read(PLATFORM)
expect(file_exists(PLATFORM)).to_equal(true)
expect(source).to_contain("val result = platform.execute_processing(ir, backend)")
expect(source).to_contain("val executor_reason = result.reason")
expect(providers).to_contain(
    "val result = processing_ir_execute_cuda_with_executor(cuda_executor, ir)")
expect(providers).to_contain("val result = processing_ir_execute_vulkan(ir)")
expect(file_read(MACOS_PLATFORM)).to_contain(
    "val result = processing_ir_execute_metal(ir)")
expect(source).to_contain(
    "val failure_reason = simpleos_host_gpu_processing_reason(executor_reason)")
expect(source).to_contain(
    "_processing_cpu_fallback(base, generation, failure_reason, ir)")
expect(source).to_contain(
    "_finish(base, generation, SIMPLEOS_HOST_GPU_STATUS_FAIL, failure_reason, 0, 0, 0, 1, 0, 0)"
)
```

</details>

#### rejects strict zero-mask negotiation as unsupported

- rejects strict zero-mask negotiation as unsupported


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects strict zero-mask negotiation as unsupported")
val source = file_read(HOST)
expect(source).to_contain(
    "# Rejecting this HELLO must not leave a previous session negotiated.")
for field in [
    "SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_RENDER_MASK",
    "SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_PROCESSING_MASK",
    "SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_MAX_PAYLOAD",
    "SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_MAX_READBACK",
    "SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_VERSION",
    "SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_CAPABILITY_MASK"
]:
    expect(source).to_contain("_write(base, " + field + ", 0)")
expect(source).to_contain(
    "_write(base, SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_RENDER_MASK, 0)\n" +
    "    _write(base, SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_PROCESSING_MASK, 0)\n" +
    "    _write(base, SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_MAX_PAYLOAD, 0)\n" +
    "    _write(base, SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_MAX_READBACK, 0)\n" +
    "    _write(base, SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_VERSION, 0)\n" +
    "    _write(base, SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_CAPABILITY_MASK, 0)\n" +
    "    memory_barrier_required()\n" +
    "    val negotiated_processing_mask = platform.processing_backend_mask(processing_mask, processing_selector)")
expect(source).to_contain(
    "if processing_selector != \"auto\" and negotiated_processing_mask == 0:")
expect(source).to_contain(
    "_finish(base, generation, SIMPLEOS_HOST_GPU_STATUS_UNSUPPORTED, SIMPLEOS_HOST_GPU_REASON_UNSUPPORTED_BACKEND, 0, 0, 0, _elapsed_us_since(started), 0, 0)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ProcessingIR executor failure wire-code mapping.
- ProcessingIR executor failure wire-code mapping

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be14e72587750d99bde41c774967d763bc847c421aecddbf5df501ac69d60d21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be14e72587750d99bde41c774967d763bc847c421aecddbf5df501ac69d60d21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be14e72587750d99bde41c774967d763bc847c421aecddbf5df501ac69d60d21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports stable submit and readback reason constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps typed executor reasons without changing checksum fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the typed mapping for every backend reason shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
