# Processing Ir Fault Source Contract Specification

> Tests covering ProcessingIR GPU executor fault source contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Ir Fault Source Contract Specification

## Scenarios

### ProcessingIR GPU executor fault source contract

#### imports the shared fault reason helper in every executor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_read(CUDA_EXECUTOR)).to_contain(FAULT_IMPORT)
for entry in BACKENDS:
    val source = _assert_exists_and_read(entry[1])
    expect(source).to_contain(FAULT_IMPORT)
```

</details>

#### guards every init, submit, readback, and mismatch phase

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_read(METAL_EXECUTOR)).to_contain(
    "processing_ir_fault_reason(\"metal\", \"mismatch\")")
for entry in BACKENDS:
    val source = _assert_exists_and_read(entry[1])
    for phase in PHASES:
        _assert_guarded_phase(source, entry[0], phase)
```

</details>

#### requires both the test gate and exact backend phase selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _assert_exists_and_read(FAULT_HELPER)
expect(source).to_contain(
    "if env_get(\"SIMPLE_GPU_TEST\") != \"1\" or\n       env_get(\"SIMPLE_GPU_FAULT_INJECT\") != target:")
expect(source).to_contain(
    "if _processing_ir_fault_target != target:\n        _processing_ir_fault_target = target\n        _processing_ir_fault_match_count = 0")
expect(source).to_contain(
    "_processing_ir_fault_match_count = _processing_ir_fault_match_count + 1")
expect(source).to_contain(
    "env_get(\"SIMPLE_GPU_FAULT_INJECT_SKIP_MATCHES\") != \"1\" or\n        _processing_ir_fault_match_count > 1")
```

</details>

#### requires exact Metal success output and checksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _assert_exists_and_read(METAL_LIVE_SPEC)
expect(source).to_contain(
    "processing_ir_fill_u32, processing_ir_output_matches")
expect(source).to_contain(
    "val values_exact = processing_ir_output_matches(ir, result.values)")
expect(source).to_contain("val checksum = _checksum(result.values)")
expect(source).to_contain(
    "values=8 values_exact=true checksum=135272480")
expect(source).to_contain(
    "values=0 values_exact=false checksum=0 handle=0 identity=0")
```

</details>

#### keeps runtime Metal unavailability distinct from initialization failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metal = _assert_exists_and_read(METAL_EXECUTOR)
val unavailable = metal.index_of("if not metal_sffi_is_available():")
val initialization = metal.index_of(
    "if not metal_sffi_init() or metal_sffi_device_count() <= 0:")
expect(unavailable).to_be_greater_than(0)
expect(initialization).to_be_greater_than(unavailable)
expect(metal.slice(unavailable, initialization)).to_contain(
    "_processing_metal_failure(\"metal-unavailable\")")
expect(metal.slice(initialization, metal.len())).to_contain(
    "_processing_metal_failure(\"metal-init-failed\")")
```

</details>

#### returns non-owning provenance after resource cleanup

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vulkan = file_read(VULKAN_EXECUTOR)
val metal = file_read(METAL_EXECUTOR)
expect(vulkan).to_contain("val handle = device_identity")
expect(metal).to_contain("val handle = identity")
expect(vulkan.contains("val handle = buffer.handle")).to_equal(false)
expect(metal.contains("val handle = output")).to_equal(false)
```

</details>

#### releases exactly the Metal resources owned at each failure boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metal = file_read(METAL_EXECUTOR)
expect(metal).to_contain("fn _processing_metal_cleanup")
_assert_cleanup_before_boundary(metal, "if queue == 0:", "_processing_metal_cleanup(device, 0, 0, 0, 0, 0, 0, 0)", "return _processing_metal_failure(\"metal-command-queue-create-failed\")")
_assert_cleanup_before_boundary(metal, "if shader == 0:", "_processing_metal_cleanup(device, queue, 0, 0, 0, 0, 0, 0)", "return _processing_metal_failure(\"metal-shader-compile-failed\")")
_assert_cleanup_before_boundary(metal, "if pipeline == 0:", "_processing_metal_cleanup(device, queue, shader, 0, 0, 0, 0, 0)", "return _processing_metal_failure(\"metal-pipeline-create-failed\")")
val full = "_processing_metal_cleanup(device, queue, shader, pipeline, output, dummy, host, byte_count)"
_assert_cleanup_before_boundary(metal, "if output == 0 or dummy == 0 or host == 0:", full, "return _processing_metal_failure(\"metal-allocation-failed\")")
_assert_cleanup_before_boundary(metal, "if submit_fault != \"\":", full, "return _processing_metal_failure(submit_fault)")
_assert_cleanup_before_boundary(metal, "if not dispatched:", full, "return _processing_metal_failure(\"metal-dispatch-failed\")")
_assert_cleanup_before_boundary(metal, "if readback_fault != \"\":", full, "return _processing_metal_failure(readback_fault)")
_assert_cleanup_before_boundary(metal, "if not copied:", full, "return _processing_metal_failure(\"metal-readback-failed\")")
_assert_cleanup_before_boundary(metal, "if values.len().to_i64() != ir.element_count:", full, "return _processing_metal_failure(\"metal-readback-size-mismatch\")")
_assert_cleanup_before_boundary(metal, "if mismatch_fault != \"\":", full, "return _processing_metal_failure(mismatch_fault)")
_assert_cleanup_before_boundary(metal, "val handle = identity", full, "ProcessingMetalResult(completed: true")
```

</details>

#### retains reusable CUDA buffers across recoverable calls and releases them at shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = file_read(CUDA_EXECUTOR)
expect(cuda).to_contain("me _ensure_capacity(byte_count: i64) -> text:")
expect(cuda).to_contain("self.buffer_capacity >= byte_count")
expect(cuda).to_contain("self.device_buffer = replacement_device")
expect(cuda).to_contain("self.host_buffer = replacement_host")
expect(cuda).to_contain("me _release_buffers():")
expect(cuda).to_contain("me shutdown():\n        self._release_buffers()")
expect(cuda).to_contain("if not dispatch_ok:\n        executor._release_buffers()")
expect(cuda).to_contain("if not copied:\n        executor._release_buffers()")
expect(cuda.contains("_release_buffers()\n        return ProcessingCudaResult(completed: false, reason: submit_fault")).to_equal(false)
expect(cuda.contains("_release_buffers()\n        return ProcessingCudaResult(completed: false, reason: readback_fault")).to_equal(false)
```

</details>

#### retains both CUDA DB data buffers across recoverable faults

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = file_read(CUDA_DB_EXECUTOR)
expect(cuda).to_contain("me _ensure_capacity(byte_count: i64) -> text:")
expect(cuda).to_contain("self.device_input = next_device_input")
expect(cuda).to_contain("self.device_output = next_device_output")
expect(cuda).to_contain("self.host_input = next_host_input")
expect(cuda).to_contain("self.host_output = next_host_output")
expect(cuda).to_contain("me shutdown():\n        self._release_buffers()")
expect(cuda.contains("if submit_fault != \"\":\n        executor._release_buffers()")).to_equal(false)
expect(cuda.contains("if synced and readback_fault != \"\":\n        executor._release_buffers()")).to_equal(false)
```

</details>

#### releases or quarantines Vulkan dependencies before every owned return

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vulkan = file_read(VULKAN_EXECUTOR)
expect(vulkan).to_contain("device_type != \"discrete\" and device_type != \"integrated\"")
expect(vulkan).to_contain("reason: \"vulkan-physical-device-required\"")
expect(vulkan).to_contain("if dispatch_status < 0:")
expect(vulkan).to_contain("processing_ir_fault_reason(\"vulkan\", \"dispatch-ineligible\")")
_assert_cleanup_before_boundary(vulkan, "if not buffer.is_valid:", "vulkan_sffi_shutdown_reaped()", "return ProcessingVulkanResult(completed: false")
val shader_failure = "vulkan_free_buffer(buffer)\n        vulkan_sffi_shutdown_reaped()"
_assert_cleanup_before_boundary(vulkan, "if not shader.is_valid:", shader_failure, "return ProcessingVulkanResult(completed: false")
val pipeline_failure = "vulkan_destroy_shader(shader)\n        vulkan_free_buffer(buffer)\n        vulkan_sffi_shutdown_reaped()"
_assert_cleanup_before_boundary(vulkan, "if not pipeline.is_valid:", pipeline_failure, "return ProcessingVulkanResult(completed: false")
val full = "vulkan_destroy_pipeline(pipeline)\n        vulkan_destroy_shader(shader)\n        vulkan_free_buffer(buffer)\n        vulkan_sffi_shutdown_reaped()"
_assert_cleanup_before_boundary(vulkan, "if submit_fault != \"\":", full, "return ProcessingVulkanResult(completed: false")
val quarantine = "vulkan_sffi_quarantine_dependencies(0, buffer.handle, pipeline.handle, shader.handle)"
_assert_cleanup_before_boundary(vulkan, "if dispatch_status < 0:", quarantine, "return ProcessingVulkanResult(completed: false")
_assert_cleanup_before_boundary(vulkan, "if dispatch_status == 1 and readback_fault != \"\":", full, "return ProcessingVulkanResult(completed: false")
_assert_cleanup_before_boundary(vulkan, "if read and mismatch_fault != \"\":", full, "return ProcessingVulkanResult(completed: false")
val success_full = "vulkan_destroy_pipeline(pipeline)\n    vulkan_destroy_shader(shader)\n    vulkan_free_buffer(buffer)\n    vulkan_sffi_shutdown_reaped()"
_assert_cleanup_before_boundary(vulkan, "val handle = device_identity", success_full, "if not read or device_identity <= 0:")
```

</details>

#### keeps real CUDA dispatch and readback failures distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = file_read(CUDA_EXECUTOR)
expect(cuda).to_contain("reason: \"cuda-dispatch-failed\"")
expect(cuda).to_contain("reason: \"cuda-readback-failed\"")
expect(cuda.contains("cuda-dispatch-or-readback-failed")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ProcessingIR GPU executor fault source contract.
- ProcessingIR GPU executor fault source contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b8e3890c44dcbf03968d733430457584a971a2f2582a084a89cb10fc9eafd524`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8e3890c44dcbf03968d733430457584a971a2f2582a084a89cb10fc9eafd524`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8e3890c44dcbf03968d733430457584a971a2f2582a084a89cb10fc9eafd524`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl:50:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'imports the shared fault reason helper in every executor' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl:56:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'guards every init, submit, readback, and mismatch phase' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl:64:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'requires both the test gate and exact backend phase selection' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos_gpu_host/processing_ir_fault_source_contract_spec.spl:75:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'requires exact Metal success output and checksum' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
