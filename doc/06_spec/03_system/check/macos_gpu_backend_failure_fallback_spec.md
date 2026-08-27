# Macos Gpu Backend Failure Fallback Specification

> Tests covering macOS GPU backend failure and fallback receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Gpu Backend Failure Fallback Specification

## Scenarios

### macOS GPU backend failure and fallback receipts

#### uses one canonical fail-closed receipt schema for Metal and Vulkan

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses one canonical fail-closed receipt schema for Metal and Vulkan


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses one canonical fail-closed receipt schema for Metal and Vulkan")
val harness = file_read(HARNESS)
expect(harness).to_contain("fn write_failure_receipt(")
expect(harness).to_contain("if backend != \"vulkan\" and backend != \"metal\":")
expect(harness).to_contain("gpu_2d_live_status=fail")
expect(harness).to_contain("gpu_2d_live_reason={{reason}}")
expect(harness).to_contain("gpu_2d_live_backend={{backend}}")
expect(harness).to_contain("gpu_2d_live_stage={{stage}}")
expect(harness).to_contain("gpu_2d_live_exit_code={{exit_code}}")
expect(harness).to_contain("gpu_2d_live_reason=backend-create-failed")
expect(harness).to_contain("initial-device-readback-failed")
expect(harness).to_contain("interaction-device-readback-failed")
expect(harness).to_contain("shared-draw-ir-device-render-failed")
```

</details>

#### records requested and selected backends instead of hiding a fallback

- records requested and selected backends instead of hiding a fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records requested and selected backends instead of hiding a fallback")
val harness = file_read(HARNESS)
expect(harness).to_contain("val selected_backend = engine.backend_name()")
expect(harness).to_contain("gpu_2d_live_requested_backend=\" + backend")
expect(harness).to_contain("gpu_2d_live_selected_backend=\" + selected_backend")
expect(harness).to_contain("gpu_2d_live_probe=\" + probe_reason")
expect(harness).to_contain("engine.shutdown()")
expect(harness).to_contain("return 4")
expect(harness.contains("gpu_2d_live_status=pass\\n" +
    "gpu_2d_live_backend=cpu")).to_equal(false)
```

</details>

#### requires typed stage failures and rejects stale or forged passes

- requires typed stage failures and rejects stale or forged passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires typed stage failures and rejects stale or forged passes")
val harness = file_read(HARNESS)
val wrapper = file_read(WRAPPER)
for field in [
    "gpu_2d_live_status=fail\\n",
    "gpu_2d_live_reason={{reason}}\\n",
    "gpu_2d_live_backend={{backend}}\\n",
    "gpu_2d_live_stage={{stage}}\\n",
    "gpu_2d_live_exit_code={{exit_code}}\\n"
]:
    expect(harness).to_contain(field)
for reason in [
    "initial-window-present-failed",
    "interaction-window-present-failed",
    "initial-device-readback-failed",
    "interaction-device-readback-failed",
    "interaction-pixel-count-mismatch",
    "shared-draw-ir-device-render-failed"
]:
    expect(harness).to_contain(reason)
expect(harness).to_contain("gpu_2d_live_backend=\" + backend")
expect(harness).to_contain("gpu_2d_live_stage=4")
expect(harness).to_contain("gpu_2d_live_exit_code=4")
for rejection in [
    "runtime-failure-receipt-without-reason",
    "backend-mismatch",
    "repo-revision-mismatch",
    "shared-scene-fingerprint-mismatch",
    "source-revision-mismatch",
    "device-readback-missing",
    "shared-draw-ir-command-skipped",
    "shared-draw-ir-fallback-required",
    "shared-draw-ir-unsupported-command"
]:
    expect(wrapper).to_contain(rejection)
expect(wrapper).to_contain("gpu_2d_live_status")
expect(wrapper).to_contain("gpu_2d_live_backend")
expect(wrapper).to_contain("gpu_2d_live_source")
```

</details>

#### keeps strict Metal and Vulkan failures typed and explicit

- keeps strict Metal and Vulkan failures typed and explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps strict Metal and Vulkan failures typed and explicit")
val vulkan = file_read(VULKAN_STRICT)
val metal = file_read(METAL_STRICT)
expect(vulkan).to_contain("fallback_reason")
expect(vulkan).to_contain("does not silently fall back to cpu")
expect(vulkan).to_contain("create_with_backend_strict(16, 16, \"vulkan\")")
expect(metal).to_contain("fallback_reason")
expect(metal).to_contain("create_with_backend_strict(16, 16, \"metal\")")
expect(metal).to_contain("BackendStatus.Failed")
expect(metal).to_contain("BackendStatus.Unavailable")
```

</details>

#### requires bounded Metal fault children and bounded output capture

- requires bounded Metal fault children and bounded output capture
   - Expected: metal_processing does not contain `process_run("env", args)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires bounded Metal fault children and bounded output capture")
val metal_processing = file_read(METAL_PROCESSING_FAILURE)
expect(metal_processing).to_contain(
    "use std.io_runtime.{get_args, process_run_bounded}")
expect(metal_processing).to_contain(
    "val METAL_FAULT_CHILD_TIMEOUT_MS: i64 = 30000")
expect(metal_processing).to_contain(
    "val METAL_FAULT_CHILD_OUTPUT_BYTES: i64 = 4194304")
expect(metal_processing).to_contain(
    "\"env\", args, METAL_FAULT_CHILD_TIMEOUT_MS, METAL_FAULT_CHILD_OUTPUT_BYTES)")
expect(metal_processing).to_contain("err.contains(\"Process timed out\")")
expect(metal_processing).to_contain("GPU_METAL_FAULT_CHILD_TIMEOUT")
expect(metal_processing.contains("process_run(\"env\", args)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering macOS GPU backend failure and fallback receipts.
- macOS GPU backend failure and fallback receipts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `9d534033ae22f5b5a0d07f5b268c55a07cbd5092da8b87081ff090d523d8b9d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d534033ae22f5b5a0d07f5b268c55a07cbd5092da8b87081ff090d523d8b9d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d534033ae22f5b5a0d07f5b268c55a07cbd5092da8b87081ff090d523d8b9d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl
mirror: doc/06_spec/03_system/check/macos_gpu_backend_failure_fallback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/macos_gpu_backend_failure_fallback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/macos_gpu_backend_failure_fallback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses one canonical fail-closed receipt schema for Metal and Vulkan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records requested and selected backends instead of hiding a fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires typed stage failures and rejects stale or forged passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
