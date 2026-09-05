# Render 8k80 Cuda Vulkan Container Readiness Specification

> Tests covering 8K80 CUDA and Vulkan container readiness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render 8k80 Cuda Vulkan Container Readiness Specification

## Scenarios

### 8K80 CUDA and Vulkan container readiness

#### prepares a reproducible NVIDIA image without a Mesa substitute

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prepares a reproducible NVIDIA image without a Mesa substitute
- Check the hardware-free campaign image contract
   - Expected: code equals `0`
   - Expected: err equals ``
- Require immutable inputs and an immutable output identity
- Reject Mesa as an NVIDIA Vulkan substitute


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prepares a reproducible NVIDIA image without a Mesa substitute")
step("Check the hardware-free campaign image contract")
val (out, err, code) = process_run_bounded(
    "sh",
    ["test/05_perf/profile_scripts/render_perf_8k80_container_image_contract_test.shs"],
    30000, 1048576)
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain(
    "render_perf_8k80_container_image_contract=true")
step("Require immutable inputs and an immutable output identity")
val setup = file_read_text(
    "scripts/setup/prepare-render-perf-8k80-container.shs")
expect(setup).to_contain("base-image-must-use-sha256-digest")
expect(setup).to_contain("image inspect --format '{{.Id}}'")
expect(setup).to_contain(
    "NVIDIA_DRIVER_CAPABILITIES=compute,utility,graphics")
step("Reject Mesa as an NVIDIA Vulkan substitute")
val dockerfile = file_read_text(
    "tools/docker/Dockerfile.render-8k80-nvidia")
expect(dockerfile).to_contain("vulkan-tools")
expect(dockerfile).to_contain("command -v /usr/bin/time")
expect(dockerfile).to_contain("mesa-vulkan-drivers")
```

</details>

#### requests the NVIDIA capabilities needed by both APIs

- requests the NVIDIA capabilities needed by both APIs
- Execute the hardware-free parent-authoritative contract matrix
   - Expected: code equals `0`
   - Expected: err equals ``
- Inspect the bounded GPU container contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requests the NVIDIA capabilities needed by both APIs")
step("Execute the hardware-free parent-authoritative contract matrix")
val (out, err, code) = process_run_bounded(
    "sh",
    ["test/05_perf/profile_scripts/render_perf_8k80_container_contract_test.shs"],
    30000, 1048576)
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("render_perf_8k80_container_contract=true")
step("Inspect the bounded GPU container contract")
val source = file_read_text(
    "scripts/check/check-render-perf-8k80-container.shs")
expect(source).to_contain(
    "NVIDIA_DRIVER_CAPABILITIES=compute,utility,graphics")
expect(source).to_contain("--gpus \"$gpu_flag\"")
expect(source).to_contain("--network=none")
expect(source).to_contain("--cap-drop=ALL")
expect(source).to_contain("--security-opt=no-new-privileges")
```

</details>

#### keeps CUDA and Vulkan execution evidence distinct

- keeps CUDA and Vulkan execution evidence distinct
- Require CUDA submit and readback qualification
- Require a separate strict Vulkan semantic receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps CUDA and Vulkan execution evidence distinct")
step("Require CUDA submit and readback qualification")
val source = file_read_text(
    "scripts/check/check-render-perf-8k80-container.shs")
expect(source).to_contain(
    "sh scripts/check/check-cuda-generated-2d-readback.shs")
expect(source).to_contain("validate_cuda_qualification")
step("Require a separate strict Vulkan semantic receipt")
expect(source).to_contain(
    "producer_receipt_requested_backend)\" = vulkan")
expect(source).to_contain(
    "producer_receipt_selected_backend)\" = vulkan")
expect(source).to_contain(
    "producer_receipt_readback_source)\" = device_readback")
```

</details>

#### retains inventory without treating enumeration as execution

- retains inventory without treating enumeration as execution
- Retain CUDA and Vulkan device inventory
- Keep strict submission and device readback as the Vulkan oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retains inventory without treating enumeration as execution")
step("Retain CUDA and Vulkan device inventory")
val source = file_read_text(
    "scripts/check/check-render-perf-8k80-container.shs")
expect(source).to_contain("vulkaninfo --summary")
expect(source).to_contain("gpu-inventory/cuda-vulkan.txt")
expect(source).to_contain(
    "cp -R \"$run/gpu-inventory\" \"$run/publish/gpu-inventory\"")
step("Keep strict submission and device readback as the Vulkan oracle")
expect(source).to_contain("producer-container-execution")
expect(source).to_contain("producer_receipt_completion_known")
expect(source).to_contain("producer_receipt_device_submit_count")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering 8K80 CUDA and Vulkan container readiness.
- 8K80 CUDA and Vulkan container readiness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-R8KC-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f8bc27591b719b85423ad5b5724d8ff7ef9bab97fc218fb103a62ca0e29e9aab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8bc27591b719b85423ad5b5724d8ff7ef9bab97fc218fb103a62ca0e29e9aab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8bc27591b719b85423ad5b5724d8ff7ef9bab97fc218fb103a62ca0e29e9aab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prepares a reproducible NVIDIA image without a Mesa substitute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requests the NVIDIA capabilities needed by both APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps CUDA and Vulkan execution evidence distinct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
