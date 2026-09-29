# Vulkan Direct Compute Ownership Contract Specification

> Tests covering Vulkan direct compute ownership contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Direct Compute Ownership Contract Specification

## Scenarios

### Vulkan direct compute ownership contract

#### passes owned buffer arcs into direct execution and quarantine

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes owned buffer arcs into direct execution and quarantine
   - Expected: pipeline does not contain `std::mem::forget(fence)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("passes owned buffer arcs into direct execution and quarantine")
val pipeline = file_read("src/compiler_rust/runtime/src/vulkan/pipeline.rs").replace("\r\n", "\n")
val kernel = file_read("src/compiler_rust/runtime/src/value/gpu_vulkan/vulkan_sffi/kernel.rs").replace("\r\n", "\n")

expect(pipeline).to_contain("self: &Arc<Self>")
expect(pipeline).to_contain("buffers.to_vec()")
expect(pipeline).to_contain("Arc::clone(self)")
expect(pipeline.contains("std::mem::forget(fence)")).to_equal(false)
expect(kernel).to_contain("pipeline.execute(&buffers")
```

</details>

#### blocks unknown compute work and reaps only after device idle

- blocks unknown compute work and reaps only after device idle
   - Expected: buffer.count("self.device.ensure_buffer_io_available()?") equals `2`
   - Expected: buffer.count("self.device.direct_compute_gate().lock()") equals `2`
   - Expected: image.count("self.device.ensure_buffer_io_available()?") equals `2`
   - Expected: image.count("self.device.direct_compute_gate().lock()") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("blocks unknown compute work and reaps only after device idle")
val device = file_read("src/compiler_rust/runtime/src/vulkan/device.rs").replace("\r\n", "\n")
val buffer = file_read("src/compiler_rust/runtime/src/vulkan/buffer.rs").replace("\r\n", "\n")
val image = file_read("src/compiler_rust/runtime/src/vulkan/image.rs").replace("\r\n", "\n")

expect(device).to_contain("struct DirectComputeSubmission")
expect(device).to_contain("pipeline: Arc<ComputePipeline>")
expect(device).to_contain("fence: Fence")
expect(device).to_contain("command_buffer: vk::CommandBuffer")
expect(device).to_contain("buffers: Vec<Arc<VulkanBuffer>>")
expect(device).to_contain("self.reap_direct_compute_submissions()")
expect(device).to_contain("let _direct_compute = self.direct_compute_gate.lock()")
expect(device).to_contain("if !submission.pipeline.recover_after_device_idle()")
expect(device).to_contain("*self.direct_compute_quarantine.lock() = pending")
expect(device).to_contain("direct compute descriptor recovery failed")
expect(device).to_contain("self.ensure_direct_compute_available()")
expect(device).to_contain("submit_definitely_not_accepted")
expect(device).to_contain("NotSubmitted(VulkanError::CommandBufferError")
expect(buffer.count("self.device.ensure_buffer_io_available()?")).to_equal(2)
expect(buffer.count("self.device.direct_compute_gate().lock()")).to_equal(2)
expect(image.count("self.device.ensure_buffer_io_available()?")).to_equal(2)
expect(image.count("self.device.direct_compute_gate().lock()")).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/check/vulkan_direct_compute_ownership_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan direct compute ownership contract.
- Vulkan direct compute ownership contract

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

- `REQ-SSPEC-CHECK`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cddf3ed09f579675e8af98828ce8e2df2c5c8c76a5dc101db2fd34adec8b5ce8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cddf3ed09f579675e8af98828ce8e2df2c5c8c76a5dc101db2fd34adec8b5ce8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cddf3ed09f579675e8af98828ce8e2df2c5c8c76a5dc101db2fd34adec8b5ce8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/check/vulkan_direct_compute_ownership_contract_spec.spl
mirror: doc/06_spec/01_unit/check/vulkan_direct_compute_ownership_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/check/vulkan_direct_compute_ownership_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/check/vulkan_direct_compute_ownership_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/check/vulkan_direct_compute_ownership_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/check/vulkan_direct_compute_ownership_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes owned buffer arcs into direct execution and quarantine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/check/vulkan_direct_compute_ownership_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks unknown compute work and reaps only after device idle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
