# Qrb2210 Adreno Vulkan Kernel Transport Specification

> Tests covering QRB2210 Adreno Vulkan kernel transport owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qrb2210 Adreno Vulkan Kernel Transport Specification

## Scenarios

### QRB2210 Adreno Vulkan kernel transport owner

#### binds one exact physical resource identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds one exact physical resource identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("binds one exact physical resource identity")
val owned = binding()
expect(qrb2210_adreno_binding_matches(owned, owned)).to_be(true)
var stale_boot = binding()
stale_boot.device.boot_id = "boot-16"
expect(qrb2210_adreno_binding_matches(stale_boot, owned)).to_be(false)
var wrong_firmware = binding()
wrong_firmware.firmware_handle = 999u64
expect(qrb2210_adreno_binding_matches(wrong_firmware, owned)).to_be(false)
var wrong_mmu = binding()
wrong_mmu.mmu_context_handle = 999u64
expect(qrb2210_adreno_binding_matches(wrong_mmu, owned)).to_be(false)
var wrong_cache = binding()
wrong_cache.cache_domain_handle = 999u64
expect(qrb2210_adreno_binding_matches(wrong_cache, owned)).to_be(false)
var wrong_queue = binding()
wrong_queue.queue_handle = 999u64
expect(qrb2210_adreno_binding_matches(wrong_queue, owned)).to_be(false)
```

</details>

#### rejects replay and command substitution at submit

- rejects replay and command substitution at submit


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects replay and command substitution at submit")
expect(qrb2210_adreno_submit_correlates(binding(), 9, 201u64, submit(), 40)).to_be(true)
expect(qrb2210_adreno_submit_correlates(binding(), 9, 201u64, submit(), 41)).to_be(false)
expect(qrb2210_adreno_submit_correlates(binding(), 10, 201u64, submit(), 40)).to_be(false)
expect(qrb2210_adreno_submit_correlates(binding(), 9, 202u64, submit(), 40)).to_be(false)
var wrong_generation = submit()
wrong_generation.driver_generation = 2
expect(qrb2210_adreno_submit_correlates(binding(), 9, 201u64, wrong_generation, 40)).to_be(false)
```

</details>

#### requires the exact command and fence completion

- requires the exact command and fence completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires the exact command and fence completion")
expect(qrb2210_adreno_fence_correlates(binding(), 41, 9, 201u64, fence())).to_be(true)
expect(qrb2210_adreno_fence_correlates(binding(), 42, 9, 201u64, fence())).to_be(false)
expect(qrb2210_adreno_fence_correlates(binding(), 41, 10, 201u64, fence())).to_be(false)
var wrong_command = fence()
wrong_command.command_buffer_handle = 202u64
expect(qrb2210_adreno_fence_correlates(binding(), 41, 9, 201u64, wrong_command)).to_be(false)
var incomplete = fence()
incomplete.completed = false
expect(qrb2210_adreno_fence_correlates(binding(), 41, 9, 201u64, incomplete)).to_be(false)
expect(qrb2210_adreno_fence_is_fresh(41, 41, 0)).to_be(true)
expect(qrb2210_adreno_fence_is_fresh(41, 41, 41)).to_be(false)
expect(qrb2210_adreno_fence_is_fresh(40, 41, 0)).to_be(false)
```

</details>

#### requires exact device readback generation and frame identity

- requires exact device readback generation and frame identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires exact device readback generation and frame identity")
expect(qrb2210_adreno_readback_correlates(
    binding(), 41, 9, 201u64, 2, 2, readback())).to_be(true)
expect(qrb2210_adreno_readback_correlates(
    binding(), 41, 10, 201u64, 2, 2, readback())).to_be(false)
var wrong_readback = readback()
wrong_readback.readback_handle = 99u64
expect(qrb2210_adreno_readback_correlates(
    binding(), 41, 9, 201u64, 2, 2, wrong_readback)).to_be(false)
var wrong_device = readback()
wrong_device.device_handle = 99u64
expect(qrb2210_adreno_readback_correlates(
    binding(), 41, 9, 201u64, 2, 2, wrong_device)).to_be(false)
var short_pixels = readback()
short_pixels.pixels = [1u32, 2u32, 3u32]
expect(qrb2210_adreno_readback_correlates(
    binding(), 41, 9, 201u64, 2, 2, short_pixels)).to_be(false)
var wrong_source = readback()
wrong_source.source = "cpu-copy"
expect(qrb2210_adreno_readback_correlates(
    binding(), 41, 9, 201u64, 2, 2, wrong_source)).to_be(false)
var wrong_queue = readback()
wrong_queue.queue_handle = 99u64
expect(qrb2210_adreno_readback_correlates(
    binding(), 41, 9, 201u64, 2, 2, wrong_queue)).to_be(false)
var wrong_fence = readback()
wrong_fence.fence_handle = 99u64
expect(qrb2210_adreno_readback_correlates(
    binding(), 41, 9, 201u64, 2, 2, wrong_fence)).to_be(false)
```

</details>

#### owns transport only and cannot promote capability or render privately

- owns transport only and cannot promote capability or render privately


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("owns transport only and cannot promote capability or render privately")
val source = file_read_text(OWNER)
expect(source).to_contain("impl Qrb2210VulkanKernelPort")
expect(source).to_contain("submission_id != self.last_fence_submission_id")
expect(source).to_contain("frame_id <= self.last_readback_frame_id")
expect(source).to_contain("qrb2210_adreno_fence_is_fresh")
expect(source.contains("uno_q_desktop_set")).to_be(false)
expect(source.contains("DrawIrComposition")).to_be(false)
expect(source.contains("Engine2D")).to_be(false)
expect(source.contains("android")).to_be(false)
expect(source.contains("adb")).to_be(false)
expect(source.contains("virtio")).to_be(false)
expect(source.contains("software")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QRB2210 Adreno Vulkan kernel transport owner.
- QRB2210 Adreno Vulkan kernel transport owner

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b336805795e72f567cf3056a94b1a1688c58a2381b6fa4dd73d47d1c9b061a7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b336805795e72f567cf3056a94b1a1688c58a2381b6fa4dd73d47d1c9b061a7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b336805795e72f567cf3056a94b1a1688c58a2381b6fa4dd73d47d1c9b061a7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.spl
mirror: doc/06_spec/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds one exact physical resource identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects replay and command substitution at submit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_adreno_vulkan_kernel_transport_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the exact command and fence completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
