# Qrb2210 Vulkan Primitive Provider Specification

> Tests covering QRB2210 physical Vulkan primitive provider.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qrb2210 Vulkan Primitive Provider Specification

## Scenarios

### QRB2210 physical Vulkan primitive provider

#### requires every kernel-owned Vulkan resource handle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires every kernel-owned Vulkan resource handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires every kernel-owned Vulkan resource handle")
expect(qrb2210_vulkan_binding_has_kernel_handles(binding(11u64, 12u64, 13u64, 14u64))).to_be(true)
expect(qrb2210_vulkan_binding_has_kernel_handles(binding(0u64, 12u64, 13u64, 14u64))).to_be(false)
expect(qrb2210_vulkan_binding_has_kernel_handles(binding(11u64, 0u64, 13u64, 14u64))).to_be(false)
expect(qrb2210_vulkan_binding_has_kernel_handles(binding(11u64, 12u64, 0u64, 14u64))).to_be(false)
expect(qrb2210_vulkan_binding_has_kernel_handles(binding(11u64, 12u64, 13u64, 0u64))).to_be(false)
var missing_firmware = binding(11u64, 12u64, 13u64, 14u64)
missing_firmware.firmware_handle = 0u64
expect(qrb2210_vulkan_binding_has_kernel_handles(missing_firmware)).to_be(false)
var missing_mmu = binding(11u64, 12u64, 13u64, 14u64)
missing_mmu.mmu_context_handle = 0u64
expect(qrb2210_vulkan_binding_has_kernel_handles(missing_mmu)).to_be(false)
var missing_cache = binding(11u64, 12u64, 13u64, 14u64)
missing_cache.cache_domain_handle = 0u64
expect(qrb2210_vulkan_binding_has_kernel_handles(missing_cache)).to_be(false)
var missing_pool = binding(11u64, 12u64, 13u64, 14u64)
missing_pool.command_pool_handle = 0u64
expect(qrb2210_vulkan_binding_has_kernel_handles(missing_pool)).to_be(false)
```

</details>

#### admits only matching physical QRB2210 Qualcomm Adreno identity

- admits only matching physical QRB2210 Qualcomm Adreno identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits only matching physical QRB2210 Qualcomm Adreno identity")
val resources = binding(11u64, 12u64, 13u64, 14u64)
expect(qrb2210_vulkan_identity_matches_binding(identity(11u64, 12u64, true), resources)).to_be(true)
expect(qrb2210_vulkan_identity_matches_binding(identity(11u64, 12u64, false), resources)).to_be(false)
expect(qrb2210_vulkan_identity_matches_binding(identity(21u64, 12u64, true), resources)).to_be(false)
expect(qrb2210_vulkan_identity_matches_binding(identity(11u64, 22u64, true), resources)).to_be(false)
var stale_boot = identity(11u64, 12u64, true)
stale_boot.boot_id = "boot-16"
expect(qrb2210_vulkan_identity_matches_binding(stale_boot, resources)).to_be(false)
var stale_generation = identity(11u64, 12u64, true)
stale_generation.driver_generation = 2
expect(qrb2210_vulkan_identity_matches_binding(stale_generation, resources)).to_be(false)
```

</details>

#### wires submit fence and device-memory readback without fallback

- wires submit fence and device-memory readback without fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("wires submit fence and device-memory readback without fallback")
val source = file_read_text(PROVIDER)
expect(source).to_contain("trait Qrb2210VulkanKernelPort:")
expect(source).to_contain("self.binding, batch.frame_id, batch.command_buffer_handle")
expect(source).to_contain("self.binding, submission_id, QRB2210_FENCE_TIMEOUT_NS")
expect(source).to_contain("self.binding, submission_id, frame_id, width, height")
expect(source).to_contain("receipt.command_buffer_handle == batch.command_buffer_handle")
expect(source).to_contain("receipt.driver_generation == self.binding.device.driver_generation")
expect(source).to_contain("receipt.readback_handle == self.binding.readback_handle")
expect(source).to_contain("receipt.queue_handle == self.binding.queue_handle")
expect(source).to_contain("receipt.fence_handle == self.binding.fence_handle")
expect(source).to_contain("qrb2210-vulkan-device-memory")
expect(source).to_contain("UNO_Q_DESKTOP_STATUS_PORT_UNAVAILABLE")
expect(source.contains("host_gpu")).to_be(false)
expect(source.contains("android")).to_be(false)
expect(source.contains("virtio")).to_be(false)
expect(source.contains("software")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QRB2210 physical Vulkan primitive provider.
- QRB2210 physical Vulkan primitive provider

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87881a169ebb90e5e462f2777ca2b9debb2664084aa06b36846060e66c5f85bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87881a169ebb90e5e462f2777ca2b9debb2664084aa06b36846060e66c5f85bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87881a169ebb90e5e462f2777ca2b9debb2664084aa06b36846060e66c5f85bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.spl
mirror: doc/06_spec/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires every kernel-owned Vulkan resource handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only matching physical QRB2210 Qualcomm Adreno identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_vulkan_primitive_provider_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wires submit fence and device-memory readback without fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
