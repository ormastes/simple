# Qrb2210 Native 2d Composition Root Specification

> Tests covering UNO Q QRB2210 physical composition root.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qrb2210 Native 2d Composition Root Specification

## Scenarios

### UNO Q QRB2210 physical composition root

#### keeps the root blocked at the first unavailable physical owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the root blocked at the first unavailable physical owner
   - Expected: admission.missing_owner equals `display`
   - Expected: admission.reason equals `qrb2210-simpleos-port-unavailable`
   - Expected: admission.route equals `QRB2210_NATIVE_2D_ROUTE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps the root blocked at the first unavailable physical owner")
val admission = qrb2210_native_2d_composition_admission()
expect(admission.admitted).to_be(false)
expect(admission.missing_owner).to_equal("display")
expect(admission.reason).to_equal("qrb2210-simpleos-port-unavailable")
expect(admission.route).to_equal(QRB2210_NATIVE_2D_ROUTE)
```

</details>

#### defines typed display input audio submit fence and device-readback ports

- defines typed display input audio submit fence and device-readback ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines typed display input audio submit fence and device-readback ports")
val source = file_read_text(PORTS)
expect(source).to_contain("trait Qrb2210DisplayPort:")
expect(source).to_contain("trait Qrb2210InputPort:")
expect(source).to_contain("poll_device_receipt() -> Qrb2210InputDeviceReceipt?")
expect(source).to_contain("qrb2210_normalize_input_receipt")
expect(source).to_contain("qrb2210_audio_completion_correlated")
expect(source).to_contain("qrb2210_display_capture_correlated")
expect(source).to_contain("_qrb2210_physical_handles_correlate")
expect(source).to_contain("physical-provider-identity-not-correlated")
expect(source).to_contain("trait Qrb2210AudioPort:")
expect(source).to_contain("trait Qrb2210GpuSubmitPort:")
expect(source).to_contain("submit_engine2d_batch(batch: Qrb2210Engine2dSubmitBatch")
expect(source.contains("submit_draw_ir")).to_be(false)
expect(source).to_contain("trait Qrb2210GpuFencePort:")
expect(source).to_contain("trait Qrb2210DeviceReadbackPort:")
expect(source).to_contain("source: text")
```

</details>

#### binds only the canonical Engine2D Qualcomm Vulkan route

- binds only the canonical Engine2D Qualcomm Vulkan route


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("binds only the canonical Engine2D Qualcomm Vulkan route")
val source = file_read_text(ROOT)
expect(source).to_contain("engine.selected_backend_name != \"qualcomm\"")
expect(source).to_contain("backend_name() != \"qualcomm-vulkan\"")
expect(source).to_contain("vendor_id() != 0x5143")
expect(source).to_contain("qrb2210_native_2d_composition_admission()")
expect(source).to_contain("composition: DrawIrComposition")
expect(source.contains("arm64.ramfb")).to_be(false)
expect(source.contains("virtio_input")).to_be(false)
expect(source.contains("host_gpu_ivshmem")).to_be(false)
```

</details>

#### assembles only typed DRM evdev PCM and Adreno owners after admission

- assembles only typed DRM evdev PCM and Adreno owners after admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("assembles only typed DRM evdev PCM and Adreno owners after admission")
val source = file_read_text(ROOT)
expect(source).to_contain("class Qrb2210Native2dKernelOwners:")
expect(source).to_contain("drm: Qrb2210DisplayPort")
expect(source).to_contain("evdev: Qrb2210EvdevKernelPort")
expect(source).to_contain("pcm: Qrb2210AudioPort")
expect(source).to_contain("adreno: Qrb2210VulkanKernelPort")
expect(source).to_contain("val admission = qrb2210_native_2d_factory_admission()")
expect(source).to_contain("if not admission.admitted:")
expect(source).to_contain("Qrb2210EvdevInputProvider(")
expect(source).to_contain("Qrb2210VulkanGpuSubmitProvider(")
expect(source).to_contain("Qrb2210VulkanGpuFenceProvider(")
expect(source).to_contain("Qrb2210VulkanDeviceReadbackProvider(")
```

</details>

#### requires one boot and generation across physical provider identities

- requires one boot and generation across physical provider identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires one boot and generation across physical provider identities")
val display = device(QRB2210_DEVICE_DISPLAY, "/dev/dri/card0", 41u64, "boot-31", 9)
val input = device(QRB2210_DEVICE_INPUT, "/dev/input/event0", 42u64, "boot-31", 9)
val audio = device(QRB2210_DEVICE_AUDIO, "/dev/snd/pcmC0D0p", 43u64, "boot-31", 9)
val gpu = device(QRB2210_DEVICE_GPU, "/dev/dri/renderD128", 44u64, "boot-31", 9)
expect(qrb2210_native_2d_provider_identity_correlates(
    display, input, audio, gpu, 9)).to_be(true)
var stale_boot = input
stale_boot.boot_id = "boot-30"
expect(qrb2210_native_2d_provider_identity_correlates(
    display, stale_boot, audio, gpu, 9)).to_be(false)
var stale_generation = audio
stale_generation.driver_generation = 8
expect(qrb2210_native_2d_provider_identity_correlates(
    display, input, stale_generation, gpu, 9)).to_be(false)
```

</details>

#### requires the same frame through submit readback present and capture

- requires the same frame through submit readback present and capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires the same frame through submit readback present and capture")
expect(qrb2210_native_2d_frame_ids_correlate(71, 71, 71, 71, 71, 71)).to_be(true)
expect(qrb2210_native_2d_frame_ids_correlate(71, 71, 71, 72, 71, 71)).to_be(false)
expect(qrb2210_native_2d_frame_ids_correlate(71, 71, 71, 71, 72, 71)).to_be(false)
expect(qrb2210_native_2d_frame_ids_correlate(71, 71, 71, 71, 71, 72)).to_be(false)
val source = file_read_text(ROOT)
expect(source).to_contain("evidence.gpu_submit.submission_id == evidence.gpu_fence.submission_id")
expect(source).to_contain("evidence.gpu_submit.submission_id == evidence.present.submission_id")
expect(source).to_contain("evidence.gpu_submit.submission_id == evidence.input.submission_id")
expect(source).to_contain("evidence.gpu_submit.submission_id == evidence.audio_submit.submission_id")
expect(source).to_contain("_qrb2210_same_device(gpu, evidence.gpu_fence.device)")
expect(source.contains("input_frame_id")).to_be(false)
expect(source.contains("audio_frame_id")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/qrb2210_native_2d_composition_root_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UNO Q QRB2210 physical composition root.
- UNO Q QRB2210 physical composition root

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e0024b3b69e80acab834ce190cfa309f0e94a784dbbb8137636ac2a7680e0505`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e0024b3b69e80acab834ce190cfa309f0e94a784dbbb8137636ac2a7680e0505`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e0024b3b69e80acab834ce190cfa309f0e94a784dbbb8137636ac2a7680e0505`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/qrb2210_native_2d_composition_root_spec.spl
mirror: doc/06_spec/01_unit/os/port/qrb2210_native_2d_composition_root_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/qrb2210_native_2d_composition_root_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/qrb2210_native_2d_composition_root_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/qrb2210_native_2d_composition_root_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/port/qrb2210_native_2d_composition_root_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/port/qrb2210_native_2d_composition_root_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the root blocked at the first unavailable physical owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_native_2d_composition_root_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds only the canonical Engine2D Qualcomm Vulkan route' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_native_2d_composition_root_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assembles only typed DRM evdev PCM and Adreno owners after admission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
