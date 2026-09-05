# Qrb2210 Drm Kms Display Provider Specification

> Tests covering QRB2210 physical DRM KMS display provider.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qrb2210 Drm Kms Display Provider Specification

## Scenarios

### QRB2210 physical DRM KMS display provider

#### requires one complete physical scanout binding

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires one complete physical scanout binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires one complete physical scanout binding")
expect(qrb2210_drm_kms_binding_ready(binding())).to_be(true)
var no_owner = binding()
no_owner.kernel_owner_handle = 0u64
expect(qrb2210_drm_kms_binding_ready(no_owner)).to_be(false)
var render_node = binding()
render_node.device.device_node = "/dev/dri/renderD128"
expect(qrb2210_drm_kms_binding_ready(render_node)).to_be(false)
var secondary_card = binding()
secondary_card.device.device_node = "/dev/dri/card1"
expect(qrb2210_drm_kms_binding_ready(secondary_card)).to_be(false)
var malformed_primary = binding()
malformed_primary.device.device_node = "/dev/dri/card0-host"
expect(qrb2210_drm_kms_binding_ready(malformed_primary)).to_be(false)
var no_framebuffer = binding()
no_framebuffer.framebuffer_handle = 0u64
expect(qrb2210_drm_kms_binding_ready(no_framebuffer)).to_be(false)
var wrong_format = binding()
wrong_format.mode.format = "argb8888"
expect(qrb2210_drm_kms_binding_ready(wrong_format)).to_be(false)
var short_stride = binding()
short_stride.mode.stride_bytes = 7
expect(qrb2210_drm_kms_binding_ready(short_stride)).to_be(false)
```

</details>

#### binds identity to boot device owner generation framebuffer CRTC and plane

- binds identity to boot device owner generation framebuffer CRTC and plane


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("binds identity to boot device owner generation framebuffer CRTC and plane")
expect(qrb2210_drm_kms_identity_matches_binding(identity(), binding())).to_be(true)
var stale_boot = identity()
stale_boot.device.boot_id = "boot-16"
expect(qrb2210_drm_kms_identity_matches_binding(stale_boot, binding())).to_be(false)
var wrong_owner = identity()
wrong_owner.kernel_owner_handle = 52u64
expect(qrb2210_drm_kms_identity_matches_binding(wrong_owner, binding())).to_be(false)
var stale_generation = identity()
stale_generation.driver_generation = 2
expect(qrb2210_drm_kms_identity_matches_binding(stale_generation, binding())).to_be(false)
var wrong_crtc = identity()
wrong_crtc.crtc_id = 99u64
expect(qrb2210_drm_kms_identity_matches_binding(wrong_crtc, binding())).to_be(false)
var wrong_plane = identity()
wrong_plane.plane_id = 99u64
expect(qrb2210_drm_kms_identity_matches_binding(wrong_plane, binding())).to_be(false)
```

</details>

#### admits a present only for the exact Vulkan readback and scanout identity

- admits a present only for the exact Vulkan readback and scanout identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits a present only for the exact Vulkan readback and scanout identity")
expect(qrb2210_drm_kms_present_correlates(binding(), readback(), present())).to_be(true)
var wrong_frame = present()
wrong_frame.frame_id = 75
expect(qrb2210_drm_kms_present_correlates(binding(), readback(), wrong_frame)).to_be(false)
var wrong_fb = present()
wrong_fb.framebuffer_handle = 65u64
expect(qrb2210_drm_kms_present_correlates(binding(), readback(), wrong_fb)).to_be(false)
var wrong_checksum = present()
wrong_checksum.readback_checksum = 11
expect(qrb2210_drm_kms_present_correlates(binding(), readback(), wrong_checksum)).to_be(false)
var cross_boot = present()
cross_boot.device.boot_id = "boot-18"
expect(qrb2210_drm_kms_present_correlates(binding(), readback(), cross_boot)).to_be(false)
var stale_generation = present()
stale_generation.driver_generation = 2
expect(qrb2210_drm_kms_present_correlates(binding(), readback(), stale_generation)).to_be(false)
```

</details>

#### rejects replayed submission frame and present identities

- rejects replayed submission frame and present identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects replayed submission frame and present identities")
expect(qrb2210_drm_kms_present_advances(present(), 70, 71, 72)).to_be(true)
expect(qrb2210_drm_kms_present_advances(present(), 71, 71, 72)).to_be(false)
expect(qrb2210_drm_kms_present_advances(present(), 70, 72, 72)).to_be(false)
expect(qrb2210_drm_kms_present_advances(present(), 70, 71, 73)).to_be(false)
```

</details>

#### admits capture only for the exact presented framebuffer and frame

- admits capture only for the exact presented framebuffer and frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits capture only for the exact presented framebuffer and frame")
expect(qrb2210_drm_kms_capture_correlates(binding(), present(), capture())).to_be(true)
var wrong_present = capture()
wrong_present.present_id = 75
expect(qrb2210_drm_kms_capture_correlates(binding(), present(), wrong_present)).to_be(false)
var wrong_plane = capture()
wrong_plane.plane_id = 65u64
expect(qrb2210_drm_kms_capture_correlates(binding(), present(), wrong_plane)).to_be(false)
var cross_boot = capture()
cross_boot.device.boot_id = "boot-18"
expect(qrb2210_drm_kms_capture_correlates(binding(), present(), cross_boot)).to_be(false)
var incomplete = capture()
incomplete.completed = false
expect(qrb2210_drm_kms_capture_correlates(binding(), present(), incomplete)).to_be(false)
var malformed_bytes = capture()
malformed_bytes.byte_count = 15
expect(qrb2210_drm_kms_capture_correlates(binding(), present(), malformed_bytes)).to_be(false)
```

</details>

#### keeps capability promotion outside the provider and calls only kernel receipts

- keeps capability promotion outside the provider and calls only kernel receipts


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps capability promotion outside the provider and calls only kernel receipts")
val source = file_read_text(PROVIDER)
expect(source).to_contain("trait Qrb2210DrmKmsKernelPort:")
expect(source).to_contain("self.kernel.atomic_present(self.binding, readback)")
expect(source).to_contain("self.kernel.capture_scanout(self.binding, present)")
expect(source).to_contain("capture.capture_id <= self.last_capture_id")
expect(source).to_contain("not qrb2210_drm_kms_present_advances(")
expect(source).to_contain("self.last_present = nil")
expect(source).to_contain("UNO_Q_DESKTOP_STATUS_PORT_UNAVAILABLE")
expect(source.contains("uno_q_desktop_backend_status")).to_be(false)
expect(source.contains("qemu")).to_be(false)
expect(source.contains("ramfb")).to_be(false)
expect(source.contains("virtio")).to_be(false)
expect(source.contains("fallback")).to_be(false)
expect(source.contains("rt_process_run")).to_be(false)
expect(source.contains("rt_env_get")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QRB2210 physical DRM KMS display provider.
- QRB2210 physical DRM KMS display provider

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3cfd2db58e4076dbae95863e8866253d48fc1be188b30942e50f8c62bd01cc6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3cfd2db58e4076dbae95863e8866253d48fc1be188b30942e50f8c62bd01cc6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3cfd2db58e4076dbae95863e8866253d48fc1be188b30942e50f8c62bd01cc6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.spl
mirror: doc/06_spec/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires one complete physical scanout binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds identity to boot device owner generation framebuffer CRTC and plane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_drm_kms_display_provider_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a present only for the exact Vulkan readback and scanout identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
