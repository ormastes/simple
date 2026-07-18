# Simpleos Wm Fullscreen Specification

> <details>

<!-- sdn-diagram:id=simpleos_wm_fullscreen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wm_fullscreen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wm_fullscreen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wm_fullscreen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wm Fullscreen Specification

## Scenarios

### SimpleOS production WM fullscreen

#### should boot at detected full scanout and preserve live state across input-driven maximize and restore

- Boot the production pure-Simple SimpleOS image in QEMU
   - Artifact capture: after_step
- Wait for the live desktop at the detected framebuffer scanout
   - Artifact capture: after_step
- Capture the baseline framebuffer through QMP
   - Artifact capture: after_step
- Submit maximize through the QEMU emulated input device
   - Artifact capture: after_step
- Observe the guest input IRQ driver and WM revision sequence
   - Artifact capture: after_step
- Capture the maximized framebuffer through QMP
   - Artifact capture: after_step
- Submit restore through the QEMU emulated input device
   - Artifact capture: after_step
- Capture the restored framebuffer through QMP
   - Artifact capture: after_step
- Validate semantic pixels hashes metadata and backend provenance
   - Artifact capture: after_step
- Verify production boot and dynamic detected scanout metadata
   - Artifact capture: after_step
- Verify the emulated input device IRQ and correlated revision path
   - Artifact capture: after_step
- Verify maximize and restore preserve every non-target state field
   - Artifact capture: after_step
- Verify shared taskbar top lane Simple GUI Web and 2D provenance
   - Artifact capture: after_step
- Verify all three framebuffer captures and their correlated hashes
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the production pure-Simple SimpleOS image in QEMU")
step("Wait for the live desktop at the detected framebuffer scanout")
step("Capture the baseline framebuffer through QMP")
step("Submit maximize through the QEMU emulated input device")
step("Observe the guest input IRQ driver and WM revision sequence")
step("Capture the maximized framebuffer through QMP")
step("Submit restore through the QEMU emulated input device")
step("Capture the restored framebuffer through QMP")
step("Validate semantic pixels hashes metadata and backend provenance")
require_production_qemu_boot_and_dynamic_scanout()
require_emulated_input_irq_revision_path()
require_live_maximize_restore_state_preservation()
require_shared_render_and_content_provenance()
require_three_verified_framebuffer_captures()
```

</details>

<details>
<summary>Advanced: should reject early exit timeout or an uncorrelated emulated input path</summary>

#### should reject early exit timeout or an uncorrelated emulated input path

- boot production simpleos desktop
   - Protocol capture: after_step
- Interrupt boot input delivery IRQ acknowledgement or frame production
   - Protocol capture: after_step
- require fail closed qemu lifecycle
   - Protocol capture: after_step
- require emulated input irq revision path
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
step("Interrupt boot input delivery IRQ acknowledgement or frame production")
require_fail_closed_qemu_lifecycle()
require_emulated_input_irq_revision_path()
```

</details>


</details>

<details>
<summary>Advanced: should reject invalid fixed stale or mismatched framebuffer metadata</summary>

#### should reject invalid fixed stale or mismatched framebuffer metadata

- boot production simpleos desktop
   - Artifact capture: after_step
- Replace detected scanout metadata with invalid or mismatched values
   - Artifact capture: after_step
- Validate semantic pixels hashes metadata and backend provenance
   - Artifact capture: after_step
- require fail closed scanout metadata
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
step("Replace detected scanout metadata with invalid or mismatched values")
step("Validate semantic pixels hashes metadata and backend provenance")
require_fail_closed_scanout_metadata()
```

</details>


</details>

<details>
<summary>Advanced: should reject missing partial stale blank or unverifiable framebuffer captures</summary>

#### should reject missing partial stale blank or unverifiable framebuffer captures

- boot production simpleos desktop
   - Artifact capture: after_step
- validate three correlated captures
   - Artifact capture: after_step
- Remove or corrupt capture identity freshness metadata pixels or hash
   - Artifact capture: after_step
- require fail closed capture contract
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
validate_three_correlated_captures()
step("Remove or corrupt capture identity freshness metadata pixels or hash")
require_fail_closed_capture_contract()
```

</details>


</details>

<details>
<summary>Advanced: should reject demo source-only seed or fabricated render provenance</summary>

#### should reject demo source-only seed or fabricated render provenance

- boot production simpleos desktop
   - Protocol capture: after_step
- Substitute demo markers fixed scenes source inspection seed execution or silent renderer fallback
   - Protocol capture: after_step
- Validate semantic pixels hashes metadata and backend provenance
   - Protocol capture: after_step
- require shared render and content provenance
   - Protocol capture: after_step
- require performance row provenance
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
step("Substitute demo markers fixed scenes source inspection seed execution or silent renderer fallback")
step("Validate semantic pixels hashes metadata and backend provenance")
require_shared_render_and_content_provenance()
require_performance_row_provenance()
```

</details>


</details>

<details>
<summary>Advanced: should keep emulated input to matching framebuffer generation at or below 500 milliseconds p95</summary>

#### should keep emulated input to matching framebuffer generation at or below 500 milliseconds p95

- boot production simpleos desktop
   - Artifact capture: after_step
- Discard setup activity and submit 30 maximize restore input pairs at idle load
   - Artifact capture: after_step
- Correlate every input submission with its matching framebuffer generation
   - Artifact capture: after_step
- Calculate nearest-rank p95 from monotonic-clock durations
   - Artifact capture: after_step
- require qemu input latency budget
   - Artifact capture: after_step
- require performance row provenance
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_production_simpleos_desktop()
step("Discard setup activity and submit 30 maximize restore input pairs at idle load")
step("Correlate every input submission with its matching framebuffer generation")
step("Calculate nearest-rank p95 from monotonic-clock durations")
require_qemu_input_latency_budget()
require_performance_row_provenance()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl` |
| Updated | 2026-07-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS production WM fullscreen

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
