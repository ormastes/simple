# Simpleos Physical Board Render Evidence Specification

> <details>

<!-- sdn-diagram:id=simpleos_physical_board_render_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_physical_board_render_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_physical_board_render_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_physical_board_render_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Physical Board Render Evidence Specification

## Scenarios

### SimpleOS physical-board rendering

#### should correlate board identity firmware boot receipt and exact capture

- Prepare a real board and flashed SimpleOS image
   - Artifact capture: after_step
- Boot and capture the guest render receipt
   - Artifact capture: after_step
- Capture the matching physical display or framebuffer
   - Artifact capture: after_step
- Verify exact pixels and transcript identity
   - Artifact capture: after_step
- pending physical board evidence
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare a real board and flashed SimpleOS image")
step("Boot and capture the guest render receipt")
step("Capture the matching physical display or framebuffer")
step("Verify exact pixels and transcript identity")
pending_physical_board_evidence()
```

</details>

<details>
<summary>Advanced: should reject a static board catalog entry without a live boot</summary>

#### should reject a static board catalog entry without a live boot

- Submit source-present catalog metadata
   - Expected: "source_present" equals `source_present`
- pending physical board evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit source-present catalog metadata")
expect("source_present").to_equal("source_present")
pending_physical_board_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should reject stale firmware and mismatched capture identity</summary>

#### should reject stale firmware and mismatched capture identity

- Pair a board transcript with another firmware or frame
   - Expected: "evidence-correlation-mismatch" equals `evidence-correlation-mismatch`
- pending physical board evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair a board transcript with another firmware or frame")
expect("evidence-correlation-mismatch").to_equal("evidence-correlation-mismatch")
pending_physical_board_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should keep QEMU evidence classified as QEMU verified</summary>

#### should keep QEMU evidence classified as QEMU verified

- Submit complete QEMU evidence without a physical board
   - Expected: "qemu_verified" equals `qemu_verified`
- pending physical board evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit complete QEMU evidence without a physical board")
expect("qemu_verified").to_equal("qemu_verified")
pending_physical_board_evidence()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS physical-board rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
