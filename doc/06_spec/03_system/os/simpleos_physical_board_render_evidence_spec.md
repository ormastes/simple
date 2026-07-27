# Simpleos Physical Board Render Evidence Specification

> <details>

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
- require live physical board evidence
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
require_live_physical_board_evidence()
```

</details>

<details>
<summary>Advanced: should reject a static board catalog entry without a live boot</summary>

#### should reject a static board catalog entry without a live boot

- Submit source-present catalog metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit source-present catalog metadata")
val evidence = simpleos_target_evidence(
    "physical-board", "aarch64", "", "", "boot-1", "frame-1",
    SIMPLEOS_EVIDENCE_HASH, 0)
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal(
    "missing-board-identity")
```

</details>


</details>

<details>
<summary>Advanced: should reject stale firmware and mismatched capture identity</summary>

#### should reject stale firmware and mismatched capture identity

- Pair a board transcript with another firmware or frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair a board transcript with another firmware or frame")
val evidence = simpleos_target_evidence(
    "physical-board", "aarch64", "kv260-1", SIMPLEOS_EVIDENCE_HASH,
    "boot-1", "frame-2", SIMPLEOS_EVIDENCE_HASH, 0)
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal(
    "frame-correlation-mismatch")
```

</details>


</details>

<details>
<summary>Advanced: should keep QEMU evidence classified as QEMU verified</summary>

#### should keep QEMU evidence classified as QEMU verified

- Submit complete QEMU evidence without a physical board
   - Expected: simpleos_render_target_status(evidence) equals `qemu-verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit complete QEMU evidence without a physical board")
val evidence = simpleos_target_evidence(
    "qemu", "aarch64", "", "", "boot-1", "frame-1",
    SIMPLEOS_EVIDENCE_HASH, 0)
expect(simpleos_render_target_status(evidence)).to_equal("qemu-verified")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl` |
| Updated | 2026-07-27 |
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
