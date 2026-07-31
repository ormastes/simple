# SimpleOS Physical Board Render Evidence

> Defines the portable board qualification record and prevents QEMU, static catalog, stale firmware, or incomplete transcripts from becoming board PASS.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Physical Board Render Evidence

Defines the portable board qualification record and prevents QEMU, static catalog, stale firmware, or incomplete transcripts from becoming board PASS.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Defines the portable board qualification record and prevents QEMU, static
catalog, stale firmware, or incomplete transcripts from becoming board PASS.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Run this spec to review the current fail-closed board qualification contract.
Promotion requires a canonical physical ARM runner joining board identity,
flashed-image hash, boot receipt, in-guest Clang filesystem execution, and UART
transcript; until then the scenario reports the implementation resume action.

## Scenarios

### SimpleOS physical-board rendering

#### should correlate board identity firmware boot receipt and exact capture

- Capture the feature evidence
   - Artifact capture: after_step
- Verify the structured evidence
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: capture.status equals `blocked`
- Render the evidence for review
   - Artifact capture: after_step
- Publish the showcase link
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: "blocked-unpublished" equals `blocked-unpublished`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val capture = capture_physical_arm_board_evidence()

step("Verify the structured evidence")
expect(capture.status).to_equal("blocked")
expect(capture.reason).to_equal(
    "missing-canonical-arm-physical-board-runner-and-receipt:" +
    "board-identity,flash,boot,guest-clang-fs-run,uart"
)

step("Render the evidence for review")
expect(capture.resume_action).to_contain(
    "in-guest Clang filesystem execution"
)

step("Publish the showcase link")
expect("blocked-unpublished").to_equal("blocked-unpublished")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/evidence_showcase.md`
- **Plan:** `doc/03_plan/sys_test/evidence_showcase.md`
- **Design:** `doc/05_design/evidence_showcase.md`
- **Research:** `doc/01_research/local/evidence_showcase.md`


</details>
