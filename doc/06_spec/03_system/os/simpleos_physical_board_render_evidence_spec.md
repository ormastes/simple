# SimpleOS Physical Board Render Evidence

> Defines the portable board qualification record and prevents QEMU, static

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Physical Board Render Evidence

Defines the portable board qualification record and prevents QEMU, static

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Defines the portable board qualification record and prevents QEMU, static
catalog, stale firmware, or incomplete transcripts from becoming board PASS.

## Scenarios

### SimpleOS physical-board rendering

#### should correlate board identity firmware boot receipt and exact capture

- should correlate board identity firmware boot receipt and exact capture
   - Artifact capture: after_step
- Prepare a real board and flashed SimpleOS image
   - Artifact capture: after_step
- Boot and capture the guest render receipt
   - Artifact capture: after_step
- Capture the matching physical display or framebuffer
   - Artifact capture: after_step
- Verify exact pixels and transcript identity
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should correlate board identity firmware boot receipt and exact capture")
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

- should reject a static board catalog entry without a live boot
- Submit source-present catalog metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a static board catalog entry without a live boot")
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

- should reject stale firmware and mismatched capture identity
- Pair a board transcript with another firmware or frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject stale firmware and mismatched capture identity")
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

- should keep QEMU evidence classified as QEMU verified
- Submit complete QEMU evidence without a physical board
   - Expected: simpleos_render_target_status(evidence) equals `qemu-verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep QEMU evidence classified as QEMU verified")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-018`
- `REQ-019`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f998c3539c1d7ce6b62894f921308e5bb2ca67ce27b578bc319de60708cc687`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f998c3539c1d7ce6b62894f921308e5bb2ca67ce27b578bc319de60708cc687`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f998c3539c1d7ce6b62894f921308e5bb2ca67ce27b578bc319de60708cc687`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos_physical_board_render_evidence_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_physical_board_render_evidence_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=80 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos_physical_board_render_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_physical_board_render_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_physical_board_render_evidence_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/simpleos_physical_board_render_evidence_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should correlate board identity firmware boot receipt and exact capture' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_physical_board_render_evidence_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a static board catalog entry without a live boot' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_physical_board_render_evidence_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject stale firmware and mismatched capture identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_physical_board_render_evidence_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep QEMU evidence classified as QEMU verified' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
