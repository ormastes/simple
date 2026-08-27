# Host Display Producer Adapter Specification

> Tests covering SOSIX X11 and Wayland display producer adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Display Producer Adapter Specification

## Scenarios

### SOSIX X11 and Wayland display producer adapter

#### freezes acquired host surface facts without renderer ownership

- freezes acquired host surface facts without renderer ownership
   - Expected: x11.snapshot.surface_token equals `41`
   - Expected: x11.snapshot.width equals `1920`
   - Expected: x11.snapshot.scale_milli equals `1000`
   - Expected: wayland.snapshot.backend equals `SOSIX_HOST_DISPLAY_WAYLAND`
   - Expected: wayland.snapshot.height equals `720`
   - Expected: wayland.snapshot.scale_milli equals `1250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("freezes acquired host surface facts without renderer ownership")
val x11 = sosix_host_display_snapshot_produce(
    SOSIX_HOST_DISPLAY_X11, 41, 1920, 1080, 1000)
val wayland = sosix_host_display_snapshot_produce(
    SOSIX_HOST_DISPLAY_WAYLAND, 52, 1280, 720, 1250)
expect(x11.accepted).to_be(true)
expect(x11.snapshot.surface_token).to_equal(41)
expect(x11.snapshot.width).to_equal(1920)
expect(x11.snapshot.scale_milli).to_equal(1000)
expect(wayland.accepted).to_be(true)
expect(wayland.snapshot.backend).to_equal(SOSIX_HOST_DISPLAY_WAYLAND)
expect(wayland.snapshot.height).to_equal(720)
expect(wayland.snapshot.scale_milli).to_equal(1250)
```

</details>

#### rejects unusable platform facts before publication

- rejects unusable platform facts before publication


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects unusable platform facts before publication")
expect(sosix_host_display_snapshot_produce(
    99, 1, 640, 480, 1000).reason).to_equal("unsupported-display-backend")
expect(sosix_host_display_snapshot_produce(
    SOSIX_HOST_DISPLAY_X11, 0, 640, 480, 1000).reason).to_equal("invalid-display-surface")
expect(sosix_host_display_snapshot_produce(
    SOSIX_HOST_DISPLAY_WAYLAND, 1, 0, 480, 1000).reason).to_equal("invalid-display-extent")
expect(sosix_host_display_snapshot_produce(
    SOSIX_HOST_DISPLAY_WAYLAND, 1, 640, 480, 0).reason).to_equal("invalid-display-scale")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/host_display_producer_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SOSIX X11 and Wayland display producer adapter.
- SOSIX X11 and Wayland display producer adapter

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6bb879c74d7f54bae5e3957a05c4ccfbd0d9ea2d8075ecd43c7432e5a9e09b39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6bb879c74d7f54bae5e3957a05c4ccfbd0d9ea2d8075ecd43c7432e5a9e09b39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6bb879c74d7f54bae5e3957a05c4ccfbd0d9ea2d8075ecd43c7432e5a9e09b39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/sosix/host_display_producer_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/host_display_producer_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/host_display_producer_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/host_display_producer_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/host_display_producer_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/host_display_producer_adapter_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'freezes acquired host surface facts without renderer ownership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/host_display_producer_adapter_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unusable platform facts before publication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
