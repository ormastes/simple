# Hosted Wm Capture Evidence Specification

> Tests covering hosted WM capture evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Wm Capture Evidence Specification

## Scenarios

### hosted WM capture evidence

#### draws bounded text into the hosted framebuffer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- draws bounded text into the hosted framebuffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draws bounded text into the hosted framebuffer")
val fb = HostedCaptureFramebuffer.with_color(48, 24, 0xFF000000u32)
fb.draw_text(0, 0, "AB", 0xFFFFFFFFu32, 0xFF000000u32)
var lit = 0
var i = 0
while i < fb.pixels.len():
    if fb.pixels[i] != 0xFF000000u32:
        lit = lit + 1
    i = i + 1
expect(lit).to_be_greater_than(0)
```

</details>

#### captures nonblank shared hosted WM metrics without a file output

- captures nonblank shared hosted WM metrics without a file output
   - Expected: metrics.write_ok is true
   - Expected: metrics.width equals `HOSTED_WM_CROP_WIDTH`
   - Expected: metrics.height equals `HOSTED_WM_CROP_HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures nonblank shared hosted WM metrics without a file output")
val metrics = capture_shared_hosted_wm_frame("")
expect(metrics.write_ok).to_equal(true)
expect(metrics.width).to_equal(HOSTED_WM_CROP_WIDTH)
expect(metrics.height).to_equal(HOSTED_WM_CROP_HEIGHT)
expect(metrics.non_background_pixels).to_be_greater_than(0)
expect(metrics.bright_pixels).to_be_greater_than(0)
expect(metrics.sample_checksum).to_not_equal(0u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/hosted_wm_capture_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted WM capture evidence.
- hosted WM capture evidence

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `401bb78e73233c9004fc92ba73375446673f2cf757ef9eceff96474f5b58bf09`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `401bb78e73233c9004fc92ba73375446673f2cf757ef9eceff96474f5b58bf09`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `401bb78e73233c9004fc92ba73375446673f2cf757ef9eceff96474f5b58bf09`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/os/compositor/hosted_wm_capture_evidence_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/hosted_wm_capture_evidence_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/hosted_wm_capture_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/hosted_wm_capture_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/hosted_wm_capture_evidence_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draws bounded text into the hosted framebuffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
