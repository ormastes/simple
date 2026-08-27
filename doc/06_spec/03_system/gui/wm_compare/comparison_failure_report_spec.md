# Comparison Failure Report Specification

> Tests covering wm_compare comparison failure report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comparison Failure Report Specification

## Scenarios

### wm_compare comparison failure report

#### preserves capture failure before metadata layout or pixel checks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves capture failure before metadata layout or pixel checks
   - Expected: report.capture_status equals `capture_failed`
   - Expected: report.metadata_status equals `not_evaluated`
   - Expected: report.structural_status equals `not_evaluated`
   - Expected: report.pixel_status equals `not_evaluated`
   - Expected: report.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves capture failure before metadata layout or pixel checks")
val report = comparison_failure_report(
    "chrome", "simple",
    false, true,
    true,
    "layout_match",
    true,
    "Initialized"
)
expect(report.capture_status).to_equal("capture_failed")
expect(report.metadata_status).to_equal("not_evaluated")
expect(report.structural_status).to_equal("not_evaluated")
expect(report.pixel_status).to_equal("not_evaluated")
expect(report.accepted).to_equal(false)
```

</details>

#### separates metadata mismatch from pixel mismatch

- separates metadata mismatch from pixel mismatch
   - Expected: report.capture_status equals `ok`
   - Expected: report.metadata_status equals `metadata_mismatch`
   - Expected: report.pixel_status equals `not_evaluated`
   - Expected: report.primary_status equals `metadata_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("separates metadata mismatch from pixel mismatch")
val report = comparison_failure_report(
    "chrome", "simple",
    true, true,
    false,
    "layout_match",
    false,
    "Initialized"
)
expect(report.capture_status).to_equal("ok")
expect(report.metadata_status).to_equal("metadata_mismatch")
expect(report.pixel_status).to_equal("not_evaluated")
expect(report.primary_status).to_equal("metadata_mismatch")
```

</details>

#### separates structural geometry mismatch from pixel mismatch

- separates structural geometry mismatch from pixel mismatch
   - Expected: report.structural_status equals `layout_mismatch`
   - Expected: report.pixel_status equals `not_evaluated`
   - Expected: report.primary_status equals `layout_mismatch`
   - Expected: report.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("separates structural geometry mismatch from pixel mismatch")
val report = comparison_failure_report(
    "tui", "gui",
    true, true,
    true,
    "layout_mismatch",
    true,
    "Initialized"
)
expect(report.structural_status).to_equal("layout_mismatch")
expect(report.pixel_status).to_equal("not_evaluated")
expect(report.primary_status).to_equal("layout_mismatch")
expect(report.accepted).to_equal(false)
```

</details>

#### reports exact pixel mismatch after valid capture metadata and layout

- reports exact pixel mismatch after valid capture metadata and layout
   - Expected: report.capture_status equals `ok`
   - Expected: report.metadata_status equals `ok`
   - Expected: report.structural_status equals `layout_match`
   - Expected: report.pixel_status equals `exact_mismatch`
   - Expected: report.primary_status equals `exact_mismatch`
   - Expected: report.exact_required is true
   - Expected: report.perceptual_diagnostic_only is true
   - Expected: report.tolerance_acceptance_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports exact pixel mismatch after valid capture metadata and layout")
val report = comparison_failure_report(
    "chrome", "simple",
    true, true,
    true,
    "layout_match",
    false,
    "Initialized"
)
expect(report.capture_status).to_equal("ok")
expect(report.metadata_status).to_equal("ok")
expect(report.structural_status).to_equal("layout_match")
expect(report.pixel_status).to_equal("exact_mismatch")
expect(report.primary_status).to_equal("exact_mismatch")
expect(report.exact_required).to_equal(true)
expect(report.perceptual_diagnostic_only).to_equal(true)
expect(report.tolerance_acceptance_allowed).to_equal(false)
```

</details>

#### keeps backend unavailability separate from comparison acceptance

- keeps backend unavailability separate from comparison acceptance
   - Expected: report.accepted is true
   - Expected: report.backend_status equals `backend_unavailable`
   - Expected: report.primary_status equals `backend_unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps backend unavailability separate from comparison acceptance")
val report = comparison_failure_report(
    "chrome", "simple",
    true, true,
    true,
    "layout_match",
    true,
    "Unavailable"
)
expect(report.accepted).to_equal(true)
expect(report.backend_status).to_equal("backend_unavailable")
expect(report.primary_status).to_equal("backend_unavailable")
val sdn = comparison_failure_report_sdn(report)
expect(sdn).to_contain("capture_status: \"ok\"")
expect(sdn).to_contain("pixel_status: \"exact_match\"")
expect(sdn).to_contain("backend_status: \"backend_unavailable\"")
expect(sdn).to_contain("acceptance_policy: (exact_required: true perceptual_diagnostic_only: true tolerance_acceptance_allowed: false)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/comparison_failure_report_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wm_compare comparison failure report.
- wm_compare comparison failure report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4f9f88e6f6bddd7747b6a4c7ab3780dead4a87e8eb7629a6f4adda98f6250cb6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f9f88e6f6bddd7747b6a4c7ab3780dead4a87e8eb7629a6f4adda98f6250cb6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f9f88e6f6bddd7747b6a4c7ab3780dead4a87e8eb7629a6f4adda98f6250cb6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/03_system/gui/wm_compare/comparison_failure_report_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/comparison_failure_report_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/comparison_failure_report_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/comparison_failure_report_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/comparison_failure_report_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'separates structural geometry mismatch from pixel mismatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
