# Pixel Surface Content Frame Specification

> Tests covering pixel surface content frame.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pixel Surface Content Frame Specification

## Scenarios

### pixel surface content frame

#### validates pixels and retains nested placement

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates pixels and retains nested placement
   - Expected: frame.origin_kind equals `WM_CONTENT_ORIGIN_PIXEL_SURFACE`
   - Expected: frame.parent_window_id equals `1`
   - Expected: frame.offset_x equals `7`
   - Expected: frame.offset_y equals `9`
   - Expected: frame.checksum > 0u64 is true
   - Expected: invalid.checksum equals `0u64`
   - Expected: invalid.pixels.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates pixels and retains nested placement")
val frame = pixel_surface_content_frame(
    "canvas", "1", 7, 9, 2, 2,
    [0xff000001u32, 0xff000002u32, 0xff000003u32, 0xff000004u32],
    3, 4
)
expect(frame.origin_kind).to_equal(WM_CONTENT_ORIGIN_PIXEL_SURFACE)
expect(frame.parent_window_id).to_equal("1")
expect(frame.offset_x).to_equal(7)
expect(frame.offset_y).to_equal(9)
expect(frame.checksum > 0u64).to_equal(true)

val invalid = pixel_surface_content_frame(
    "bad", "", 0, 0, 2, 2, [0u32], 1, 1
)
expect(invalid.checksum).to_equal(0u64)
expect(invalid.pixels.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/pixel_surface_content_frame_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pixel surface content frame.
- pixel surface content frame

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `60ee65ab89b1c0f64bd2cbbab7679a6a7a975c7f1f5a9efcd6ece3a5d08f98e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60ee65ab89b1c0f64bd2cbbab7679a6a7a975c7f1f5a9efcd6ece3a5d08f98e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60ee65ab89b1c0f64bd2cbbab7679a6a7a975c7f1f5a9efcd6ece3a5d08f98e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/ui/pixel_surface_content_frame_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/pixel_surface_content_frame_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/pixel_surface_content_frame_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/pixel_surface_content_frame_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/pixel_surface_content_frame_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/pixel_surface_content_frame_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates pixels and retains nested placement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
