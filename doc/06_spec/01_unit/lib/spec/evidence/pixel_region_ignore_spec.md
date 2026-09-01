# Pixel Region Ignore Specification

> Tests covering GUI image compare — ignore sections.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pixel Region Ignore Specification

## Scenarios

### GUI image compare — ignore sections

#### names a rectangular region of the captured image

- names a rectangular region of the captured image
- Select a 120x40 region at offset (16, 8) — a status bar, say
- Confirm the rectangle round-trips exactly through the selector
   - Expected: pixel_region_x(region) equals `16`
   - Expected: pixel_region_y(region) equals `8`
   - Expected: pixel_region_width(region) equals `120`
   - Expected: pixel_region_height(region) equals `40`
- Confirm it is carried as a pixel_region, not silently downgraded
   - Expected: selector_kind_name(region.kind) equals `pixel_region`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("names a rectangular region of the captured image")
step("Select a 120x40 region at offset (16, 8) — a status bar, say")
val region = selector_pixel_region(16, 8, 120, 40)

step("Confirm the rectangle round-trips exactly through the selector")
expect(pixel_region_x(region)).to_equal(16)
expect(pixel_region_y(region)).to_equal(8)
expect(pixel_region_width(region)).to_equal(120)
expect(pixel_region_height(region)).to_equal(40)

step("Confirm it is carried as a pixel_region, not silently downgraded")
expect(selector_kind_name(region.kind)).to_equal("pixel_region")
```

</details>

#### keeps a large region's extent intact rather than truncating it

- keeps a large region's extent intact rather than truncating it
- Select a region spanning a 4K framebuffer
- Confirm both extents survive the packing
   - Expected: pixel_region_width(region) equals `3840`
   - Expected: pixel_region_height(region) equals `2160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a large region's extent intact rather than truncating it")
# The rect is packed two-per-field; a naive 32-bit pack corrupts a 4K capture.
step("Select a region spanning a 4K framebuffer")
val region = selector_pixel_region(0, 0, 3840, 2160)

step("Confirm both extents survive the packing")
expect(pixel_region_width(region)).to_equal(3840)
expect(pixel_region_height(region)).to_equal(2160)
```

</details>

#### records why a region is masked instead of dropping it silently

- records why a region is masked instead of dropping it silently
- Mask the clock region, stating the reason it cannot be compared
- Confirm the reason travelled with the check
- Confirm the masked rectangle is still fully described
   - Expected: pixel_region_width(clock) equals `100`
   - Expected: pixel_region_height(clock) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records why a region is masked instead of dropping it silently")
step("Mask the clock region, stating the reason it cannot be compared")
val clock = selector_pixel_region(900, 4, 100, 20)
val ignored = check_ignore("clock", "wall-clock text differs on every capture")

step("Confirm the reason travelled with the check")
expect(ignored.reason.len()).to_be_greater_than(0)
expect(ignored.reason).to_contain("wall-clock")

step("Confirm the masked rectangle is still fully described")
expect(pixel_region_width(clock)).to_equal(100)
expect(pixel_region_height(clock)).to_equal(20)
```

</details>

#### pairs a masked region with a positive check over the rest of the image

- pairs a masked region with a positive check over the rest of the image
- Build an oracle that masks the clock but still checks the title bar
- Confirm both checks are carried — the mask did not replace the oracle
   - Expected: spec.checks.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pairs a masked region with a positive check over the rest of the image")
# An oracle needs at least one positive claim; the comparator rejects an
# all-ignore spec ("oracle has no positive production check"). This example
# documents the shape a real GUI comparison must take.
step("Build an oracle that masks the clock but still checks the title bar")
val title = selector_pixel_region(0, 0, 400, 24)
val checks = [
    check_exact_selector(title, "title-bar-digest"),
    check_ignore("clock", "wall-clock text differs on every capture")
]
val spec = oracle_spec("gui.image.v1", checks)

step("Confirm both checks are carried — the mask did not replace the oracle")
expect(spec.checks.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/spec/evidence/pixel_region_ignore_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GUI image compare — ignore sections.
- GUI image compare — ignore sections

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82ce9c6bcff0d61385ccb27bde32fd41589911792a05cab6f0e56d392a870cac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82ce9c6bcff0d61385ccb27bde32fd41589911792a05cab6f0e56d392a870cac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82ce9c6bcff0d61385ccb27bde32fd41589911792a05cab6f0e56d392a870cac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/spec/evidence/pixel_region_ignore_spec.spl
mirror: doc/06_spec/01_unit/lib/spec/evidence/pixel_region_ignore_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/spec/evidence/pixel_region_ignore_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/spec/evidence/pixel_region_ignore_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/spec/evidence/pixel_region_ignore_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/spec/evidence/pixel_region_ignore_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names a rectangular region of the captured image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/spec/evidence/pixel_region_ignore_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a large region's extent intact rather than truncating it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/spec/evidence/pixel_region_ignore_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records why a region is masked instead of dropping it silently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
