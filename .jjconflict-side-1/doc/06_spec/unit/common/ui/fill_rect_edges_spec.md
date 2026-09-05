# Fill Rect Edges Specification

> Tests covering BrowserCompositorBackend fill_rect edges.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fill Rect Edges Specification

## Scenarios

### BrowserCompositorBackend fill_rect edges

#### painted region is half-open [x,x+w) x [y,y+h)

#### paints interior pixel (4, 4) when rect is (2,2,3,3)

- paints interior pixel (4, 4) when rect is (2,2,3,3)
   - Expected: cap_read_pixel(backend, 4, 4) equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints interior pixel (4, 4) when rect is (2,2,3,3)")
val backend = _fresh()
backend.fill_rect(2, 2, 3, 3, RED)
expect(cap_read_pixel(backend, 4, 4)).to_equal(RED)
```

</details>

#### paints top-left corner (2, 2) when rect is (2,2,3,3)

- paints top-left corner (2, 2) when rect is (2,2,3,3)
   - Expected: cap_read_pixel(backend, 2, 2) equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints top-left corner (2, 2) when rect is (2,2,3,3)")
val backend = _fresh()
backend.fill_rect(2, 2, 3, 3, RED)
expect(cap_read_pixel(backend, 2, 2)).to_equal(RED)
```

</details>

#### leaves right/bottom edge (5, 5) untouched (EXCLUSIVE)

- leaves right/bottom edge (5, 5) untouched (EXCLUSIVE)
   - Expected: cap_read_pixel(backend, 5, 5) equals `CLEAR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves right/bottom edge (5, 5) untouched (EXCLUSIVE)")
val backend = _fresh()
backend.fill_rect(2, 2, 3, 3, RED)
expect(cap_read_pixel(backend, 5, 5)).to_equal(CLEAR)
```

</details>

#### leaves outside-top-left (1, 1) untouched

- leaves outside-top-left (1, 1) untouched
   - Expected: cap_read_pixel(backend, 1, 1) equals `CLEAR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves outside-top-left (1, 1) untouched")
val backend = _fresh()
backend.fill_rect(2, 2, 3, 3, RED)
expect(cap_read_pixel(backend, 1, 1)).to_equal(CLEAR)
```

</details>

#### degenerate and full-canvas cases

#### no-ops on zero width/height

- no-ops on zero width/height
   - Expected: _all_pixels_are(backend, CLEAR) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no-ops on zero width/height")
val backend = _fresh()
backend.fill_rect(0, 0, 0, 0, BLUE)
expect(_all_pixels_are(backend, CLEAR)).to_equal(true)
```

</details>

#### fills every pixel when rect matches canvas

- fills every pixel when rect matches canvas
   - Expected: _all_pixels_are(backend, GREEN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fills every pixel when rect matches canvas")
val backend = _fresh()
backend.fill_rect(0, 0, W, H, GREEN)
expect(_all_pixels_are(backend, GREEN)).to_equal(true)
```

</details>

#### edge-overlap write order

#### later write wins at overlap (0,0) -> CYAN

- later write wins at overlap (0,0) -> CYAN
   - Expected: cap_read_pixel(backend, 0, 0) equals `CYAN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("later write wins at overlap (0,0) -> CYAN")
val backend = _fresh()
backend.fill_rect(0, 0, W, 1, YELLOW)
backend.fill_rect(0, 0, 1, H, CYAN)
expect(cap_read_pixel(backend, 0, 0)).to_equal(CYAN)
```

</details>

#### non-overlap strip pixel (1, 0) stays YELLOW

- non-overlap strip pixel (1, 0) stays YELLOW
   - Expected: cap_read_pixel(backend, 1, 0) equals `YELLOW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-overlap strip pixel (1, 0) stays YELLOW")
val backend = _fresh()
backend.fill_rect(0, 0, W, 1, YELLOW)
backend.fill_rect(0, 0, 1, H, CYAN)
expect(cap_read_pixel(backend, 1, 0)).to_equal(YELLOW)
```

</details>

#### non-overlap column pixel (0, 1) stays CYAN

- non-overlap column pixel (0, 1) stays CYAN
   - Expected: cap_read_pixel(backend, 0, 1) equals `CYAN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-overlap column pixel (0, 1) stays CYAN")
val backend = _fresh()
backend.fill_rect(0, 0, W, 1, YELLOW)
backend.fill_rect(0, 0, 1, H, CYAN)
expect(cap_read_pixel(backend, 0, 1)).to_equal(CYAN)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/common/ui/fill_rect_edges_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserCompositorBackend fill_rect edges.
- BrowserCompositorBackend fill_rect edges

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `0455540ed34bb3c7460123b8af9ac40f4d8e2a7a4a8215a484338726efae987f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0455540ed34bb3c7460123b8af9ac40f4d8e2a7a4a8215a484338726efae987f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0455540ed34bb3c7460123b8af9ac40f4d8e2a7a4a8215a484338726efae987f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/common/ui/fill_rect_edges_spec.spl
mirror: doc/06_spec/unit/common/ui/fill_rect_edges_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/common/ui/fill_rect_edges_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/common/ui/fill_rect_edges_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/common/ui/fill_rect_edges_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints interior pixel (4, 4) when rect is (2,2,3,3)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/common/ui/fill_rect_edges_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints top-left corner (2, 2) when rect is (2,2,3,3)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/common/ui/fill_rect_edges_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves right/bottom edge (5, 5) untouched (EXCLUSIVE)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
