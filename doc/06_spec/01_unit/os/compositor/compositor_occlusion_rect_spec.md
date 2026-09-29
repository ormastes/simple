# Compositor Occlusion Rect Specification

> Tests covering WS-D6 occlusion coverage predicate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compositor Occlusion Rect Specification

## Scenarios

### WS-D6 occlusion coverage predicate

#### degenerate inputs

#### an empty or inverted rect is trivially covered

- an empty or inverted rect is trivially covered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("an empty or inverted rect is trivially covered")
assert_true(_covered(10, 10, 0, 40, []))
assert_true(_covered(10, 10, 40, 0, []))
assert_true(_covered(10, 10, -5, 40, []))
```

</details>

#### a real rect with NO occluders is never covered

- a real rect with NO occluders is never covered
- this is the empty-desktop case; a true here culls everything


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a real rect with NO occluders is never covered")
step("this is the empty-desktop case; a true here culls everything")
expect_not(_covered(10, 10, 40, 30, []))
```

</details>

#### single occluder

#### exact same rect covers

- exact same rect covers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("exact same rect covers")
assert_true(_covered(10, 10, 40, 30, [10, 10, 40, 30]))
```

</details>

#### strictly larger occluder covers

- strictly larger occluder covers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("strictly larger occluder covers")
assert_true(_covered(10, 10, 40, 30, [0, 0, 100, 100]))
```

</details>

#### one pixel short on width does NOT cover

- one pixel short on width does NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("one pixel short on width does NOT cover")
expect_not(_covered(10, 10, 40, 30, [10, 10, 39, 30]))
```

</details>

#### one pixel short on height does NOT cover

- one pixel short on height does NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("one pixel short on height does NOT cover")
expect_not(_covered(10, 10, 40, 30, [10, 10, 40, 29]))
```

</details>

#### one pixel offset on x does NOT cover

- one pixel offset on x does NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("one pixel offset on x does NOT cover")
expect_not(_covered(10, 10, 40, 30, [11, 10, 40, 30]))
```

</details>

#### one pixel offset on y does NOT cover

- one pixel offset on y does NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("one pixel offset on y does NOT cover")
expect_not(_covered(10, 10, 40, 30, [10, 11, 40, 30]))
```

</details>

#### a disjoint occluder does NOT cover

- a disjoint occluder does NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a disjoint occluder does NOT cover")
expect_not(_covered(10, 10, 40, 30, [200, 200, 40, 30]))
```

</details>

#### an edge-adjacent occluder (touching, not overlapping) does NOT cover

- an edge-adjacent occluder (touching, not overlapping) does NOT cover
- half-open rects: x+w is exclusive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("an edge-adjacent occluder (touching, not overlapping) does NOT cover")
step("half-open rects: x+w is exclusive")
expect_not(_covered(10, 10, 40, 30, [50, 10, 40, 30]))
```

</details>

#### a strictly contained occluder does NOT cover

- a strictly contained occluder does NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a strictly contained occluder does NOT cover")
expect_not(_covered(10, 10, 40, 30, [15, 15, 10, 10]))
```

</details>

#### multiple occluders — the union cases

#### two halves that tile the rect exactly DO cover

- two halves that tile the rect exactly DO cover
- neither alone covers; together they do


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("two halves that tile the rect exactly DO cover")
step("neither alone covers; together they do")
assert_true(_covered(10, 10, 40, 30, [10, 10, 20, 30, 30, 10, 20, 30]))
```

</details>

#### two halves with a one-pixel gap do NOT cover

- two halves with a one-pixel gap do NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("two halves with a one-pixel gap do NOT cover")
expect_not(_covered(10, 10, 40, 30, [10, 10, 19, 30, 30, 10, 20, 30]))
```

</details>

#### overlapping halves still cover

- overlapping halves still cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("overlapping halves still cover")
assert_true(_covered(10, 10, 40, 30, [10, 10, 25, 30, 25, 10, 25, 30]))
```

</details>

#### four quadrants tiling the rect DO cover

- four quadrants tiling the rect DO cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("four quadrants tiling the rect DO cover")
assert_true(_covered(0, 0, 20, 20, [0, 0, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10]))
```

</details>

#### three of four quadrants do NOT cover

- three of four quadrants do NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("three of four quadrants do NOT cover")
expect_not(_covered(0, 0, 20, 20, [0, 0, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10]))
```

</details>

#### a donut of occluders leaving a centre hole does NOT cover

- a donut of occluders leaving a centre hole does NOT cover
- classic false-positive shape for a bounding-box test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a donut of occluders leaving a centre hole does NOT cover")
step("classic false-positive shape for a bounding-box test")
expect_not(_covered(0, 0, 30, 30, [0, 0, 30, 10, 0, 20, 30, 10, 0, 0, 10, 30, 20, 0, 10, 30]))
```

</details>

#### the same donut plus the centre patch DOES cover

- the same donut plus the centre patch DOES cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the same donut plus the centre patch DOES cover")
val donut_plus_centre = [0, 0, 30, 10, 0, 20, 30, 10,
                         0, 0, 10, 30, 20, 0, 10, 30, 10, 10, 10, 10]
assert_true(_covered(0, 0, 30, 30, donut_plus_centre))
```

</details>

#### three horizontal bands tiling the rect DO cover

- three horizontal bands tiling the rect DO cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("three horizontal bands tiling the rect DO cover")
assert_true(_covered(5, 5, 50, 30, [5, 5, 50, 10, 5, 15, 50, 10, 5, 25, 50, 10]))
```

</details>

#### three horizontal bands with a middle gap do NOT cover

- three horizontal bands with a middle gap do NOT cover


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("three horizontal bands with a middle gap do NOT cover")
expect_not(_covered(5, 5, 50, 30, [5, 5, 50, 10, 5, 16, 50, 9, 5, 25, 50, 10]))
```

</details>

#### the production toggle

#### defaults to enabled and round-trips

- defaults to enabled and round-trips


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defaults to enabled and round-trips")
assert_true(wm_occlusion_culling_enabled())
wm_set_occlusion_culling(false)
expect_not(wm_occlusion_culling_enabled())
wm_set_occlusion_culling(true)
assert_true(wm_occlusion_culling_enabled())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/compositor_occlusion_rect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WS-D6 occlusion coverage predicate.
- WS-D6 occlusion coverage predicate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `883d14154c37a5031aca8b0d296b5a087ccfd0b3ccb27526b03d0cadbdc7f2b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `883d14154c37a5031aca8b0d296b5a087ccfd0b3ccb27526b03d0cadbdc7f2b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `883d14154c37a5031aca8b0d296b5a087ccfd0b3ccb27526b03d0cadbdc7f2b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/compositor_occlusion_rect_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/compositor_occlusion_rect_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/compositor_occlusion_rect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/compositor_occlusion_rect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/compositor_occlusion_rect_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an empty or inverted rect is trivially covered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/compositor_occlusion_rect_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a real rect with NO occluders is never covered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/compositor_occlusion_rect_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exact same rect covers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
