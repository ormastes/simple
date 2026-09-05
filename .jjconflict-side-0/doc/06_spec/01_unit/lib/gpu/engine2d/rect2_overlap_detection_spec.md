# rect2_overlap_detection_spec

> Engine2D-adjacent Overlap Detection Specification (Rect2)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rect2_overlap_detection_spec

Engine2D-adjacent Overlap Detection Specification (Rect2)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/rect2_overlap_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine2D-adjacent Overlap Detection Specification (Rect2)

@tag: gpu, engine2d, overlap, rect, hit-testing

Audit tranche (E2D-AUDIT, 2026-07-20): Engine2D itself has no rect-overlap or
region-intersection API (grep of src/lib/gc_async_mut/gpu/engine2d/*.spl for
`fn intersect|overlap|contains_point` returns nothing). The nearest usable
primitive in the tree is `Rect2` (`src/lib/common/engine/rect.spl`,
`common` tier, generic — not engine2d-specific), which the compositional
overlap-detection scenarios below would have to be built on if Engine2D grew
a dedicated API. This spec locks down `Rect2.intersects` / `.contains_point`
edge-convention behavior since a 2D compositor's overlap/hit-test logic is
only as correct as those two primitives.

Both methods use a half-open convention throughout `Rect2`: `right()` /
`bottom()` are exclusive bounds. This means edge-touching and corner-touching
rectangles do NOT intersect, and a point exactly on the right or bottom edge
is NOT contained. This spec asserts that convention explicitly so a future
Engine2D-level overlap/hit-test API inherits it deliberately, not by
accident.

## Scenarios

### Rect2 rect-rect intersection

#### partially overlapping rects intersect

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- partially overlapping rects intersect
   - Expected: a.intersects(b) is true
   - Expected: b.intersects(a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("partially overlapping rects intersect")
val a = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
val b = Rect2(x: 5.0, y: 5.0, width: 10.0, height: 10.0)
expect(a.intersects(b)).to_equal(true)
expect(b.intersects(a)).to_equal(true)
```

</details>

#### one rect fully contained in another intersects

- one rect fully contained in another intersects
   - Expected: outer.intersects(inner) is true
   - Expected: inner.intersects(outer) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one rect fully contained in another intersects")
val outer = Rect2(x: 0.0, y: 0.0, width: 20.0, height: 20.0)
val inner = Rect2(x: 5.0, y: 5.0, width: 2.0, height: 2.0)
expect(outer.intersects(inner)).to_equal(true)
expect(inner.intersects(outer)).to_equal(true)
```

</details>

#### disjoint rects (far apart) do not intersect

- disjoint rects (far apart) do not intersect
   - Expected: a.intersects(b) is false
   - Expected: b.intersects(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disjoint rects (far apart) do not intersect")
val a = Rect2(x: 0.0, y: 0.0, width: 5.0, height: 5.0)
val b = Rect2(x: 100.0, y: 100.0, width: 5.0, height: 5.0)
expect(a.intersects(b)).to_equal(false)
expect(b.intersects(a)).to_equal(false)
```

</details>

#### edge-touching rects (shared vertical edge, half-open convention) do not intersect

- edge-touching rects (shared vertical edge, half-open convention) do not intersect
   - Expected: a.intersects(b) is false
   - Expected: b.intersects(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge-touching rects (shared vertical edge, half-open convention) do not intersect")
val a = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
val b = Rect2(x: 10.0, y: 0.0, width: 10.0, height: 10.0)
expect(a.intersects(b)).to_equal(false)
expect(b.intersects(a)).to_equal(false)
```

</details>

#### edge-touching rects (shared horizontal edge, half-open convention) do not intersect

- edge-touching rects (shared horizontal edge, half-open convention) do not intersect
   - Expected: a.intersects(b) is false
   - Expected: b.intersects(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge-touching rects (shared horizontal edge, half-open convention) do not intersect")
val a = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
val b = Rect2(x: 0.0, y: 10.0, width: 10.0, height: 10.0)
expect(a.intersects(b)).to_equal(false)
expect(b.intersects(a)).to_equal(false)
```

</details>

#### corner-touching rects do not intersect

- corner-touching rects do not intersect
   - Expected: a.intersects(b) is false
   - Expected: b.intersects(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("corner-touching rects do not intersect")
val a = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
val b = Rect2(x: 10.0, y: 10.0, width: 10.0, height: 10.0)
expect(a.intersects(b)).to_equal(false)
expect(b.intersects(a)).to_equal(false)
```

</details>

#### one-pixel overlap counts as intersecting

- one-pixel overlap counts as intersecting
   - Expected: a.intersects(b) is true
   - Expected: b.intersects(a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one-pixel overlap counts as intersecting")
val a = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
val b = Rect2(x: 9.0, y: 9.0, width: 10.0, height: 10.0)
expect(a.intersects(b)).to_equal(true)
expect(b.intersects(a)).to_equal(true)
```

</details>

### Rect2 point containment

#### point strictly inside is contained

- point strictly inside is contained
   - Expected: r.contains_point(5.0, 5.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("point strictly inside is contained")
val r = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
expect(r.contains_point(5.0, 5.0)).to_equal(true)
```

</details>

#### point on the left/top edge is contained (inclusive)

- point on the left/top edge is contained (inclusive)
   - Expected: r.contains_point(0.0, 5.0) is true
   - Expected: r.contains_point(5.0, 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("point on the left/top edge is contained (inclusive)")
val r = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
expect(r.contains_point(0.0, 5.0)).to_equal(true)
expect(r.contains_point(5.0, 0.0)).to_equal(true)
```

</details>

#### point on the right/bottom edge is NOT contained (exclusive)

- point on the right/bottom edge is NOT contained (exclusive)
   - Expected: r.contains_point(10.0, 5.0) is false
   - Expected: r.contains_point(5.0, 10.0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("point on the right/bottom edge is NOT contained (exclusive)")
val r = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
expect(r.contains_point(10.0, 5.0)).to_equal(false)
expect(r.contains_point(5.0, 10.0)).to_equal(false)
```

</details>

#### point fully outside is not contained

- point fully outside is not contained
   - Expected: r.contains_point(-1.0, 5.0) is false
   - Expected: r.contains_point(50.0, 50.0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("point fully outside is not contained")
val r = Rect2(x: 0.0, y: 0.0, width: 10.0, height: 10.0)
expect(r.contains_point(-1.0, 5.0)).to_equal(false)
expect(r.contains_point(50.0, 50.0)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `a0f91a0cdf37e5c672be60ca5e72ccdbc23a4f11d50ca7c5ae35ffd61dd4e2c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0f91a0cdf37e5c672be60ca5e72ccdbc23a4f11d50ca7c5ae35ffd61dd4e2c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0f91a0cdf37e5c672be60ca5e72ccdbc23a4f11d50ca7c5ae35ffd61dd4e2c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/rect2_overlap_detection_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/rect2_overlap_detection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/rect2_overlap_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/rect2_overlap_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/rect2_overlap_detection_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'partially overlapping rects intersect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/rect2_overlap_detection_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'one rect fully contained in another intersects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/rect2_overlap_detection_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'disjoint rects (far apart) do not intersect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
