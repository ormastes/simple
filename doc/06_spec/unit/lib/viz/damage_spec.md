# Damage Specification

> Tests covering damage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Damage Specification

## Scenarios

### damage

#### union_rects with empty second operand returns first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- union_rects with empty second operand returns first
   - Expected: eq is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("union_rects with empty second operand returns first")
val a = _rect(10.0, 20.0, 50.0, 60.0)
val empty = _empty_rect()
val result = union_rects(a, empty)
val eq = _rect_eq(result, a)
expect(eq).to_equal(true)
```

</details>

#### union_rects of two disjoint rects returns bounding box

- union_rects of two disjoint rects returns bounding box
   - Expected: result.left equals `0.0`
   - Expected: result.top equals `0.0`
   - Expected: result.right equals `40.0`
   - Expected: result.bottom equals `50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("union_rects of two disjoint rects returns bounding box")
val a = _rect(0.0, 0.0, 10.0, 10.0)
val b = _rect(20.0, 30.0, 40.0, 50.0)
val result = union_rects(a, b)
expect(result.left).to_equal(0.0)
expect(result.top).to_equal(0.0)
expect(result.right).to_equal(40.0)
expect(result.bottom).to_equal(50.0)
```

</details>

#### union_rects of two overlapping rects returns outer bounds

- union_rects of two overlapping rects returns outer bounds
   - Expected: result.left equals `0.0`
   - Expected: result.top equals `0.0`
   - Expected: result.right equals `50.0`
   - Expected: result.bottom equals `50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("union_rects of two overlapping rects returns outer bounds")
val a = _rect(0.0, 0.0, 30.0, 30.0)
val b = _rect(20.0, 20.0, 50.0, 50.0)
val result = union_rects(a, b)
expect(result.left).to_equal(0.0)
expect(result.top).to_equal(0.0)
expect(result.right).to_equal(50.0)
expect(result.bottom).to_equal(50.0)
```

</details>

#### intersect_rect of disjoint rects returns empty

- intersect_rect of disjoint rects returns empty
   - Expected: result.left equals `0.0`
   - Expected: result.top equals `0.0`
   - Expected: result.right equals `0.0`
   - Expected: result.bottom equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("intersect_rect of disjoint rects returns empty")
val a = _rect(0.0, 0.0, 10.0, 10.0)
val b = _rect(20.0, 20.0, 40.0, 40.0)
val result = intersect_rect(a, b)
expect(result.left).to_equal(0.0)
expect(result.top).to_equal(0.0)
expect(result.right).to_equal(0.0)
expect(result.bottom).to_equal(0.0)
```

</details>

#### intersect_rect of contained rects returns the smaller rect

- intersect_rect of contained rects returns the smaller rect
   - Expected: result.left equals `10.0`
   - Expected: result.top equals `10.0`
   - Expected: result.right equals `40.0`
   - Expected: result.bottom equals `40.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("intersect_rect of contained rects returns the smaller rect")
val outer = _rect(0.0, 0.0, 100.0, 100.0)
val inner = _rect(10.0, 10.0, 40.0, 40.0)
val result = intersect_rect(outer, inner)
expect(result.left).to_equal(10.0)
expect(result.top).to_equal(10.0)
expect(result.right).to_equal(40.0)
expect(result.bottom).to_equal(40.0)
```

</details>

#### aggregate_damage with no children equals root damage clipped to viewport

- aggregate_damage with no children equals root damage clipped to viewport
   - Expected: eq is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aggregate_damage with no children equals root damage clipped to viewport")
val viewport = _rect(0.0, 0.0, 800.0, 600.0)
val damage   = _rect(10.0, 20.0, 200.0, 150.0)
val root = _make_frame_with_damage(damage, viewport)
val no_children: [CompositorFrame] = []
val no_clips: [SkRect] = []
val result = aggregate_damage(root, no_children, no_clips)
val eq = _rect_eq(result, damage)
expect(eq).to_equal(true)
```

</details>

#### aggregate_damage unions child damage clipped by child clip rect

- aggregate_damage unions child damage clipped by child clip rect
   - Expected: result.left equals `0.0`
   - Expected: result.top equals `0.0`
   - Expected: result.right equals `100.0`
   - Expected: result.bottom equals `100.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aggregate_damage unions child damage clipped by child clip rect")
val viewport      = _rect(0.0, 0.0, 800.0, 600.0)
val root_damage   = _rect(0.0, 0.0, 50.0, 50.0)
val root_frame    = _make_frame_with_damage(root_damage, viewport)

# child damage extends to (300, 300) but clip cuts it to (100, 100)
val child_damage  = _rect(0.0, 0.0, 300.0, 300.0)
val child_frame   = _make_frame_with_damage(child_damage, viewport)
val child_clip    = _rect(0.0, 0.0, 100.0, 100.0)

val children      = [child_frame]
val clips         = [child_clip]
val result        = aggregate_damage(root_frame, children, clips)

# union of root(0,0,50,50) and clipped-child(0,0,100,100) = (0,0,100,100)
# then clamped to viewport (0,0,800,600) => (0,0,100,100)
expect(result.left).to_equal(0.0)
expect(result.top).to_equal(0.0)
expect(result.right).to_equal(100.0)
expect(result.bottom).to_equal(100.0)
```

</details>

<details>
<summary>Advanced: propagate_damage_up through identity matrix returns unchanged rect</summary>

#### propagate_damage_up through identity matrix returns unchanged rect

- propagate_damage_up through identity matrix returns unchanged rect
   - Expected: eq is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagate_damage_up through identity matrix returns unchanged rect")
val dmg    = _rect(10.0, 20.0, 80.0, 90.0)
val ident  = Matrix3x3.identity()
val result = propagate_damage_up(dmg, ident)
val eq = _rect_eq(result, dmg)
expect(eq).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/viz/damage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering damage.
- damage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `f09afc3ca062a773bca4089b5388c84ee7b20ad8030be12b0e86102a150c6f16`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f09afc3ca062a773bca4089b5388c84ee7b20ad8030be12b0e86102a150c6f16`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f09afc3ca062a773bca4089b5388c84ee7b20ad8030be12b0e86102a150c6f16`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/viz/damage_spec.spl
mirror: doc/06_spec/unit/lib/viz/damage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/viz/damage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/viz/damage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/viz/damage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/viz/damage_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'union_rects with empty second operand returns first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/viz/damage_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'union_rects of two disjoint rects returns bounding box' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/viz/damage_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'union_rects of two overlapping rects returns outer bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
