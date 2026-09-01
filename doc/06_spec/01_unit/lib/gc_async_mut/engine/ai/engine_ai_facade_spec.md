# Engine Ai Facade Specification

> Tests covering gc_async_mut engine ai facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Ai Facade Specification

## Scenarios

### gc_async_mut engine ai facade

#### re-exports navmesh geometry and path helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports navmesh geometry and path helpers
   - Expected: a.distance_to(b) equals `5.0`
   - Expected: poly.contains_point(1.0, 1.0) is true
   - Expected: poly.has_neighbor(8) is true
   - Expected: mesh.polygon_count() equals `2`
   - Expected: mesh.find_polygon_at(1.0, 1.0) equals `left`
   - Expected: mesh.find_path(1.0, 1.0, 11.0, 1.0).length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports navmesh geometry and path helpers")
val a = NavPoint(x: 0.0, y: 0.0)
val b = NavPoint(x: 3.0, y: 4.0)
expect(a.distance_to(b)).to_equal(5.0)

var poly = NavPolygon.new(7, [
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 0.0, y: 10.0)
])
expect(poly.center.x).to_be_greater_than(3.0)
expect(poly.contains_point(1.0, 1.0)).to_equal(true)
poly.add_neighbor(8)
expect(poly.has_neighbor(8)).to_equal(true)

var mesh = NavMesh.new()
val left = mesh.add_polygon([
    NavPoint(x: 0.0, y: 0.0),
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 0.0, y: 10.0)
])
val right = mesh.add_polygon([
    NavPoint(x: 10.0, y: 0.0),
    NavPoint(x: 20.0, y: 0.0),
    NavPoint(x: 10.0, y: 10.0)
])
mesh.connect(left, right)
expect(mesh.polygon_count()).to_equal(2)
expect(mesh.find_polygon_at(1.0, 1.0)).to_equal(left)
expect(mesh.find_path(1.0, 1.0, 11.0, 1.0).length()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/ai/engine_ai_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut engine ai facade.
- gc_async_mut engine ai facade

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

- Canonical SPipe generation for source `bf374e90e7f7c31b53c7b73ca09170aea88c885e7f7ccd970edf81404cddadd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf374e90e7f7c31b53c7b73ca09170aea88c885e7f7ccd970edf81404cddadd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf374e90e7f7c31b53c7b73ca09170aea88c885e7f7ccd970edf81404cddadd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/engine/ai/engine_ai_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/engine/ai/engine_ai_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/engine/ai/engine_ai_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/engine/ai/engine_ai_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/engine/ai/engine_ai_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/engine/ai/engine_ai_facade_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports navmesh geometry and path helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
