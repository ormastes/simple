# Render Surface Widget Specification

> Tests covering RenderSurface widget.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Surface Widget Specification

## Scenarios

### RenderSurface widget

#### translates contained child coordinates and rejects letterbox pixels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- translates contained child coordinates and rejects letterbox pixels
   - Expected: center.child_surface_handle equals `77`
   - Expected: center.local_x equals `50`
   - Expected: center.local_y equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("translates contained child coordinates and rejects letterbox pixels")
val root = render_surface(
    "contained-surface", 77, 100, 50, RENDER_SURFACE_FIT_CONTAIN
)
expect(render_surface_is_node(root)).to_be(true)
val center = render_surface_pointer_target(
    root, 200, 200, root.id, 100, 100
)
expect(center.found).to_be(true)
expect(center.child_surface_handle).to_equal(77)
expect(center.local_x).to_equal(50)
expect(center.local_y).to_equal(25)
expect(render_surface_pointer_target(
    root, 200, 200, root.id, 100, 10
).found).to_be(false)
```

</details>

#### supports stretch and native fit without inventing another widget kind

- supports stretch and native fit without inventing another widget kind
   - Expected: stretch_hit.local_x equals `25`
   - Expected: stretch_hit.local_y equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("supports stretch and native fit without inventing another widget kind")
val stretched = render_surface(
    "stretched-surface", 88, 100, 50, RENDER_SURFACE_FIT_STRETCH
)
val stretch_hit = render_surface_pointer_target(
    stretched, 200, 200, stretched.id, 50, 150
)
expect(stretch_hit.local_x).to_equal(25)
expect(stretch_hit.local_y).to_equal(37)

val native = render_surface(
    "native-surface", 99, 100, 50, RENDER_SURFACE_FIT_NATIVE
)
expect(render_surface_pointer_target(
    native, 200, 200, native.id, 99, 49
).found).to_be(true)
expect(render_surface_pointer_target(
    native, 200, 200, native.id, 100, 49
).found).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/render_surface_widget_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RenderSurface widget.
- RenderSurface widget

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d36de7a0d51295ea91e04952dbc948f0d2916c150af217325fc0c320d1ca85e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d36de7a0d51295ea91e04952dbc948f0d2916c150af217325fc0c320d1ca85e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d36de7a0d51295ea91e04952dbc948f0d2916c150af217325fc0c320d1ca85e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/render_surface_widget_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/render_surface_widget_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/render_surface_widget_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/render_surface_widget_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/render_surface_widget_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/render_surface_widget_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translates contained child coordinates and rejects letterbox pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_surface_widget_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports stretch and native fit without inventing another widget kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
