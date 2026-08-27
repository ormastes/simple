# Gui Content Renderer Specification

> Tests covering GUI content renderer theme seed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gui Content Renderer Specification

## Scenarios

### GUI content renderer theme seed

#### starts neutral so canonical widget Draw IR owns the package seed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts neutral so canonical widget Draw IR owns the package seed
   - Expected: gui_content_frame_clear_color() equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts neutral so canonical widget Draw IR owns the package seed")
expect(gui_content_frame_clear_color()).to_equal(0u32)
```

</details>

#### reuses a seeded idle frame without rebuilding widget DrawIR

- reuses a seeded idle frame without rebuilding widget DrawIR
   - Expected: retained.seed(session) is true
   - Expected: plan.mode equals `DAMAGE_PLAN_NONE`
   - Expected: idle.ops_rendered equals `0`
   - Expected: idle.tiles_rendered equals `0`
   - Expected: idle.readback.source equals `not_requested`
   - Expected: session.draw_ir_submission_revision equals `seeded_revision`
   - Expected: evidence.ops_rendered equals `0`
   - Expected: evidence.readback.source equals `cpu_mirror`
   - Expected: evidence.readback.pixel_count equals `32 * 16`
   - Expected: session.draw_ir_submission_revision equals `seeded_revision`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reuses a seeded idle frame without rebuilding widget DrawIR")
val tree = build_tree(column("root", [label("message", "ready")]))
var session = UISession.new(tree)
var retained = GuiRetainedRenderSession.create(32, 16, "cpu")
expect(retained.seed(session)).to_equal(true)
val seeded_revision = session.draw_ir_submission_revision

var pyramid = DirtyTilePyramid.create(32, 16, [8], [8])
pyramid.begin_frame()
val plan = build_damage_plan(
    pyramid, 0, DamagePlanPolicy.create(8, 60))
expect(plan.mode).to_equal(DAMAGE_PLAN_NONE)

val idle = retained.render_damage(session, plan, false)
expect(idle.ops_rendered).to_equal(0)
expect(idle.tiles_rendered).to_equal(0)
expect(idle.readback.source).to_equal("not_requested")
expect(session.draw_ir_submission_revision).to_equal(seeded_revision)

val evidence = retained.render_damage(session, plan, true)
expect(evidence.ops_rendered).to_equal(0)
expect(evidence.readback.source).to_equal("cpu_mirror")
expect(evidence.readback.pixel_count).to_equal(32 * 16)
expect(session.draw_ir_submission_revision).to_equal(seeded_revision)
retained.shutdown()
```

</details>

#### seeds the first damaged-render call with one valid full-frame plan

- seeds the first damaged-render call with one valid full-frame plan
   - Expected: first.unsupported_kinds equals `none`
   - Expected: first.ops_rendered equals `0`
   - Expected: first.readback.source equals `cpu_mirror`
   - Expected: first.readback.pixel_count equals `32 * 16`
   - Expected: idle.ops_rendered equals `0`
   - Expected: idle.readback.pixels equals `first.readback.pixels`
   - Expected: session.draw_ir_submission_revision equals `first_revision`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("seeds the first damaged-render call with one valid full-frame plan")
val tree = build_tree(column("root", [label("message", "ready")]))
var session = UISession.new(tree)
var retained = GuiRetainedRenderSession.create(32, 16, "cpu")
var pyramid = DirtyTilePyramid.create(32, 16, [8], [8])
pyramid.begin_frame()
val empty = build_damage_plan(
    pyramid, 0, DamagePlanPolicy.create(8, 60))

val first = retained.render_damage(session, empty, true)
expect(first.unsupported_kinds).to_equal("none")
expect(first.ops_rendered).to_equal(0)
expect(first.readback.source).to_equal("cpu_mirror")
expect(first.readback.pixel_count).to_equal(32 * 16)
val first_revision = session.draw_ir_submission_revision

val idle = retained.render_damage(session, empty, true)
expect(idle.ops_rendered).to_equal(0)
expect(idle.readback.pixels).to_equal(first.readback.pixels)
expect(session.draw_ir_submission_revision).to_equal(first_revision)
retained.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GUI content renderer theme seed.
- GUI content renderer theme seed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `c89bc78d2b860d6c6749d2a8a96c87ddbce398b6a33e757e723b841cfef9cf8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c89bc78d2b860d6c6749d2a8a96c87ddbce398b6a33e757e723b841cfef9cf8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c89bc78d2b860d6c6749d2a8a96c87ddbce398b6a33e757e723b841cfef9cf8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts neutral so canonical widget Draw IR owns the package seed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses a seeded idle frame without rebuilding widget DrawIR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seeds the first damaged-render call with one valid full-frame plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
