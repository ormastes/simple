# simple_web_retained_engine2d_surface_spec

> Exact retained-frame contract for the direct Web-to-Engine2D CPU adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_web_retained_engine2d_surface_spec

Exact retained-frame contract for the direct Web-to-Engine2D CPU adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_retained_engine2d_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exact retained-frame contract for the direct Web-to-Engine2D CPU adapter.

## Scenarios

### Simple Web retained Engine2D surface

#### seeds once, replays exact damage, and leaves an idle frame untouched

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- seeds once, replays exact damage, and leaves an idle frame untouched
   - Expected: seed.readback.pixels[0] equals `RETAINED_GREEN`
   - Expected: changed.unsupported_kinds equals `none`
   - Expected: changed.ops_rendered equals `1`
   - Expected: changed.readback.pixels[1 * 8 + 2] equals `RETAINED_RED`
   - Expected: changed.readback.pixels[1 * 8 + 3] equals `RETAINED_RED`
   - Expected: changed.readback.pixels[0] equals `RETAINED_GREEN`
   - Expected: changed.readback.pixels[1 * 8 + 1] equals `RETAINED_GREEN`
   - Expected: idle.ops_rendered equals `0`
   - Expected: idle.readback.pixels equals `changed.readback.pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("seeds once, replays exact damage, and leaves an idle frame untouched")
var surface = SimpleWebCpuDrawIrRetainedSurface.create(8, 4, "cpu")
val seed = surface.seed(_retained_web_composition([
    draw_ir_rect("background", 0, 0, 8, 4, RETAINED_GREEN)
]), true)
expect(seed.readback.pixels[0]).to_equal(RETAINED_GREEN)

val changed = surface.render_damage(_retained_web_composition([
    draw_ir_rect("changed", 2, 1, 2, 1, RETAINED_RED)
]), _retained_local_plan(), true)
expect(changed.unsupported_kinds).to_equal("none")
expect(changed.ops_rendered).to_equal(1)
expect(changed.readback.pixels[1 * 8 + 2]).to_equal(RETAINED_RED)
expect(changed.readback.pixels[1 * 8 + 3]).to_equal(RETAINED_RED)
expect(changed.readback.pixels[0]).to_equal(RETAINED_GREEN)
expect(changed.readback.pixels[1 * 8 + 1]).to_equal(RETAINED_GREEN)

val idle = surface.render_damage(
    _retained_web_composition([]), _retained_idle_plan(), true)
expect(idle.ops_rendered).to_equal(0)
expect(idle.readback.pixels).to_equal(changed.readback.pixels)
surface.shutdown()
```

</details>

#### rejects a malformed none plan instead of silently idling

- rejects a malformed none plan instead of silently idling
   - Expected: outcome.unsupported_kinds equals `retained-none-plan-has-rects`
   - Expected: outcome.readback.pixels equals `seed.readback.pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a malformed none plan instead of silently idling")
var surface = SimpleWebCpuDrawIrRetainedSurface.create(8, 4, "cpu")
val seed = surface.seed(_retained_web_composition([
    draw_ir_rect("background", 0, 0, 8, 4, RETAINED_GREEN)
]), true)
val malformed = DamagePlan(
    rects: [2, 1, 2, 1], mode: DAMAGE_PLAN_NONE,
    source_tile_count: 1, output_rect_count: 1,
    merged_tile_count: 0, dirty_pixels: 2, planned_pixels: 2,
    full_fallback_count: 0, fallback_reason: DAMAGE_FALLBACK_NONE,
    tiles_examined: 1)
val outcome = surface.render_damage(
    _retained_web_composition([]), malformed, true)
expect(outcome.unsupported_kinds).to_equal("retained-none-plan-has-rects")
expect(outcome.readback.pixels).to_equal(seed.readback.pixels)
surface.shutdown()
```

</details>

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

- Canonical SPipe generation for source `654c31c68726190718240864a496208c5af2fbe781b380b23ac46f523dbfcbef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `654c31c68726190718240864a496208c5af2fbe781b380b23ac46f523dbfcbef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `654c31c68726190718240864a496208c5af2fbe781b380b23ac46f523dbfcbef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_retained_engine2d_surface_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_retained_engine2d_surface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_retained_engine2d_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_retained_engine2d_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_retained_engine2d_surface_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_retained_engine2d_surface_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seeds once, replays exact damage, and leaves an idle frame untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_retained_engine2d_surface_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a malformed none plan instead of silently idling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
