# Hosted Browser Compositor Revision Cache Specification

> Tests covering hosted browser compositor revision reuse.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Browser Compositor Revision Cache Specification

## Scenarios

### hosted browser compositor revision reuse

#### reuses an unchanged frame and renders a changed revision

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reuses an unchanged frame and renders a changed revision
   - Expected: initial_frame.ok is true
   - Expected: unchanged_frame.ok is true
   - Expected: reused.pixels equals `first.pixels`
   - Expected: raster.revision_render_count equals `1`
   - Expected: raster.revision_reuse_count equals `1`
   - Expected: changed_render.pixels == first.pixels is false
   - Expected: raster.revision_render_count equals `2`
   - Expected: raster.revision_reuse_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reuses an unchanged frame and renders a changed revision")
var worker = HostedBrowserRendererWorkerSession.create(16, 16)
val initial = worker.handle(BrowserRendererCapabilityMessage(
    kind: "init",
    generation: 7,
    request_id: 2,
    root_command_request_id: 2,
    command_capability: "11111111111111111111111111111111",
    payload: "<main style='width:16px;height:16px;background:#2563eb'></main>"
))
val unchanged = worker.handle(BrowserRendererCapabilityMessage(
    kind: "advance",
    generation: 7,
    request_id: 3,
    root_command_request_id: 3,
    command_capability: "22222222222222222222222222222222",
    payload: "A1\t16"
))
val initial_frame = decode_worker_frame(initial.wire)
val unchanged_frame = decode_worker_frame(unchanged.wire)
expect(initial_frame.ok).to_equal(true)
expect(unchanged_frame.ok).to_equal(true)
expect(unchanged_frame.composition_revision).to_equal(
    initial_frame.composition_revision
)

var raster = Engine2dCompositorBackend.create_named(
    16, 16, "software")
val first = raster.render_draw_ir_composition_resources_revision(
    initial_frame.composition, initial_frame.image_resources,
    7, initial_frame.composition_revision)
val reused = raster.render_draw_ir_composition_resources_revision(
    unchanged_frame.composition, unchanged_frame.image_resources,
    7, unchanged_frame.composition_revision)
expect(reused.pixels).to_equal(first.pixels)
expect(raster.revision_render_count).to_equal(1)
expect(raster.revision_reuse_count).to_equal(1)

expect(worker.browser.eval_script(
    "document.body.innerHTML = '<main style=\"width:16px;height:16px;background:#dc2626\"></main>'"
).is_ok()).to_equal(true)
val changed = worker.handle(BrowserRendererCapabilityMessage(
    kind: "advance",
    generation: 7,
    request_id: 4,
    root_command_request_id: 4,
    command_capability: "33333333333333333333333333333333",
    payload: "A1\t32"
))
val changed_frame = decode_worker_frame(changed.wire)
expect(changed_frame.composition_revision).to_be_greater_than(
    unchanged_frame.composition_revision
)
val changed_render = raster.render_draw_ir_composition_resources_revision(
    changed_frame.composition, changed_frame.image_resources,
    7, changed_frame.composition_revision)
expect(changed_render.pixels == first.pixels).to_equal(false)
expect(raster.revision_render_count).to_equal(2)
expect(raster.revision_reuse_count).to_equal(1)
raster.shutdown()
worker.close()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted browser compositor revision reuse.
- hosted browser compositor revision reuse

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f6b5a3208b3c75d1de91de67debdd7ee753fcac4b943cafafc5889cf25fb4f24`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6b5a3208b3c75d1de91de67debdd7ee753fcac4b943cafafc5889cf25fb4f24`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6b5a3208b3c75d1de91de67debdd7ee753fcac4b943cafafc5889cf25fb4f24`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl
mirror: doc/06_spec/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses an unchanged frame and renders a changed revision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
