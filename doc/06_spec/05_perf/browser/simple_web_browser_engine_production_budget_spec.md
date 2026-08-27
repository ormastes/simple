# Production Simple Browser Performance and GC Budgets

> Measures exact production binaries for startup, render, frame, input,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production Simple Browser Performance and GC Budgets

Measures exact production binaries for startup, render, frame, input,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Measures exact production binaries for startup, render, frame, input,
cancellation, RSS, GC/lifecycle, and 10,000-cycle stability without per-frame
Engine2D/font recreation or unconditional readback.

## Scenarios

### Production Simple browser performance and GC budgets

#### should bind one animation clock to changed Draw IR and Engine2D pixels

- should bind one animation clock to changed Draw IR and Engine2D pixels
- Open at clock zero and require the SimpleReady title
- Advance to 16 milliseconds and require rAF timestamp 16
- Require stage Draw IR at 0,0 32x24 from red to blue
- Render exactly 768 red then blue pixels with zero skips


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should bind one animation clock to changed Draw IR and Engine2D pixels")
step("Open at clock zero and require the SimpleReady title")
step("Advance to 16 milliseconds and require rAF timestamp 16")
step("Require stage Draw IR at 0,0 32x24 from red to blue")
step("Render exactly 768 red then blue pixels with zero skips")
val evidence = _browser_budget_animation_evidence()
expect(evidence).to_equal(
    "initial_title=SimpleReady|raf_ms=16|revision_changed=true|" +
    "initial=html_ast:stage:rect:0,0,32,24,4293870660|" +
    "advanced=html_ast:stage:rect:0,0,32,24,4280640491|" +
    "render=0,0,3072,3072,768,0,768,0,false"
)
```

</details>

#### should count unchanged retained-frame reuse without duplicate stage work

- should count unchanged retained-frame reuse without duplicate stage work
   - Log capture: after_step
- Reuse parsed layout work across unchanged animation frames
   - Log capture: after_step
   - Evidence: log output verified by 7 expected checks
   - Expected: after.serialize_count equals `before_serialize`
   - Expected: after.parse_count equals `before_parse`
   - Expected: after.css_count equals `before_css`
   - Expected: after.style_count equals `before_style`
   - Expected: after.layout_count equals `before_layout`
   - Expected: after.paint_count equals `before_paint`
   - Expected: after.reuse_count equals `before_reuse + 1`
- Close the page and reclaim browser resources
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should count unchanged retained-frame reuse without duplicate stage work")
step("Reuse parsed layout work across unchanged animation frames")
var worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<main id='stable'>unchanged</main>"
)).ok).to_be(true)
val counters = worker.render_session.counters
val before_serialize = counters.serialize_count
val before_parse = counters.parse_count
val before_css = counters.css_count
val before_style = counters.style_count
val before_layout = counters.layout_count
val before_paint = counters.paint_count
val before_reuse = counters.reuse_count
val before_composition_revision = counters.composition_revision
expect(worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "16"
)).ok).to_be(true)
val after = worker.render_session.counters

expect(after.serialize_count).to_equal(before_serialize)
expect(after.parse_count).to_equal(before_parse)
expect(after.css_count).to_equal(before_css)
expect(after.style_count).to_equal(before_style)
expect(after.layout_count).to_equal(before_layout)
expect(after.paint_count).to_equal(before_paint)
expect(after.reuse_count).to_equal(before_reuse + 1)
expect(after.composition_revision).to_equal(
    before_composition_revision
)
step("Close the page and reclaim browser resources")
worker.close()
expect(
    worker.render_session.counters.retained_command_count
).to_equal(0)
```

</details>

#### should meet warm cold startup first-render and navigation budgets

- should meet warm cold startup first-render and navigation budgets
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should meet warm cold startup first-render and navigation budgets")
_browser_budget_fixture()
_check_budget_row()
_require_production_budget_evidence()
```

</details>

#### should meet changed unchanged frame and input-to-present budgets

- should meet changed unchanged frame and input-to-present budgets
   - Artifact capture: after_step
- Run animation pointer keyboard text and scroll workloads
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should meet changed unchanged frame and input-to-present budgets")
_browser_budget_fixture()
step("Run animation pointer keyboard text and scroll workloads")
_require_animation_frame_receipt()
```

</details>

#### should stabilize heap RSS and browser resources over ten thousand cycles

- should stabilize heap RSS and browser resources over ten thousand cycles
   - Artifact capture: after_step
- Run ten thousand navigation interaction and animation cycles
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should stabilize heap RSS and browser resources over ten thousand cycles")
_browser_budget_fixture()
step("Run ten thousand navigation interaction and animation cycles")
_check_resource_reclaimed()
_require_animation_resource_receipt()
```

</details>

<details>
<summary>Advanced: should keep GC pauses within frame budgets and reject stale callbacks</summary>

#### should keep GC pauses within frame budgets and reject stale callbacks

- should keep GC pauses within frame budgets and reject stale callbacks
- Measure GC pauses callback queues and post-cancel activity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should keep GC pauses within frame budgets and reject stale callbacks")
_browser_budget_fixture()
step("Measure GC pauses callback queues and post-cancel activity")
_check_resource_reclaimed()
_require_animation_resource_receipt()
```

</details>


</details>

<details>
<summary>Advanced: should create Engine2D device and font state once and release it once</summary>

#### should create Engine2D device and font state once and release it once

- should create Engine2D device and font state once and release it once
- Inspect Engine2D device font render-session and readback counters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should create Engine2D device and font state once and release it once")
_browser_budget_fixture()
step("Inspect Engine2D device font render-session and readback counters")
_check_resource_reclaimed()
_require_production_budget_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should block regressions above five percent and cap verification cycles</summary>

#### should block regressions above five percent and cap verification cycles

- should block regressions above five percent and cap verification cycles
- Compare production receipt with the recorded baseline
- Record one final result per gate and stop after three fix cycles


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("should block regressions above five percent and cap verification cycles")
step("Compare production receipt with the recorded baseline")
step("Record one final result per gate and stop after three fix cycles")
_require_production_budget_evidence()
```

</details>


</details>

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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9114e1c8eb63f7976e13208f99bb9fbae6a421b50f2c68408110644b8767a5fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9114e1c8eb63f7976e13208f99bb9fbae6a421b50f2c68408110644b8767a5fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9114e1c8eb63f7976e13208f99bb9fbae6a421b50f2c68408110644b8767a5fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl
mirror: doc/06_spec/05_perf/browser/simple_web_browser_engine_production_budget_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/browser/simple_web_browser_engine_production_budget_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/browser/simple_web_browser_engine_production_budget_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:174:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind one animation clock to changed Draw IR and Engine2D pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:192:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should count unchanged retained-frame reuse without duplicate stage work' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:192:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should count unchanged retained-frame reuse without duplicate stage work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:235:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should meet warm cold startup first-render and navigation budgets' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:245:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should meet changed unchanged frame and input-to-present budgets' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:245:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should meet changed unchanged frame and input-to-present budgets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:255:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stabilize heap RSS and browser resources over ten thousand cycles' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:255:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should stabilize heap RSS and browser resources over ten thousand cycles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl:264:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep GC pauses within frame budgets and reject stale callbacks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
