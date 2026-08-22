# Primary Pointer Compatibility Suppression

> Verifies the browser pointer compatibility suppression behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primary Pointer Compatibility Suppression

Verifies the browser pointer compatibility suppression behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser pointer compatibility suppression behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Primary pointer compatibility suppression

#### should suppress compatibility mouse events after canceled pointerdown

- Verify: should suppress compatibility mouse events after canceled pointerdown
   - HTML capture: after_step
- Open the same canceling button in hosted and isolated renderers
   - HTML capture: after_step
   - Evidence: HTML text verified by 2 expected checks
   - Expected: hosted.browser.current_title equals ``
   - Expected: worker.browser.current_title equals ``
- Press the primary pointer on both buttons
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: hosted_down.semantic_target_id equals `target`
   - Expected: hosted_down.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted.browser.current_title equals `pointerdown,`
   - Expected: worker.browser.current_title equals `pointerdown,`
- Release the primary pointer over the original targets
   - HTML capture: after_step
   - Evidence: HTML text verified by 2 expected checks
   - Expected: hosted_up.semantic_target_id equals `target`
   - Expected: hosted_up.callback_count equals `2)  # oracle: pinned constant asserted by this scenario`
- Observe pointer click order and suppressed compatibility mouse events
   - HTML capture: after_step
   - Evidence: HTML text verified by 8 expected checks
   - Expected: hosted.browser.current_title equals `expected_events`
   - Expected: worker.browser.current_title equals `expected_events`
   - Expected: hosted.browser.dom_callback_count equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: worker.browser.dom_callback_count equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted.pressed_target_id equals ``
   - Expected: worker.pressed_target_id equals ``
   - Expected: hosted.browser.pending_request_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: worker.browser.pending_request_count() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008
step("Verify: should suppress compatibility mouse events after canceled pointerdown")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open the same canceling button in hosted and isolated renderers")
var hosted = HostedWebContentSession.create(
    901, POINTER_COMPATIBILITY_HTML, 80, 40
)
var worker = HostedBrowserRendererWorkerSession.create(80, 40)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: POINTER_COMPATIBILITY_HTML
)).ok).to_be(true)
expect(hosted.browser.current_title).to_equal("")
expect(worker.browser.current_title).to_equal("")

step("Press the primary pointer on both buttons")
val hosted_down = hosted.dispatch_pointer_at(1, 4, 4, true)
val worker_down = worker.handle(BrowserRendererMessage(
    kind: "pointer", generation: 7, request_id: 3,
    payload: "P1\t1\t4\t4\t1"
))
expect(hosted_down.semantic_target_id).to_equal("target")
expect(hosted_down.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(worker_down.ok).to_be(true)
expect(hosted.browser.current_title).to_equal("pointerdown,")
expect(worker.browser.current_title).to_equal("pointerdown,")
expect(hosted.pressed_compat_mouse_suppressed).to_be(true)
expect(worker.pressed_compat_mouse_suppressed).to_be(true)

step("Release the primary pointer over the original targets")
val hosted_up = hosted.dispatch_pointer_at(2, 4, 4, false)
val worker_up = worker.handle(BrowserRendererMessage(
    kind: "pointer", generation: 7, request_id: 4,
    payload: "P1\t2\t4\t4\t0"
))
expect(hosted_up.semantic_target_id).to_equal("target")
expect(hosted_up.callback_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(worker_up.ok).to_be(true)

step("Observe pointer click order and suppressed compatibility mouse events")
val expected_events = "pointerdown,pointerup,click,"
expect(hosted.browser.current_title).to_equal(expected_events)
expect(worker.browser.current_title).to_equal(expected_events)
expect(hosted.browser.dom_callback_count).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(worker.browser.dom_callback_count).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(hosted.pressed_target_id).to_equal("")
expect(worker.pressed_target_id).to_equal("")
expect(hosted.pressed_compat_mouse_suppressed).to_be(false)
expect(worker.pressed_compat_mouse_suppressed).to_be(false)
expect(hosted.browser.pending_request_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(worker.browser.pending_request_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
hosted.close()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c11986b6b60921366c743d18422210ce1fdcb6932f3e14b7d0d5190f2189f82`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c11986b6b60921366c743d18422210ce1fdcb6932f3e14b7d0d5190f2189f82`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c11986b6b60921366c743d18422210ce1fdcb6932f3e14b7d0d5190f2189f82`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should suppress compatibility mouse events after canceled pointerdown' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
