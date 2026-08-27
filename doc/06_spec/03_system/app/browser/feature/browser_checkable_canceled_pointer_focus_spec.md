# Checkable Canceled-Pointer Focus Preservation

> A canceled primary pointerdown still permits the same-target click and the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Checkable Canceled-Pointer Focus Preservation

A canceled primary pointerdown still permits the same-target click and the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A canceled primary pointerdown still permits the same-target click and the
checkbox input/change defaults, but it must not move focus from an existing
text input. Hosted and isolated renderer paths must expose the same exact
event order and focused target.

## Scenarios

### Checkable canceled-pointer focus preservation

#### should preserve text focus while activating the checkbox

- should preserve text focus while activating the checkbox
   - HTML capture: after_step
- Open the same text input and checkbox in hosted and isolated renderers
   - HTML capture: after_step
   - Evidence: HTML text verified by 2 expected checks
   - Expected: hosted.browser.current_title equals ``
   - Expected: worker.browser.current_title equals ``
- Focus both text inputs through the primary pointer
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: hosted_focus_down.semantic_target_id equals `keep`
   - Expected: hosted_focus_up.semantic_target_id equals `keep`
   - Expected: hosted.browser.current_title equals `focus,`
   - Expected: worker.browser.current_title equals `focus,`
- Activate both checkboxes after canceling their pointerdown events
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: hosted_choice_down.semantic_target_id equals `choice`
   - Expected: hosted_choice_down.callback_count equals `1`
   - Expected: hosted_choice_up.semantic_target_id equals `choice`
   - Expected: hosted_choice_up.callback_count equals `3`
- Observe checkable order and preserved text focus
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: hosted.browser.current_title equals `expected_events`
   - Expected: worker.browser.current_title equals `expected_events`
   - Expected: hosted.browser.dom_callback_count equals `5`
   - Expected: worker.browser.dom_callback_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 81 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve text focus while activating the checkbox")
step("Open the same text input and checkbox in hosted and isolated renderers")
var hosted = HostedWebContentSession.create(
    902, CHECKABLE_CANCELED_POINTER_FOCUS_HTML, 80, 48
)
var worker = HostedBrowserRendererWorkerSession.create(80, 48)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 13, request_id: 2,
    payload: CHECKABLE_CANCELED_POINTER_FOCUS_HTML
)).ok).to_be(true)
expect(hosted.browser.current_title).to_equal("")
expect(worker.browser.current_title).to_equal("")

step("Focus both text inputs through the primary pointer")
val hosted_focus_down = hosted.dispatch_pointer_at(1, 4, 4, true)
val hosted_focus_up = hosted.dispatch_pointer_at(2, 4, 4, false)
val worker_focus_down = worker.handle(BrowserRendererMessage(
    kind: "pointer", generation: 13, request_id: 3,
    payload: "P1\t1\t4\t4\t1"
))
val worker_focus_up = worker.handle(BrowserRendererMessage(
    kind: "pointer", generation: 13, request_id: 4,
    payload: "P1\t2\t4\t4\t0"
))
expect(hosted_focus_down.semantic_target_id).to_equal("keep")
expect(hosted_focus_up.semantic_target_id).to_equal("keep")
expect(worker_focus_down.ok).to_be(true)
expect(worker_focus_up.ok).to_be(true)
expect(hosted.browser.current_title).to_equal("focus,")
expect(worker.browser.current_title).to_equal("focus,")

step("Activate both checkboxes after canceling their pointerdown events")
val hosted_choice_down = hosted.dispatch_pointer_at(3, 4, 28, true)
val hosted_choice_up = hosted.dispatch_pointer_at(4, 4, 28, false)
val worker_choice_down = worker.handle(BrowserRendererMessage(
    kind: "pointer", generation: 13, request_id: 5,
    payload: "P1\t3\t4\t28\t1"
))
val worker_choice_up = worker.handle(BrowserRendererMessage(
    kind: "pointer", generation: 13, request_id: 6,
    payload: "P1\t4\t4\t28\t0"
))
expect(hosted_choice_down.semantic_target_id).to_equal("choice")
expect(hosted_choice_down.callback_count).to_equal(1)
expect(hosted_choice_up.semantic_target_id).to_equal("choice")
expect(hosted_choice_up.callback_count).to_equal(3)
expect(worker_choice_down.ok).to_be(true)
expect(worker_choice_up.ok).to_be(true)

step("Observe checkable order and preserved text focus")
val expected_events = "focus,pointerdown,click,input,change,"
expect(hosted.browser.current_title).to_equal(expected_events)
expect(worker.browser.current_title).to_equal(expected_events)
val hosted_root = hosted.browser.dom_root()
val worker_root = worker.browser.dom_root()
val hosted_index = system_browser_dom_identity_index(hosted.browser)
val worker_index = system_browser_dom_identity_index(worker.browser)
expect(system_dom_focused_route(
    hosted_root, hosted_index
).node_id).to_equal(system_dom_route(hosted_index, "keep").node_id)
expect(system_dom_focused_route(
    worker_root, worker_index
).node_id).to_equal(system_dom_route(worker_index, "keep").node_id)
val hosted_choice = be_dom_path_for_route(
    hosted_root, hosted_index, system_dom_route(hosted_index, "choice")
)
val worker_choice = be_dom_path_for_route(
    worker_root, worker_index, system_dom_route(worker_index, "choice")
)
expect(hosted_choice.len()).to_be_greater_than(0)
expect(worker_choice.len()).to_be_greater_than(0)
expect(be_dom_has_attr(
    hosted_choice[hosted_choice.len() - 1], "checked"
)).to_be(true)
expect(be_dom_has_attr(
    worker_choice[worker_choice.len() - 1], "checked"
)).to_be(true)
expect(hosted.browser.dom_callback_count).to_equal(5)
expect(worker.browser.dom_callback_count).to_equal(5)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67dde46c6a8b2bc17988709c425d50d0c2c3e26c3fb76871bd54c76f66c09cf7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67dde46c6a8b2bc17988709c425d50d0c2c3e26c3fb76871bd54c76f66c09cf7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67dde46c6a8b2bc17988709c425d50d0c2c3e26c3fb76871bd54c76f66c09cf7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve text focus while activating the checkbox' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve text focus while activating the checkbox' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
