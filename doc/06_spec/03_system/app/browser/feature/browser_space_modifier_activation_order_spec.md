# Space Activation Across Modifier Events

> Verifies the browser space modifier activation order behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Space Activation Across Modifier Events

Verifies the browser space modifier activation order behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser space modifier activation order behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Space activation across modifier events

#### should retain Space activation while Shift is pressed and released

- Verify: should retain Space activation while Shift is pressed and released
   - HTML capture: after_step
- Open the same keyboard button in hosted and isolated renderers
   - HTML capture: after_step
   - Evidence: HTML text verified by 2 expected checks
   - Expected: hosted.browser.current_title equals ``
   - Expected: worker.browser.current_title equals ``
- Focus both buttons through the host Tab route
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: hosted_tab.semantic_target_id equals `target`
   - Expected: hosted_tab.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted.browser.current_title equals `focus,`
   - Expected: worker.browser.current_title equals `focus,`
- Hold Space while pressing and releasing Shift on both buttons
   - HTML capture: after_step
   - Evidence: HTML text verified by 5 expected checks
   - Expected: hosted_space_down.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted_shift_down.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted_shift_up.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted.browser.current_title equals `held_events`
   - Expected: worker.browser.current_title equals `held_events`
- Release Space and observe ordered activation in both renderers
   - HTML capture: after_step
   - Evidence: HTML text verified by 7 expected checks
   - Expected: hosted_space_up.callback_count equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted.browser.current_title equals `expected_events`
   - Expected: worker.browser.current_title equals `expected_events`
   - Expected: hosted.browser.pending_space_activation_target equals ``
   - Expected: worker.browser.pending_space_activation_target equals ``
   - Expected: hosted.browser.dom_callback_count equals `6)  # oracle: pinned constant asserted by this scenario`
   - Expected: worker.browser.dom_callback_count equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 109 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-005 REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008
step("Verify: should retain Space activation while Shift is pressed and released")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open the same keyboard button in hosted and isolated renderers")
var hosted = HostedWebContentSession.create(
    903, SPACE_MODIFIER_ACTIVATION_HTML, 80, 40
)
var worker = HostedBrowserRendererWorkerSession.create(80, 40)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 17, request_id: 2,
    payload: SPACE_MODIFIER_ACTIVATION_HTML
)).ok).to_be(true)
expect(hosted.browser.current_title).to_equal("")
expect(worker.browser.current_title).to_equal("")

step("Focus both buttons through the host Tab route")
val hosted_tab = hosted.dispatch_key_with_shift(1, 9, true, false)
val worker_tab = worker.handle(BrowserRendererMessage(
    kind: "key", generation: 17, request_id: 3,
    payload: "K2\t1\t9\t1\t0"
))
expect(hosted_tab.semantic_target_id).to_equal("target")
expect(hosted_tab.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(worker_tab.ok).to_be(true)
expect(hosted.browser.current_title).to_equal("focus,")
expect(worker.browser.current_title).to_equal("focus,")

step("Hold Space while pressing and releasing Shift on both buttons")
val hosted_space_down = hosted.dispatch_key_with_shift(
    2, 32, true, false
)
val hosted_shift_down = hosted.dispatch_key_with_shift(
    3, 16, true, true
)
val hosted_shift_up = hosted.dispatch_key_with_shift(
    4, 16, false, false
)
val worker_space_down = worker.handle(BrowserRendererMessage(
    kind: "key", generation: 17, request_id: 4,
    payload: "K2\t2\t32\t1\t0"
))
val worker_shift_down = worker.handle(BrowserRendererMessage(
    kind: "key", generation: 17, request_id: 5,
    payload: "K2\t3\t16\t1\t1"
))
val worker_shift_up = worker.handle(BrowserRendererMessage(
    kind: "key", generation: 17, request_id: 6,
    payload: "K2\t4\t16\t0\t0"
))
expect(hosted_space_down.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(hosted_shift_down.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(hosted_shift_up.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(worker_space_down.ok).to_be(true)
expect(worker_shift_down.ok).to_be(true)
expect(worker_shift_up.ok).to_be(true)
val held_events = "focus,keydown,keydown,keyup,"
expect(hosted.browser.current_title).to_equal(held_events)
expect(worker.browser.current_title).to_equal(held_events)
expect(hosted.browser.pending_space_activation_target).to_equal(
    "target"
)
expect(worker.browser.pending_space_activation_target).to_equal(
    "target"
)

step("Release Space and observe ordered activation in both renderers")
val hosted_space_up = hosted.dispatch_key_with_shift(
    5, 32, false, false
)
val worker_space_up = worker.handle(BrowserRendererMessage(
    kind: "key", generation: 17, request_id: 7,
    payload: "K2\t5\t32\t0\t0"
))
val expected_events = (
    "focus,keydown,keydown,keyup,keyup,click,"
)
expect(hosted_space_up.callback_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(worker_space_up.ok).to_be(true)
expect(hosted.browser.current_title).to_equal(expected_events)
expect(worker.browser.current_title).to_equal(expected_events)
val hosted_root = hosted.browser.dom_root()
val worker_root = worker.browser.dom_root()
val hosted_index = system_browser_dom_identity_index(hosted.browser)
val worker_index = system_browser_dom_identity_index(worker.browser)
expect(system_dom_focused_route(
    hosted_root, hosted_index
).node_id).to_equal(system_dom_route(hosted_index, "target").node_id)
expect(system_dom_focused_route(
    worker_root, worker_index
).node_id).to_equal(system_dom_route(worker_index, "target").node_id)
val hosted_target = be_dom_path_for_route(
    hosted_root, hosted_index, system_dom_route(hosted_index, "target")
)
val worker_target = be_dom_path_for_route(
    worker_root, worker_index, system_dom_route(worker_index, "target")
)
expect(hosted_target.len()).to_be_greater_than(0)
expect(worker_target.len()).to_be_greater_than(0)
expect(be_dom_has_attr(
    hosted_target[hosted_target.len() - 1], "data-activated"
)).to_be(true)
expect(be_dom_has_attr(
    worker_target[worker_target.len() - 1], "data-activated"
)).to_be(true)
expect(hosted.browser.pending_space_activation_target).to_equal("")
expect(worker.browser.pending_space_activation_target).to_equal("")
expect(hosted.browser.dom_callback_count).to_equal(6)  # oracle: pinned constant asserted by this scenario
expect(worker.browser.dom_callback_count).to_equal(6)  # oracle: pinned constant asserted by this scenario
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

- Canonical SPipe generation for source `f21e17acf6c3c653cfa6f1bb53a14466999d925848e6e53faebc2aea9154663e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f21e17acf6c3c653cfa6f1bb53a14466999d925848e6e53faebc2aea9154663e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f21e17acf6c3c653cfa6f1bb53a14466999d925848e6e53faebc2aea9154663e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain Space activation while Shift is pressed and released' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
