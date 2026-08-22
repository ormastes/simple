# Stop Preserves Partial Document Focus

> Verifies the browser stop partial focus behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stop Preserves Partial Document Focus

Verifies the browser stop partial focus behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_stop_partial_focus_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser stop partial focus behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Stop preserves partial document focus

#### should retain focus and selection while retiring transient state

- Verify: should retain focus and selection while retiring transient state
   - HTML capture: after_step
- Open the same partial document in hosted and isolated renderers
   - HTML capture: after_step
- Retain page selection while transient chrome state is armed
   - HTML capture: after_step
- Activate Stop through hosted chrome and isolated authority
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: hosted_down.reason equals `chrome-pressed`
   - Expected: hosted_up.reason equals ``
   - Expected: hosted_up.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: decoded.status equals `message`
- Observe partial focus and selection with transient state retired
   - HTML capture: after_step
   - Evidence: HTML text verified by 10 expected checks
   - Expected: hosted.pressed_chrome_control equals ``
   - Expected: hosted.chrome_focus equals ``
   - Expected: worker.pressed_target_id equals ``
   - Expected: worker.pressed_chrome_control equals ``
   - Expected: worker.chrome_focus equals ``
   - Expected: worker.input_view_target_key equals `id:draft`
   - Expected: worker.input_view_start_byte equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: worker.caret_blink_epoch_ms equals `77)  # oracle: pinned constant asserted by this scenario`
   - Expected: worker.active_root_command_request_id equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: worker.active_command_capability equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-009 REQ-WEB-BROWSER-021
step("Verify: should retain focus and selection while retiring transient state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open the same partial document in hosted and isolated renderers")
var hosted = HostedWebContentSession.create(
    904, STOP_PARTIAL_HTML, 160, 64
)
var worker = HostedBrowserRendererWorkerSession.create(160, 64)
expect(worker.browser.open_html(
    "https://page.example.test/partial", STOP_PARTIAL_HTML
).is_ok()).to_be(true)
worker.initialized = true
expect(hosted.browser.can_stop_loading()).to_be(true)
expect(worker.browser.can_stop_loading()).to_be(true)

step("Retain page selection while transient chrome state is armed")
expect(hosted.browser.set_dom_text_selection(
    "draft", 1, 5
)).to_be(true)
expect(worker.browser.set_dom_text_selection(
    "draft", 1, 5
)).to_be(true)
worker.pressed_target_id = "draft"
worker.pressed_chrome_control = "stop"
worker.chrome_focus = "address"
worker.address_replace_on_text = true
worker.input_view_target_key = "id:draft"
worker.input_view_start_byte = 1
worker.caret_blink_epoch_ms = 77

step("Activate Stop through hosted chrome and isolated authority")
val hosted_down = hosted.dispatch_chrome_pointer(1, "stop", true)
val hosted_up = hosted.dispatch_chrome_pointer(2, "stop", false)
expect(hosted_down.reason).to_equal("chrome-pressed")
expect(hosted_up.reason).to_equal("")
expect(hosted_up.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario

val stop = browser_renderer_navigation_encode(
    19, 2, "stop", "", "", "", "", ""
)
expect(stop.ok).to_be(true)
val bound = browser_renderer_capability_bind_encoded(
    stop, 19, 2, 2, STOP_COMMAND_CAPABILITY
)
expect(bound.ok).to_be(true)
val decoded = browser_renderer_capability_decoder_feed(
    browser_renderer_capability_decoder_new(19), bound.wire
)
expect(decoded.status).to_equal("message")
val worker_stop = worker.handle(decoded.message)
expect(worker_stop.ok).to_be(true)

step("Observe partial focus and selection with transient state retired")
expect_partial_focus(hosted.browser)
expect_partial_focus(worker.browser)
expect(hosted.pressed_chrome_control).to_equal("")
expect(hosted.chrome_focus).to_equal("")
expect(hosted.address_replace_on_text).to_be(false)
expect(worker.pressed_target_id).to_equal("")
expect(worker.pressed_chrome_control).to_equal("")
expect(worker.chrome_focus).to_equal("")
expect(worker.address_replace_on_text).to_be(false)
expect(worker.input_view_target_key).to_equal("id:draft")
expect(worker.input_view_start_byte).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(worker.caret_blink_epoch_ms).to_equal(77)  # oracle: pinned constant asserted by this scenario
expect(worker.active_root_command_request_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(worker.active_command_capability).to_equal("")
hosted.close()
worker.close()
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

- Canonical SPipe generation for source `10bbf468287700e20e469427666ae56e1a00020fa760823c5ad56ea914ae554c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `10bbf468287700e20e469427666ae56e1a00020fa760823c5ad56ea914ae554c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `10bbf468287700e20e469427666ae56e1a00020fa760823c5ad56ea914ae554c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_stop_partial_focus_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_stop_partial_focus_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_stop_partial_focus_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_stop_partial_focus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_stop_partial_focus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_stop_partial_focus_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain focus and selection while retiring transient state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
