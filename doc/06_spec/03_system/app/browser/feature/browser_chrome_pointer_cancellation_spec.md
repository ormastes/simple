# Browser Chrome Pointer Cancellation

> Verifies the browser chrome pointer cancellation behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Chrome Pointer Cancellation

Verifies the browser chrome pointer cancellation behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser chrome pointer cancellation behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Browser chrome pointer cancellation

#### should cancel a page press before navigation chrome owns input

- Verify: should cancel a page press before navigation chrome owns input
   - GUI capture: after_step (HTML preferred when available)
- Press a renderer-owned page target
   - GUI capture: after_step (HTML preferred when available)
- Cancel through navigation chrome state
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: chrome.reason equals `chrome-pressed`
   - Expected: registry.pressed_event_id equals `402)  # oracle: pinned constant asserted by this scenario`
- Observe one canonical pointer release
   - GUI capture: after_step (HTML preferred when available)
- Render without stale pressed state
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: registry.pressed_window_id equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry.pressed_event_id equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-009
step("Verify: should cancel a page press before navigation chrome owns input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var registry = setup_chrome_cancel_fixture()

step("Press a renderer-owned page target")
check_page_press_owned(
    registry, CHROME_CANCEL_WINDOW, 401
)

step("Cancel through navigation chrome state")
val chrome = registry.dispatch_chrome_pointer(
    402, CHROME_CANCEL_WINDOW, "address", true
)
expect(chrome.reason).to_equal("chrome-pressed")
expect(registry.pressed_event_id).to_equal(402)  # oracle: pinned constant asserted by this scenario

step("Observe one canonical pointer release")
check_renderer_release_sent(
    registry, CHROME_CANCEL_WINDOW, 401
)

step("Render without stale pressed state")
check_pressed_state_cleared(registry)
expect(registry.dispatch_chrome_pointer(
    403, CHROME_CANCEL_WINDOW, "address", false
).reason).to_equal("address-focused")
expect(registry.pressed_window_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(registry.pressed_event_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(registry.close()).to_be(true)
```

</details>

<details>
<summary>Advanced: should release the prior renderer before a second page owns input</summary>

#### should release the prior renderer before a second page owns input

- Verify: should release the prior renderer before a second page owns input
- Press the first renderer-owned page target
- Replace ownership with a second page renderer
   - Expected: replacement.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry.pressed_event_id equals `502)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-009
step("Verify: should release the prior renderer before a second page owns input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var registry = setup_chrome_cancel_fixture()
step("Press the first renderer-owned page target")
check_page_press_owned(
    registry, CHROME_CANCEL_WINDOW, 501
)

step("Replace ownership with a second page renderer")
val replacement = registry.dispatch_pointer(
    502, CHROME_CANCEL_SECOND_WINDOW, 4, 4, true
)
expect(replacement.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(registry.pressed_window_id).to_equal(
    CHROME_CANCEL_SECOND_WINDOW
)
expect(registry.pressed_event_id).to_equal(502)  # oracle: pinned constant asserted by this scenario
check_renderer_release_sent(
    registry, CHROME_CANCEL_WINDOW, 501
)
_await_chrome_cancel_window(
    registry, CHROME_CANCEL_SECOND_WINDOW
)
expect(registry.dispatch_pointer(
    503, CHROME_CANCEL_SECOND_WINDOW, 4, 4, false
).callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(registry.close()).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: should drop an old generation release before same-window replacement</summary>

#### should drop an old generation release before same-window replacement

- Verify: should drop an old generation release before same-window replacement
- Arm page and pending-release ownership on the old generation
- Replace the renderer generation at the teardown boundary
   - Expected: registry._begin_site_swap(index, 100000) equals `none`
   - Expected: registry.pressed_window_id equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry.pressed_event_id equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry.pending_cancel_window_id equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry.pending_cancel_event_id equals `0)  # oracle: pinned constant asserted by this scenario`
- Reject the stale release for the replacement generation
   - Expected: registry.pointer_cancel_receipt_count equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-009 REQ-WEB-BROWSER-021
step("Verify: should drop an old generation release before same-window replacement")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Arm page and pending-release ownership on the old generation")
var registry = setup_chrome_cancel_fixture()
val index = registry._index(CHROME_CANCEL_WINDOW)
expect(index).to_be_greater_than(-1)
var entry = registry.entries[index]
val old_generation = entry.renderer.generation
entry.renderer.navigation_permit = HostedBrowserNavigationPermit(
    active: true,
    url: "https://replacement.test/page",
    method: "GET",
    headers: "",
    body: "",
    content_type: "",
    redirect_count: 0
)
entry.renderer.site_lock = "https://old.test"
entry.renderer.site_swap_pending = true
entry.renderer.site_swap_site = "https://replacement.test"
entry.renderer.pointer_pressed = true
registry.entries[index] = entry
registry.pressed_window_id = CHROME_CANCEL_WINDOW
registry.pressed_event_id = 601
registry.pending_cancel_window_id = CHROME_CANCEL_WINDOW
registry.pending_cancel_event_id = 601

step("Replace the renderer generation at the teardown boundary")
expect(registry._begin_site_swap(index, 100000)).to_equal("none")
expect(
    registry.entries[index].renderer.generation
).to_be_greater_than(old_generation)
expect(registry.pressed_window_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(registry.pressed_event_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(registry.pending_cancel_window_id).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(registry.pending_cancel_event_id).to_equal(0)  # oracle: pinned constant asserted by this scenario

step("Reject the stale release for the replacement generation")
registry.cancel_pointer_state(999)
expect(registry.pointer_cancel_receipt_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(registry.entries[index].renderer.pointer_pressed).to_be(false)
expect(
    registry.entries[index].renderer.pending_pointer_cancel_event_id
).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(registry.close()).to_be(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fbe688c7f51e2f9e5b656216a66ac74ddb0f859bca534999873d857b98379604`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fbe688c7f51e2f9e5b656216a66ac74ddb0f859bca534999873d857b98379604`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fbe688c7f51e2f9e5b656216a66ac74ddb0f859bca534999873d857b98379604`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:192:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cancel a page press before navigation chrome owns input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:226:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should release the prior renderer before a second page owns input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:258:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should drop an old generation release before same-window replacement' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
