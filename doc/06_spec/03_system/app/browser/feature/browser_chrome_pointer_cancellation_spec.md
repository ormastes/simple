# Browser Chrome Pointer Cancellation

> Proves navigation chrome and page-to-page ownership replacement release the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Chrome Pointer Cancellation

Proves navigation chrome and page-to-page ownership replacement release the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves navigation chrome and page-to-page ownership replacement release the
previous renderer-owned page press exactly once, using the prior press receipt.
The retained page remains unchanged through canonical Draw IR and Engine2D.

## Scenarios

### Browser chrome pointer cancellation

#### should cancel a page press before navigation chrome owns input

- should cancel a page press before navigation chrome owns input
   - GUI capture: after_step (HTML preferred when available)
- Press a renderer-owned page target
   - GUI capture: after_step (HTML preferred when available)
- Cancel through navigation chrome state
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: chrome.reason equals `chrome-pressed`
   - Expected: registry.pressed_event_id equals `402`
- Observe one canonical pointer release
   - GUI capture: after_step (HTML preferred when available)
- Render without stale pressed state
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: registry.pressed_window_id equals `0`
   - Expected: registry.pressed_event_id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cancel a page press before navigation chrome owns input")
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
expect(registry.pressed_event_id).to_equal(402)

step("Observe one canonical pointer release")
check_renderer_release_sent(
    registry, CHROME_CANCEL_WINDOW, 401
)

step("Render without stale pressed state")
check_pressed_state_cleared(registry)
expect(registry.dispatch_chrome_pointer(
    403, CHROME_CANCEL_WINDOW, "address", false
).reason).to_equal("address-focused")
expect(registry.pressed_window_id).to_equal(0)
expect(registry.pressed_event_id).to_equal(0)
expect(registry.close()).to_be(true)
```

</details>

<details>
<summary>Advanced: should release the prior renderer before a second page owns input</summary>

#### should release the prior renderer before a second page owns input

- should release the prior renderer before a second page owns input
- Press the first renderer-owned page target
- Replace ownership with a second page renderer
   - Expected: replacement.callback_count equals `1`
   - Expected: registry.pressed_event_id equals `502`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should release the prior renderer before a second page owns input")
var registry = setup_chrome_cancel_fixture()
step("Press the first renderer-owned page target")
check_page_press_owned(
    registry, CHROME_CANCEL_WINDOW, 501
)

step("Replace ownership with a second page renderer")
val replacement = registry.dispatch_pointer(
    502, CHROME_CANCEL_SECOND_WINDOW, 4, 4, true
)
expect(replacement.callback_count).to_equal(1)
expect(registry.pressed_window_id).to_equal(
    CHROME_CANCEL_SECOND_WINDOW
)
expect(registry.pressed_event_id).to_equal(502)
check_renderer_release_sent(
    registry, CHROME_CANCEL_WINDOW, 501
)
_await_chrome_cancel_window(
    registry, CHROME_CANCEL_SECOND_WINDOW
)
expect(registry.dispatch_pointer(
    503, CHROME_CANCEL_SECOND_WINDOW, 4, 4, false
).callback_count).to_equal(1)
expect(registry.close()).to_be(true)
```

</details>


</details>

<details>
<summary>Advanced: should drop an old generation release before same-window replacement</summary>

#### should drop an old generation release before same-window replacement

- should drop an old generation release before same-window replacement
- Arm page and pending-release ownership on the old generation
- Replace the renderer generation at the teardown boundary
   - Expected: registry._begin_site_swap(index, 100000) equals `none`
   - Expected: registry.pressed_window_id equals `0`
   - Expected: registry.pressed_event_id equals `0`
   - Expected: registry.pending_cancel_window_id equals `0`
   - Expected: registry.pending_cancel_event_id equals `0`
- Reject the stale release for the replacement generation
   - Expected: registry.pointer_cancel_receipt_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should drop an old generation release before same-window replacement")
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
expect(registry.pressed_window_id).to_equal(0)
expect(registry.pressed_event_id).to_equal(0)
expect(registry.pending_cancel_window_id).to_equal(0)
expect(registry.pending_cancel_event_id).to_equal(0)

step("Reject the stale release for the replacement generation")
registry.cancel_pointer_state(999)
expect(registry.pointer_cancel_receipt_count).to_equal(0)
expect(registry.entries[index].renderer.pointer_pressed).to_be(false)
expect(
    registry.entries[index].renderer.pending_pointer_cancel_event_id
).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ad8a41ff2d6893df6e1017e04824017458559f48c54061723a71ee9a73fa71f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ad8a41ff2d6893df6e1017e04824017458559f48c54061723a71ee9a73fa71f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ad8a41ff2d6893df6e1017e04824017458559f48c54061723a71ee9a73fa71f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:182:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cancel a page press before navigation chrome owns input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should cancel a page press before navigation chrome owns input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:215:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should release the prior renderer before a second page owns input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:215:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should release the prior renderer before a second page owns input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:246:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should drop an old generation release before same-window replacement' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl:246:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should drop an old generation release before same-window replacement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
