# Pending Home address truth

> Verifies the browser home pending address behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pending Home address truth

Verifies the browser home pending address behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_home_pending_address_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser home pending address behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Pending Home address truth

#### should publish only an admitted Home target without committing early

- Verify: should publish only an admitted Home target without committing early
- Commit one old document and configure canonical Home owners
- Leave a distinct abandoned address draft focused
- Admit Home through BrowserSession UI worker and parent registry
   - Expected: home_down.reason equals `chrome-pressed`
   - Expected: home_up.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: home_up.reason equals ``
- Show pending Home preserve commit and retain state on rejection
   - Expected: session.address_draft equals `HOME_TARGET_URL`
   - Expected: session.pending_url equals `HOME_TARGET_URL`
   - Expected: session.current_url equals `HOME_OLD_URL`
   - Expected: session.history.len() equals `session_history_len`
   - Expected: session.current_index equals `session_history_index`
   - Expected: worker.chrome_focus equals ``
   - Expected: worker.browser.address_draft equals `HOME_TARGET_URL`
   - Expected: worker.browser.pending_url equals `HOME_TARGET_URL`
   - Expected: worker.browser.current_url equals `HOME_OLD_URL`
   - Expected: worker.browser.history.len() equals `worker_history_len`
   - Expected: rejected_session.home_url equals `HOME_TARGET_URL`
   - Expected: rejected_session.current_url equals `HOME_OLD_URL`
   - Expected: rejected_session.history.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: rejected_down.reason equals `chrome-pressed`
   - Expected: rejected_up.callback_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rejected_up.reason equals `home-unconfigured`
   - Expected: busy_home.callback_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: busy_home.reason equals `renderer-busy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 235 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-009 REQ-WEB-BROWSER-010
step("Verify: should publish only an admitted Home target without committing early")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Commit one old document and configure canonical Home owners")
var session = BrowserSession.new()
expect(session.open_html(
    HOME_OLD_URL, HOME_OLD_HTML
).unwrap()).to_be(true)
expect(session.try_set_home_url(HOME_TARGET_URL)).to_be(true)
val session_history_len = session.history.len()
val session_history_index = session.current_index

var worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: HOME_OLD_HTML
)).ok).to_be(true)
expect(worker.browser.open_html(
    HOME_OLD_URL, HOME_OLD_HTML
).unwrap()).to_be(true)
val worker_history_len = worker.browser.history.len()
val worker_history_index = worker.browser.current_index

var registry = home_registry(HOME_TARGET_URL)
val registry_history_urls = (
    registry.entries[0].renderer.history_urls
)
val registry_history_index = (
    registry.entries[0].renderer.history_index
)

step("Leave a distinct abandoned address draft focused")
expect(session.apply_address_update(
    "", HOME_ABANDONED_DRAFT, true
).unwrap()).to_equal(HOME_ABANDONED_DRAFT)
val session_revision = session.ui_access_revision
worker.browser.address_draft = HOME_ABANDONED_DRAFT
worker.chrome_focus = "address"
worker.address_replace_on_text = true
val worker_revision = worker.browser.ui_access_revision
expect(registry.address_text(HOME_WINDOW_ID)).to_equal(
    HOME_ABANDONED_DRAFT
)
expect(registry.entries[0].address_editing).to_be(true)

step("Admit Home through BrowserSession UI worker and parent registry")
val session_home = session.ui_access_act(
    WinTextActionRequest(
        target_id: "browser:session#home", action: "click",
        text_value: "", x: 0, y: 0
    )
)
expect(session_home.ok).to_be(true)

val worker_home = browser_renderer_navigation_encode(
    7, 3, "home", HOME_TARGET_URL, "GET", "", "", ""
)
expect(worker_home.ok).to_be(true)
val worker_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), worker_home.wire
)
expect(worker.handle(worker_message.message).ok).to_be(true)

val home_down = registry.dispatch_chrome_pointer(
    1, HOME_WINDOW_ID, "home", true
)
expect(home_down.reason).to_equal("chrome-pressed")
expect(registry.entries[0].address_editing).to_be(true)
val home_up = registry.dispatch_chrome_pointer(
    2, HOME_WINDOW_ID, "home", false
)
expect(home_up.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(home_up.reason).to_equal("")

step("Show pending Home preserve commit and retain state on rejection")
expect(session.address_draft).to_equal(HOME_TARGET_URL)
expect(session.ui_access_snapshot().nodes[7].text_value).to_equal(
    HOME_TARGET_URL
)
expect(session.ui_access_snapshot().nodes[7].focused).to_be(false)
expect(session.pending_url).to_equal(HOME_TARGET_URL)
expect(session.ui_access_revision).to_equal(
    session_revision + 1
)
expect(session.current_url).to_equal(HOME_OLD_URL)
expect(session.history.len()).to_equal(session_history_len)
expect(session.current_index).to_equal(session_history_index)

expect(worker.chrome_focus).to_equal("")
expect(worker.address_replace_on_text).to_be(false)
expect(worker.browser.address_draft).to_equal(HOME_TARGET_URL)
expect(worker.browser.pending_url).to_equal(HOME_TARGET_URL)
expect(worker.browser.ui_access_revision).to_equal(
    worker_revision + 1
)
expect(worker.browser.current_url).to_equal(HOME_OLD_URL)
expect(worker.browser.history.len()).to_equal(worker_history_len)
expect(worker.browser.current_index).to_equal(
    worker_history_index
)

expect(registry.address_text(HOME_WINDOW_ID)).to_equal(
    HOME_TARGET_URL
)
expect(registry.entries[0].address_editing).to_be(false)
expect(
    registry.entries[0].address_replace_on_text
).to_be(false)
expect(
    registry.entries[0].renderer.navigation_permit.url
).to_equal(HOME_TARGET_URL)
expect(registry.document_url(HOME_WINDOW_ID)).to_equal(
    HOME_OLD_URL
)
expect(
    registry.entries[0].renderer.history_urls
).to_equal(registry_history_urls)
expect(
    registry.entries[0].renderer.history_index
).to_equal(registry_history_index)

var rejected_session = BrowserSession.new()
expect(rejected_session.open_html(
    HOME_OLD_URL, HOME_OLD_HTML
).unwrap()).to_be(true)
expect(rejected_session.try_set_home_url(
    HOME_TARGET_URL
)).to_be(true)
rejected_session.address_draft = HOME_ABANDONED_DRAFT
val rejected_revision = rejected_session.ui_access_revision
expect(rejected_session.try_set_home_url(
    "javascript:alert(1)"
)).to_be(false)
expect(rejected_session.home_url).to_equal(HOME_TARGET_URL)
expect(rejected_session.begin_network_navigation(
    "javascript:alert(1)", "GET", "", "", ""
).unwrap_err()).to_equal("unsupported navigation scheme")
expect(rejected_session.address_draft).to_equal(
    HOME_ABANDONED_DRAFT
)
expect(rejected_session.ui_access_revision).to_equal(
    rejected_revision
)
expect(rejected_session.current_url).to_equal(HOME_OLD_URL)
expect(rejected_session.history.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario

var rejected_registry = home_registry(
    "javascript:alert(1)"
)
val rejected_down = rejected_registry.dispatch_chrome_pointer(
    3, HOME_WINDOW_ID, "home", true
)
expect(rejected_down.reason).to_equal("chrome-pressed")
expect(rejected_registry.entries[0].address_editing).to_be(true)
val rejected_up = rejected_registry.dispatch_chrome_pointer(
    4, HOME_WINDOW_ID, "home", false
)
expect(rejected_up.callback_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(rejected_up.reason).to_equal("home-unconfigured")
expect(rejected_registry.address_text(
    HOME_WINDOW_ID
)).to_equal(HOME_ABANDONED_DRAFT)
expect(
    rejected_registry.entries[0].address_editing
).to_be(true)
expect(
    rejected_registry.entries[0].address_replace_on_text
).to_be(true)
expect(rejected_registry.document_url(
    HOME_WINDOW_ID
)).to_equal(HOME_OLD_URL)
expect(
    rejected_registry.entries[0].renderer.history_urls
).to_equal([HOME_OLD_URL])
expect(
    rejected_registry.entries[0].renderer.history_index
).to_equal(0)  # oracle: pinned constant asserted by this scenario

var busy_registry = home_registry(HOME_TARGET_URL)
var busy_entry = busy_registry.entries[0]
busy_entry.renderer.pending_wire = "partially-written"
busy_entry.renderer.pending_wire_offset = 1
busy_registry.entries[0] = busy_entry
val busy_revision = busy_entry.mutation_revision
expect(busy_registry.dispatch_chrome_pointer(
    5, HOME_WINDOW_ID, "home", true
).reason).to_equal("chrome-pressed")
val busy_home = busy_registry.dispatch_chrome_pointer(
    6, HOME_WINDOW_ID, "home", false
)
expect(busy_home.callback_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(busy_home.reason).to_equal("renderer-busy")
expect(busy_registry.address_text(
    HOME_WINDOW_ID
)).to_equal(HOME_ABANDONED_DRAFT)
expect(busy_registry.entries[0].address_editing).to_be(true)
expect(
    busy_registry.entries[0].address_replace_on_text
).to_be(true)
expect(
    busy_registry.entries[0].mutation_revision
).to_equal(busy_revision)
expect(busy_registry.document_url(
    HOME_WINDOW_ID
)).to_equal(HOME_OLD_URL)
expect(
    busy_registry.entries[0].renderer.history_urls
).to_equal([HOME_OLD_URL])

var address_session = BrowserSession.new()
expect(address_session.open_html(
    HOME_OLD_URL, HOME_OLD_HTML
).unwrap()).to_be(true)
address_session.address_draft = HOME_ABANDONED_DRAFT
val address_revision = address_session.ui_access_revision
expect(address_session.begin_network_navigation(
    "Example.COM/next", "GET", "", "", ""
).unwrap()).to_be(true)
expect(address_session.address_draft).to_equal(
    "https://Example.COM/next"
)
expect(address_session.ui_access_revision).to_equal(
    address_revision + 1
)
val unchanged_revision = address_session.ui_access_revision
expect(address_session.begin_network_navigation(
    "https://Example.COM/next", "GET", "", "", ""
).unwrap()).to_be(true)
expect(address_session.ui_access_revision).to_equal(
    unchanged_revision
)

close_home_registry(registry)
close_home_registry(rejected_registry)
close_home_registry(busy_registry)
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

- Canonical SPipe generation for source `74bba96c6672ddd3527bda2f7123923e47db1f37e3c0b4dacc74e979e18b068a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74bba96c6672ddd3527bda2f7123923e47db1f37e3c0b4dacc74e979e18b068a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74bba96c6672ddd3527bda2f7123923e47db1f37e3c0b4dacc74e979e18b068a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_home_pending_address_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_home_pending_address_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_home_pending_address_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_home_pending_address_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_home_pending_address_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_home_pending_address_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish only an admitted Home target without committing early' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
