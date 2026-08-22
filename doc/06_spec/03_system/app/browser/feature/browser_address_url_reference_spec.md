# browser_address_url_reference_spec

> Verifies the browser address url reference behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_address_url_reference_spec

Verifies the browser address url reference behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-008, REQ-WEB-BROWSER-009 |
| Source | `test/03_system/app/browser/feature/browser_address_url_reference_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser address url reference behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Browser address URL-reference resolution

#### should resolve URL references before the worker boundary and reject invalid hosts atomically

- Verify: should resolve URL references before the worker boundary and reject invalid hosts atomically
- Resolve only URL-reference forms against the committed document
- Submit a root-relative address while retaining the committed page
   - Expected: session.pending_url equals `target_url`
   - Expected: session.current_url equals `committed_url`
   - Expected: session.history.len() equals `session_history`
   - Expected: session.current_url equals `target_url`
   - Expected: session.document_url equals `target_url`
   - Expected: hosted_submit.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: hosted.browser.pending_url equals `target_url`
   - Expected: hosted.browser.current_url equals `committed_url`
   - Expected: hosted.browser.history.len() equals `hosted_history`
- Send only the resolved absolute URL across the worker wire
   - Expected: registry_submit.callback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry_command.url equals `target_url`
   - Expected: registry.entries[0].renderer.history_index equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: worker.browser.pending_url equals `target_url`
   - Expected: worker.browser.current_url equals `committed_url`
- Reject an invalid absolute host without losing editable or committed state
   - Expected: rejected_hosted.chrome_focus equals `address`
   - Expected: rejected_hosted.browser.address_draft equals `invalid`
   - Expected: rejected_hosted.browser.current_url equals `committed_url`
   - Expected: invalid_registry.address_text(74) equals `invalid`
   - Expected: invalid_registry.document_url(74) equals `committed_url`
   - Expected: reason equals `stale document response`
   - Expected: worker.chrome_focus equals `address`
   - Expected: worker.browser.address_draft equals `invalid`
   - Expected: worker.browser.current_url equals `committed_url`
   - Expected: worker.browser.source_html equals `worker_source`
   - Expected: worker.browser.history equals `worker_history`
   - Expected: worker.browser.current_index equals `worker_index`
   - Expected: worker.browser.document_url equals `worker_document_url`
   - Expected: worker.browser.pending_url equals `worker_pending_url`
   - Expected: worker.pressed_target_id equals `committed-target`
   - Expected: worker.input_view_target_key equals `committed-input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 329 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-009
step("Verify: should resolve URL references before the worker boundary and reject invalid hosts atomically")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Resolve only URL-reference forms against the committed document")
val base = "https://example.test/a/page?old=1#old"
expect(normalize_browser_address_reference_url(
    base, "/next?x=1#ok"
).unwrap()).to_equal("https://example.test/next?x=1#ok")
expect(normalize_browser_address_reference_url(
    base, "?x=2"
).unwrap()).to_equal("https://example.test/a/page?x=2")
expect(normalize_browser_address_reference_url(
    base, "#new"
).unwrap()).to_equal(
    "https://example.test/a/page?old=1#new"
)
expect(normalize_browser_address_reference_url(
    base, "./child"
).unwrap()).to_equal("https://example.test/a/child")
expect(normalize_browser_address_reference_url(
    base, "../up"
).unwrap()).to_equal("https://example.test/up")
expect(normalize_browser_address_reference_url(
    base, "https://bad_host/"
).is_err()).to_be(true)

step("Submit a root-relative address while retaining the committed page")
val committed_url = "https://example.test/a/page"
val committed_html = "<html><body><p>committed</p></body></html>"
val target_url = "https://example.test/next?x=1#ok"
var session = BrowserSession.new()
expect(session.open_html(
    committed_url, committed_html
).is_ok()).to_be(true)
val session_history = session.history.len()
expect(session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: "/next?x=1#ok", x: 0, y: 0
)).ok).to_be(true)
val submitted = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "submit",
    text_value: "", x: 0, y: 0
))
expect(submitted.ok).to_be(true)
expect(session.pending_url).to_equal(target_url)
expect(session.current_url).to_equal(committed_url)
expect(session.current_body_html).to_equal(
    "<p>committed</p>"
)
expect(session.history.len()).to_equal(session_history)
val session_request = session.take_pending_request().unwrap()
expect(session_request.url).to_equal(
    "https://example.test/next?x=1"
)
val session_committed = session.commit_network_response(
    BrowserResponse.create(
        request_id: session_request.id,
        kind: "document",
        url: session_request.url,
        status: 200,
        headers: "Content-Type: text/html",
        body: "<html><body><p>fragment committed</p></body></html>",
        error: ""
    )
)
expect(session_committed.is_ok()).to_be(true)
expect(session.current_url).to_equal(target_url)
expect(session.document_url).to_equal(target_url)
expect(session.history[session.current_index].url).to_equal(
    target_url
)
expect(session.current_body_html).to_equal(
    "<p>fragment committed</p>"
)

var hosted = HostedWebContentSession.create(
    71, committed_html, 32, 16
)
expect(hosted.browser.open_html(
    committed_url, committed_html
).is_ok()).to_be(true)
val hosted_history = hosted.browser.history.len()
val _ = hosted.dispatch_chrome_pointer(1, "address", true)
val _ = hosted.dispatch_chrome_pointer(2, "address", false)
expect(hosted.dispatch_text(
    3, "/next?x=1#ok"
).callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
val hosted_submit = hosted.dispatch_key(4, 13, true)
expect(hosted_submit.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(hosted.browser.pending_url).to_equal(target_url)
expect(hosted.browser.current_url).to_equal(committed_url)
expect(hosted.browser.current_body_html).to_equal(
    "<p>committed</p>"
)
expect(hosted.browser.history.len()).to_equal(hosted_history)

step("Send only the resolved absolute URL across the worker wire")
var registry = HostedBrowserRendererRegistry.create(
    "/bin/false", "https://home.test/"
)
val _ = registry.ensure(
    72, committed_html, 32, 16, 0, 100000
)
var entry = registry.entries[0]
entry.renderer = HostedBrowserRendererProcess.create(7, 32, 16)
entry.renderer.state = "active"
entry.renderer.document_url = committed_url
entry.renderer.document_origin = "https://example.test"
entry.renderer.history_urls = [committed_url]
entry.renderer.history_index = 0
entry.renderer_closed = false
entry.ready = true
entry.failure_reason = ""
entry.address_draft = "/next?x=1#ok"
entry.address_editing = true
entry.address_replace_on_text = false
registry.entries[0] = entry
val registry_submit = registry.dispatch_key_with_shift(
    5, 72, 13, true, false
)
expect(registry_submit.callback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
val registry_envelope = browser_renderer_capability_decoder_feed(
    browser_renderer_capability_decoder_new(7),
    registry.entries[0].renderer.pending_wire
)
val registry_command = browser_renderer_navigation_decode(
    browser_renderer_capability_payload_message(
        registry_envelope.message
    )
)
expect(registry_command.ok).to_be(true)
expect(registry_command.url).to_equal(target_url)
expect(
    registry.entries[0].renderer.history_urls
).to_equal([committed_url])
expect(registry.entries[0].renderer.history_index).to_equal(0)  # oracle: pinned constant asserted by this scenario

var worker = HostedBrowserRendererWorkerSession.create(32, 16)
val worker_capability = "11111111111111111111111111111111"
val worker_init = browser_renderer_capability_bind_encoded(
    browser_renderer_message_encode(
        "init", 7, 1, committed_html
    ),
    7, 1, 1, worker_capability
)
expect(worker.handle(
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(7),
        worker_init.wire
    ).message
).ok).to_be(true)
expect(worker.browser.open_html(
    committed_url, committed_html
).is_ok()).to_be(true)
val worker_committed_history = worker.browser.history.len()
val worker_navigation = browser_renderer_capability_bind_encoded(
    browser_renderer_navigation_encode(
        7, 2, "open", registry_command.url,
        "GET", "", "", ""
    ),
    7, 2, 2, worker_capability
)
val worker_requested = worker.handle(
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(7),
        worker_navigation.wire
    ).message
)
expect(worker_requested.ok).to_be(true)
val worker_fetch_envelope = (
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(7),
        worker_requested.wire
    )
)
val worker_fetch = browser_renderer_fetch_request_decode(
    browser_renderer_capability_payload_message(
        worker_fetch_envelope.message
    )
)
expect(worker_fetch.ok).to_be(true)
expect(worker_fetch.url).to_equal(
    "https://example.test/next?x=1"
)
expect(worker.browser.pending_url).to_equal(target_url)
expect(worker.browser.current_url).to_equal(committed_url)
expect(worker.browser.current_body_html).to_equal(
    "<p>committed</p>"
)
expect(worker.browser.history.len()).to_equal(
    worker_committed_history
)

step("Reject an invalid absolute host without losing editable or committed state")
val invalid = "https://bad_host/"
var rejected_hosted = HostedWebContentSession.create(
    73, committed_html, 32, 16
)
expect(rejected_hosted.browser.open_html(
    committed_url, committed_html
).is_ok()).to_be(true)
val rejected_history = rejected_hosted.browser.history.len()
val _ = rejected_hosted.dispatch_chrome_pointer(
    6, "address", true
)
val _ = rejected_hosted.dispatch_chrome_pointer(
    7, "address", false
)
val _ = rejected_hosted.dispatch_text(8, invalid)
val hosted_rejected = rejected_hosted.dispatch_key(9, 13, true)
expect(hosted_rejected.reason).to_equal(
    "invalid navigation authority"
)
expect(rejected_hosted.chrome_focus).to_equal("address")
expect(rejected_hosted.browser.address_draft).to_equal(invalid)
expect(rejected_hosted.browser.current_url).to_equal(committed_url)
expect(rejected_hosted.browser.current_body_html).to_equal(
    "<p>committed</p>"
)
expect(rejected_hosted.browser.history.len()).to_equal(
    rejected_history
)

var invalid_registry = HostedBrowserRendererRegistry.create(
    "/bin/false", "https://home.test/"
)
val _ = invalid_registry.ensure(
    74, committed_html, 32, 16, 0, 100000
)
var invalid_entry = invalid_registry.entries[0]
invalid_entry.renderer = HostedBrowserRendererProcess.create(
    8, 32, 16
)
invalid_entry.renderer.state = "active"
invalid_entry.renderer.document_url = committed_url
invalid_entry.renderer.document_origin = "https://example.test"
invalid_entry.renderer.history_urls = [committed_url]
invalid_entry.renderer.history_index = 0
invalid_entry.renderer_closed = false
invalid_entry.ready = true
invalid_entry.failure_reason = ""
invalid_entry.address_draft = invalid
invalid_entry.address_editing = true
invalid_entry.address_replace_on_text = false
invalid_registry.entries[0] = invalid_entry
val registry_rejected = invalid_registry.dispatch_key_with_shift(
    10, 74, 13, true, false
)
expect(registry_rejected.reason).to_equal(
    "invalid navigation authority"
)
expect(invalid_registry.address_text(74)).to_equal(invalid)
expect(invalid_registry.entries[0].address_editing).to_be(true)
expect(invalid_registry.document_url(74)).to_equal(committed_url)
expect(
    invalid_registry.entries[0].renderer.history_urls
).to_equal([committed_url])
expect(
    invalid_registry.entries[0].renderer.history_index
).to_equal(0)  # oracle: pinned constant asserted by this scenario

var stale = BrowserSession.new()
expect(stale.begin_network_navigation(
    target_url, "GET", "", "", ""
).is_ok()).to_be(true)
val stale_request = stale.take_pending_request().unwrap()
stale.pending_url = "https://example.test/genuinely-different#new"
match stale.commit_network_response(BrowserResponse.create(
    request_id: stale_request.id,
    kind: "document",
    url: stale_request.url,
    status: 200,
    headers: "Content-Type: text/html",
    body: "<html><body>must not commit</body></html>",
    error: ""
)):
    Err(reason):
        expect(reason).to_equal("stale document response")
    Ok(_):
        fail("genuinely different pending URL must stay stale")

worker.chrome_focus = "address"
worker.address_replace_on_text = false
worker.browser.address_draft = invalid
worker.pressed_target_id = "committed-target"
worker.input_view_target_key = "committed-input"
val worker_dom = worker.browser.current_dom
val worker_source = worker.browser.source_html
val worker_history = worker.browser.history
val worker_index = worker.browser.current_index
val worker_document_url = worker.browser.document_url
val worker_pending_url = worker.browser.pending_url
val snapshot = browser_renderer_history_proposal_encode(
    "N", "O", "", "https://snapshot.test/current",
    worker_capability, 0, ["https://snapshot.test/current"]
)
expect(snapshot.is_ok()).to_be(true)
val invalid_wire = browser_renderer_capability_bind_encoded(
    browser_renderer_navigation_encode_with_history(
        7, 3, "open", invalid, "GET", "", "", "",
        snapshot.unwrap()
    ),
    7, 3, 3, worker_capability
)
val worker_rejected = worker.handle(
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(7),
        invalid_wire.wire
    ).message
)
expect(worker_rejected.reason).to_equal(
    "invalid navigation authority"
)
expect(worker.chrome_focus).to_equal("address")
expect(worker.browser.address_draft).to_equal(invalid)
expect(worker.browser.current_url).to_equal(committed_url)
expect(worker.browser.current_body_html).to_equal(
    "<p>committed</p>"
)
expect(worker.browser.current_dom).to_be(worker_dom)
expect(worker.browser.source_html).to_equal(worker_source)
expect(worker.browser.history).to_equal(worker_history)
expect(worker.browser.current_index).to_equal(worker_index)
expect(worker.browser.document_url).to_equal(worker_document_url)
expect(worker.browser.pending_url).to_equal(worker_pending_url)
expect(worker.pressed_target_id).to_equal("committed-target")
expect(worker.input_view_target_key).to_equal("committed-input")
expect(registry.close()).to_be(true)
expect(invalid_registry.close()).to_be(true)
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


## Related Documentation

- **Requirements:** `REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-008, REQ-WEB-BROWSER-009`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1195b1ef4fbacbb1ff5a5e93071ce2f03a2d45d2057715ba4eb241c5a2675402`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1195b1ef4fbacbb1ff5a5e93071ce2f03a2d45d2057715ba4eb241c5a2675402`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1195b1ef4fbacbb1ff5a5e93071ce2f03a2d45d2057715ba4eb241c5a2675402`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_address_url_reference_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_address_url_reference_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_address_url_reference_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_address_url_reference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_address_url_reference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_address_url_reference_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve URL references before the worker boundary and reject invalid hosts atomically' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
