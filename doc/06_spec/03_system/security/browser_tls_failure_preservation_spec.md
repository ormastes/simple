# Browser TLS failure classification and preservation

> The runtime and hosted broker expose only stable TLS/network failure codes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser TLS failure classification and preservation

The runtime and hosted broker expose only stable TLS/network failure codes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_tls_failure_preservation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The runtime and hosted broker expose only stable TLS/network failure codes.
Certificate failures never commit a response, retry, redirect, learn HSTS, or
replace the previously committed document, CSP, title, or history.

## Scenarios

### browser TLS failure boundary

#### should expose stable failures while preserving committed browser state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose stable failures while preserving committed browser state
- Commit one HTTPS page and capture its security state
- Reject a fetch with the broker-owned stable failure
   - Expected: value equals `stable_error`
- Fail a replacement HTTPS navigation without retrying
   - Expected: session.inflight_requests.len() equals `0`
- Keep DOM CSP history and HSTS at the prior commit
   - Expected: session.current_title equals `Stable`
   - Expected: session.render_html_document() equals `committed_html`
   - Expected: session.content_security_policy equals `committed_csp`
   - Expected: session.history.len() equals `1`
   - Expected: session.current_index equals `0`
   - Expected: session.history[0].url equals `committed_history_url`
- Sanitize an unclassified platform failure at the broker
- Retire broker navigation state without erasing committed title
   - Expected: broker.document_title equals `Stable`
   - Expected: broker.pending_history_action equals ``
   - Expected: broker.pending_document_commit_url equals ``
   - Expected: broker.provisional_document_origin equals ``
   - Expected: broker.document_url equals `https://stable.test/page`
   - Expected: broker.document_title equals `Stable`
   - Expected: broker.document_csp_policy equals `default-src 'self'`
   - Expected: broker.history_urls equals `[`
   - Expected: broker.history_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 152 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose stable failures while preserving committed browser state")
for stable_error in TLS_FAILURES:
    step("Commit one HTTPS page and capture its security state")
    var session = BrowserSession.new()
    expect(session.load_hsts_snapshot(
        BrowserHstsSnapshot.create([
            BrowserHstsSnapshotEntry(
                host: "stable.test",
                received_at_unix_ms: 1000,
                expires_at_unix_ms: 100000,
                include_subdomains: false
            )
        ]),
        2000
    )).to_equal(1)
    expect(session.open_html(
        "https://stable.test/page",
        "<html><head><title>Stable</title>" +
        "<meta http-equiv='content-security-policy' " +
        "content=\"default-src 'self'\">" +
        "</head><body><p id='kept'>kept</p>" +
        "<script>var tlsError = 'start'; " +
        "window.fetch('/probe').catch(function(err) " +
        "{ tlsError = err; });</script></body></html>"
    ).is_ok()).to_be(true)

    step("Reject a fetch with the broker-owned stable failure")
    match session.take_pending_request():
        nil:
            fail("Expected the TLS fetch probe")
        Some(fetch):
            expect(session.commit_network_response(
                BrowserResponse.create(
                    fetch.id, "fetch", fetch.url, 0,
                    "", "", hosted_browser_network_error(
                        "https", stable_error
                    )
                )
            ).is_err()).to_be(true)
    match session.eval_script("tlsError"):
        Ok(JsValue.String(value)):
            expect(value).to_equal(stable_error)
        Ok(_):
            fail("Expected a stable string failure in script")
        Err(reason):
            fail("Expected the script failure value: {reason}")
    val committed_html = session.render_html_document()
    val committed_csp = session.content_security_policy
    val committed_history_url = session.history[0].url
    val committed_hsts = session.hsts_snapshot(2000)

    step("Fail a replacement HTTPS navigation without retrying")
    expect(session.begin_network_navigation(
        "https://invalid.test/page", "GET", "", "", ""
    ).is_ok()).to_be(true)
    match session.take_pending_request():
        nil:
            fail("Expected the replacement document request")
        Some(document):
            val failed = hosted_browser_network_error(
                "https", stable_error
            )
            expect(session.commit_network_response(
                BrowserResponse.create(
                    document.id, "document", document.url, 0,
                    "", "", failed
                )
            ).unwrap_err()).to_equal(stable_error)
    expect(session.has_pending_requests()).to_be(false)
    expect(session.inflight_requests.len()).to_equal(0)

    step("Keep DOM CSP history and HSTS at the prior commit")
    expect(session.current_url).to_equal(
        "https://stable.test/page"
    )
    expect(session.current_title).to_equal("Stable")
    expect(session.render_html_document()).to_equal(committed_html)
    expect(session.content_security_policy).to_equal(committed_csp)
    expect(session.history.len()).to_equal(1)
    expect(session.current_index).to_equal(0)
    expect(session.history[0].url).to_equal(committed_history_url)
    expect(session.hsts_snapshot(2000).entries.len()).to_equal(
        committed_hsts.entries.len()
    )
    expect(session.is_loading).to_be(false)

step("Sanitize an unclassified platform failure at the broker")
expect(hosted_browser_network_error(
    "https",
    "certificate for invalid.test disclosed platform path /secret"
)).to_equal("network: Network request failed")
expect(hosted_browser_network_error(
    "http",
    "tls-hostname: TLS certificate identity validation failed"
)).to_equal("network: Network request failed")

step("Retire broker navigation state without erasing committed title")
var broker = HostedBrowserRendererProcess.create(81, 64, 48)
broker.document_url = "https://stable.test/page"
broker.document_origin = "https://stable.test"
broker.document_csp_policy = "default-src 'self'"
broker.document_csp_ready = true
broker.document_title = "Stable"
broker.document_title_url = broker.document_url
broker.history_urls = [broker.document_url]
broker.history_csp_policies = [broker.document_csp_policy]
broker.history_csp_ready = [true]
broker.history_index = 0
expect(broker._commit_validated_https_hsts(
    "https://stable.test/page",
    "Strict-Transport-Security: max-age=60"
)).to_be(true)
expect(broker.authorize_navigation(
    "https://invalid.test/page", "GET", "", "", ""
)).to_be(true)
expect(broker.document_title).to_equal("Stable")
var failed_response = broker._finalize_network(
    "document",
    FetchRequest(
        url: Url.parse_or_opaque("https://invalid.test/page"),
        method: "GET", headers: "", body: [],
        mode: RequestMode.Navigate, credentials: "include"
    ),
    FetchResponse(status: 200, headers: "", body: [])
)
failed_response.status = 0
failed_response.error = TLS_FAILURES[0]
expect(broker._record_document_response(
    _renderer_document_request("https://invalid.test/page"),
    HostedBrowserRequestPolicy(
        ok: true, reason: "ok", mode: RequestMode.Navigate,
        credentials: "include",
        canonical_url: "https://invalid.test/page",
        sanitized_headers: "", consumes_navigation: true
    ),
    failed_response, 0
).is_ok()).to_be(true)
expect(broker.navigation_permit.active).to_be(false)
expect(broker.pending_history_action).to_equal("")
expect(broker.pending_document_commit_url).to_equal("")
expect(broker.provisional_document_origin).to_equal("")
expect(broker.document_url).to_equal("https://stable.test/page")
expect(broker.document_title).to_equal("Stable")
expect(broker.document_csp_policy).to_equal("default-src 'self'")
expect(broker.history_urls).to_equal([
    "https://stable.test/page"
])
expect(broker.history_index).to_equal(0)
expect(broker._hsts_upgrade_url(
    "http://stable.test/next"
)).to_equal("https://stable.test/next")
```

</details>

#### should recover through the bound broker worker protocol

- should recover through the bound broker worker protocol
- Render and retain the committed worker frame
   - Expected: stable_bound_frame.status equals `message`
- Bind the admitted navigation from worker to broker
   - Expected: bound_fetch.status equals `message`
   - Expected: fetch.kind equals `document`
   - Expected: fetch.url equals `failed_url`
- Dispatch one sanitized TLS failure through SBR2
   - Expected: bound_failure.status equals `message`
   - Expected: decoded_failure.error equals `TLS_FAILURES[0]`
- Return a recoverable retained frame and keep both sides alive
   - Expected: worker.browser.current_url equals `stable_url`
   - Expected: bound_recovered_frame.status equals `message`
   - Expected: broker.state equals `active`
   - Expected: broker.document_url equals `stable_url`
   - Expected: broker.document_title equals `Stable`
   - Expected: broker.history_urls equals `[stable_url]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 189 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should recover through the bound broker worker protocol")
val generation: i64 = 7
val stable_url = "https://stable.test/page"
val failed_url = "https://invalid.test/page"
val stable_html = (
    "<html><head><title>Stable</title></head>" +
    "<body><p id='kept'>kept</p></body></html>"
)
val stable_capability = "11111111111111111111111111111111"
val navigation_capability = "22222222222222222222222222222222"
val followup_capability = "33333333333333333333333333333333"

step("Render and retain the committed worker frame")
var worker = HostedBrowserRendererWorkerSession.create(64, 48)
val initialized = worker.handle(
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(generation),
        browser_renderer_capability_bind_encoded(
            browser_renderer_message_encode(
                "init", generation, 2, stable_html
            ),
            generation, 2, 2, stable_capability
        ).wire
    ).message
)
expect(initialized.ok).to_be(true)
var committed_session = BrowserSession.new()
committed_session.broker_network_policy = true
expect(committed_session.open_html(
    stable_url, stable_html
).is_ok()).to_be(true)
worker.browser = committed_session
val stable_result = worker.handle(
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(generation),
        browser_renderer_capability_bind_encoded(
            browser_renderer_message_encode(
                "advance", generation, 3, "16"
            ),
            generation, 3, 3, stable_capability
        ).wire
    ).message
)
expect(stable_result.ok).to_be(true)
val stable_bound_frame = browser_renderer_capability_decoder_feed(
    browser_renderer_capability_decoder_new(generation),
    stable_result.wire
)
expect(stable_bound_frame.status).to_equal("message")
val stable_frame = browser_renderer_frame_decode(
    browser_renderer_capability_payload_message(
        stable_bound_frame.message
    ),
    64, 48
)
expect(stable_frame.ok).to_be(true)

step("Bind the admitted navigation from worker to broker")
val navigation = browser_renderer_capability_bind_encoded(
    browser_renderer_navigation_encode(
        generation, 4, "open", failed_url,
        "GET", "", "", ""
    ),
    generation, 4, 4, navigation_capability
)
val requested = worker.handle(
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(generation),
        navigation.wire
    ).message
)
expect(requested.ok).to_be(true)
val bound_fetch = browser_renderer_capability_decoder_feed(
    browser_renderer_capability_decoder_new(generation),
    requested.wire
)
expect(bound_fetch.status).to_equal("message")
val fetch = browser_renderer_fetch_request_decode(
    browser_renderer_capability_payload_message(
        bound_fetch.message
    )
)
expect(fetch.ok).to_be(true)
expect(fetch.kind).to_equal("document")
expect(fetch.url).to_equal(failed_url)

step("Dispatch one sanitized TLS failure through SBR2")
var broker = HostedBrowserRendererProcess.create(
    generation, 64, 48
)
broker.state = "active"
broker.document_url = stable_url
broker.document_origin = "https://stable.test"
broker.document_csp_policy = ""
broker.document_csp_ready = true
broker.document_title = "Stable"
broker.document_title_url = stable_url
broker.history_urls = [stable_url]
broker.history_csp_policies = [""]
broker.history_csp_ready = [true]
broker.history_index = 0
broker.active_command_capability = navigation_capability
broker.active_root_command_request_id = 4
broker.next_request_id = 5
broker.pending_operation = "navigation"
var failed_response = broker._finalize_network(
    "document",
    FetchRequest(
        url: Url.parse_or_opaque(failed_url),
        method: "GET", headers: "", body: [],
        mode: RequestMode.Navigate, credentials: "include"
    ),
    FetchResponse(status: 200, headers: "", body: [])
)
failed_response.status = 0
failed_response.headers = ""
failed_response.body = ""
failed_response.error = hosted_browser_network_error(
    "https", TLS_FAILURES[0]
)
expect(broker._write_network_response(
    fetch,
    HostedBrowserRequestPolicy(
        ok: true, reason: "ok", mode: RequestMode.Navigate,
        credentials: "include", canonical_url: failed_url,
        sanitized_headers: "", consumes_navigation: true
    ),
    failed_response, 0
)).to_equal("")
val bound_failure = browser_renderer_capability_decoder_feed(
    browser_renderer_capability_decoder_new(generation),
    broker.pending_wire
)
expect(bound_failure.status).to_equal("message")
val decoded_failure = browser_renderer_network_response_decode(
    browser_renderer_capability_payload_message(
        bound_failure.message
    )
)
expect(decoded_failure.error).to_equal(TLS_FAILURES[0])
expect(decoded_failure.error.contains("private")).to_be(false)

step("Return a recoverable retained frame and keep both sides alive")
val recovered = worker.handle(bound_failure.message)
expect(recovered.ok).to_be(true)
expect(worker.initialized).to_be(true)
expect(worker.browser.current_url).to_equal(stable_url)
val bound_recovered_frame = (
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(generation),
        recovered.wire
    )
)
expect(bound_recovered_frame.status).to_equal("message")
val recovered_frame = browser_renderer_frame_decode(
    browser_renderer_capability_payload_message(
        bound_recovered_frame.message
    ),
    64, 48
)
expect(recovered_frame.ok).to_be(true)
expect(recovered_frame.composition_revision).to_equal(
    stable_frame.composition_revision
)
expect(recovered_frame.composition.batches).to_equal(
    stable_frame.composition.batches
)
expect(recovered_frame.diagnostics).to_contain(TLS_FAILURES[0])
val accepted = broker._accept_decoded_frame(
    recovered_frame, generation
)
expect(accepted.ok).to_be(true)
expect(broker.state).to_equal("active")
expect(broker.document_url).to_equal(stable_url)
expect(broker.document_title).to_equal("Stable")
expect(broker.history_urls).to_equal([stable_url])
val followup = worker.handle(
    browser_renderer_capability_decoder_feed(
        browser_renderer_capability_decoder_new(generation),
        browser_renderer_capability_bind_encoded(
            browser_renderer_message_encode(
                "advance", generation, 6, "32"
            ),
            generation, 6, 6, followup_capability
        ).wire
    ).message
)
expect(followup.ok).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-009`
- `REQ-WEB-BROWSER-011`
- `REQ-WEB-BROWSER-014`
- `REQ-WEB-BROWSER-020`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78e3cd3f74be92156b3e523879810475405a845aa65e538e2679af7dd15395ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78e3cd3f74be92156b3e523879810475405a845aa65e538e2679af7dd15395ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78e3cd3f74be92156b3e523879810475405a845aa65e538e2679af7dd15395ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/browser_tls_failure_preservation_spec.spl
mirror: doc/06_spec/03_system/security/browser_tls_failure_preservation_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=90 oracle=70
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/security/browser_tls_failure_preservation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_tls_failure_preservation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_tls_failure_preservation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/security/browser_tls_failure_preservation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/security/browser_tls_failure_preservation_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose stable failures while preserving committed browser state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_tls_failure_preservation_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose stable failures while preserving committed browser state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/browser_tls_failure_preservation_spec.spl:233:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recover through the bound broker worker protocol' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_tls_failure_preservation_spec.spl:233:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should recover through the bound broker worker protocol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
