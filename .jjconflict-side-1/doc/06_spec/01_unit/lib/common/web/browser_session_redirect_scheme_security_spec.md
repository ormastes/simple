# browser_session_redirect_scheme_security_spec

> BrowserSession redirect security.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_session_redirect_scheme_security_spec

BrowserSession redirect security.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

BrowserSession redirect security.

Only top-level document downgrade policy uses the canonical scheme of the
matched inflight request. Active-subresource and fetch redirects use the secure
client context plus target trustworthiness. Fetch scenarios enable
broker_network_policy to model the trusted transport boundary.

## Scenarios

### BrowserSession redirect source-scheme security

<details>
<summary>Advanced: should reject a loopback stylesheet redirect to ordinary HTTP without replacing committed state</summary>

#### should reject a loopback stylesheet redirect to ordinary HTTP without replacing committed state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject a loopback stylesheet redirect to ordinary HTTP without replacing committed state
- Commit stable HTTPS page and history state
- Take the allowed loopback stylesheet request
   - Expected: request.kind equals `style`
   - Expected: request.url equals `http://127.0.0.1/theme.css`
- Redirect the loopback stylesheet to ordinary HTTP
- Reject the mixed-content redirect and preserve page history
   - Expected: session.current_url equals `https://stable.test/two`
   - Expected: session.current_title equals `Stable`
   - Expected: session.history_back_url() equals `https://stable.test/one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a loopback stylesheet redirect to ordinary HTTP without replacing committed state")
step("Commit stable HTTPS page and history state")
var session = BrowserSession.new()
expect(session.open_html(
    "https://stable.test/one",
    "<html><head><title>One</title></head><body>one</body></html>"
).is_ok()).to_be(true)
expect(session.open_html(
    "https://stable.test/two",
    "<html><head><title>Stable</title>" +
    "<link rel='stylesheet' href='http://127.0.0.1/theme.css'>" +
    "</head><body>stable</body></html>"
).is_ok()).to_be(true)

step("Take the allowed loopback stylesheet request")
val request = session.take_pending_request().unwrap()
expect(request.kind).to_equal("style")
expect(request.url).to_equal("http://127.0.0.1/theme.css")

step("Redirect the loopback stylesheet to ordinary HTTP")
expect(session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: request.url,
    status: 302,
    headers: "Location: http://cdn.test/theme.css\n",
    body: "",
    error: ""
)).is_ok()).to_be(true)

step("Reject the mixed-content redirect and preserve page history")
expect(session.has_pending_requests()).to_be(false)
expect(session.warnings.join("|")).to_contain(
    "stylesheet load error: redirect blocked HTTPS downgrade"
)
expect(session.current_url).to_equal("https://stable.test/two")
expect(session.current_title).to_equal("Stable")
expect(session.current_body_html).to_contain("stable")
expect(session.can_go_back()).to_be(true)
expect(session.history_back_url()).to_equal("https://stable.test/one")
expect(session.can_go_forward()).to_be(false)
```

</details>


</details>

<details>
<summary>Advanced: should reject a loopback fetch redirect to ordinary HTTP without replacing committed state</summary>

#### should reject a loopback fetch redirect to ordinary HTTP without replacing committed state

- should reject a loopback fetch redirect to ordinary HTTP without replacing committed state
- Commit HTTPS page and history state with a loopback fetch
- Take the allowed loopback fetch request
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `http://127.0.0.1/start`
- Redirect the loopback fetch to ordinary HTTP
- Reject the mixed-content redirect and preserve page history
   - Expected: session.current_url equals `https://stable.test/two`
   - Expected: session.current_title equals `Stable`
   - Expected: session.history_back_url() equals `https://stable.test/one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a loopback fetch redirect to ordinary HTTP without replacing committed state")
step("Commit HTTPS page and history state with a loopback fetch")
var session = BrowserSession.new()
session.broker_network_policy = true
expect(session.open_html(
    "https://stable.test/one",
    "<html><head><title>One</title></head><body>one</body></html>"
).is_ok()).to_be(true)
expect(session.open_html(
    "https://stable.test/two",
    "<html><head><title>Stable</title></head><body>stable" +
    "<script>var outcome = 'pending';" +
    "fetch('http://127.0.0.1/start').catch(function(e) {" +
    " outcome = e; });</script></body></html>"
).is_ok()).to_be(true)

step("Take the allowed loopback fetch request")
val request = session.take_pending_request().unwrap()
expect(request.kind).to_equal("fetch")
expect(request.url).to_equal("http://127.0.0.1/start")

step("Redirect the loopback fetch to ordinary HTTP")
expect(session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: request.url,
    status: 302,
    headers: "Location: http://cdn.test/data\n",
    body: "",
    error: ""
)).is_ok()).to_be(true)

step("Reject the mixed-content redirect and preserve page history")
expect(session.has_pending_requests()).to_be(false)
match session.eval_script("outcome"):
    Ok(JsValue.String(message)):
        expect(message).to_contain(
            "redirect-blocked:https-downgrade"
        )
    _:
        fail("Expected the loopback fetch redirect to reject with text")
expect(session.current_url).to_equal("https://stable.test/two")
expect(session.current_title).to_equal("Stable")
expect(session.current_body_html).to_contain("stable")
expect(session.can_go_back()).to_be(true)
expect(session.history_back_url()).to_equal("https://stable.test/one")
expect(session.can_go_forward()).to_be(false)
```

</details>


</details>

<details>
<summary>Advanced: should continue following a brokered loopback fetch redirect to loopback</summary>

#### should continue following a brokered loopback fetch redirect to loopback

- should continue following a brokered loopback fetch redirect to loopback
- Open a secure page that starts a brokered loopback fetch
- Take the allowed loopback fetch request
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `http://127.0.0.1/start`
- Redirect the fetch to another loopback URL
- Follow the trustworthy loopback target
   - Expected: redirected.kind equals `fetch`
   - Expected: redirected.url equals `http://localhost/final`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should continue following a brokered loopback fetch redirect to loopback")
step("Open a secure page that starts a brokered loopback fetch")
var session = BrowserSession.new()
session.broker_network_policy = true
expect(session.open_html(
    "https://safe.test/app",
    "<html><body><script>" +
    "fetch('http://127.0.0.1/start');" +
    "</script></body></html>"
).is_ok()).to_be(true)

step("Take the allowed loopback fetch request")
val request = session.take_pending_request().unwrap()
expect(request.kind).to_equal("fetch")
expect(request.url).to_equal("http://127.0.0.1/start")

step("Redirect the fetch to another loopback URL")
expect(session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: request.url,
    status: 302,
    headers: "Location: http://localhost/final\n",
    body: "",
    error: ""
)).is_ok()).to_be(true)

step("Follow the trustworthy loopback target")
val redirected = session.take_pending_request().unwrap()
expect(redirected.kind).to_equal("fetch")
expect(redirected.url).to_equal("http://localhost/final")
```

</details>


</details>

<details>
<summary>Advanced: should continue following a loopback stylesheet redirect to loopback</summary>

#### should continue following a loopback stylesheet redirect to loopback

- should continue following a loopback stylesheet redirect to loopback
- Open a secure page that loads a loopback stylesheet
- Take the allowed loopback stylesheet request
   - Expected: request.kind equals `style`
- Redirect the stylesheet to another loopback URL
- Follow the trustworthy loopback target
   - Expected: redirected.kind equals `style`
   - Expected: redirected.url equals `http://localhost/final.css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should continue following a loopback stylesheet redirect to loopback")
step("Open a secure page that loads a loopback stylesheet")
var session = BrowserSession.new()
expect(session.open_html(
    "https://safe.test/app",
    "<html><head><link rel='stylesheet' " +
    "href='http://127.0.0.1/start.css'></head><body>safe</body></html>"
).is_ok()).to_be(true)

step("Take the allowed loopback stylesheet request")
val request = session.take_pending_request().unwrap()
expect(request.kind).to_equal("style")

step("Redirect the stylesheet to another loopback URL")
expect(session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: request.url,
    status: 302,
    headers: "Location: http://localhost/final.css\n",
    body: "",
    error: ""
)).is_ok()).to_be(true)

step("Follow the trustworthy loopback target")
val redirected = session.take_pending_request().unwrap()
expect(redirected.kind).to_equal("style")
expect(redirected.url).to_equal("http://localhost/final.css")
```

</details>


</details>

<details>
<summary>Advanced: should continue following a loopback stylesheet redirect to HTTPS</summary>

#### should continue following a loopback stylesheet redirect to HTTPS

- should continue following a loopback stylesheet redirect to HTTPS
- Open a secure page that loads a loopback stylesheet
- Take the allowed loopback stylesheet request
   - Expected: request.kind equals `style`
- Redirect the stylesheet to HTTPS
- Follow the secure target
   - Expected: redirected.kind equals `style`
   - Expected: redirected.url equals `https://cdn.test/final.css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should continue following a loopback stylesheet redirect to HTTPS")
step("Open a secure page that loads a loopback stylesheet")
var session = BrowserSession.new()
expect(session.open_html(
    "https://safe.test/app",
    "<html><head><link rel='stylesheet' " +
    "href='http://127.0.0.1/start.css'></head><body>safe</body></html>"
).is_ok()).to_be(true)

step("Take the allowed loopback stylesheet request")
val request = session.take_pending_request().unwrap()
expect(request.kind).to_equal("style")

step("Redirect the stylesheet to HTTPS")
expect(session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: request.url,
    status: 302,
    headers: "Location: https://cdn.test/final.css\n",
    body: "",
    error: ""
)).is_ok()).to_be(true)

step("Follow the secure target")
val redirected = session.take_pending_request().unwrap()
expect(redirected.kind).to_equal("style")
expect(redirected.url).to_equal("https://cdn.test/final.css")
```

</details>


</details>

#### should reject a case-variant document downgrade without replacing committed state

- should reject a case-variant document downgrade without replacing committed state
- Commit stable page and history state
- Start a secure document navigation
- Return a case-variant secure response that redirects to HTTP
- Keep the committed page and history after rejecting the downgrade
   - Expected: session.current_url equals `https://stable.test/two`
   - Expected: session.current_title equals `Stable`
   - Expected: session.history_back_url() equals `https://stable.test/one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a case-variant document downgrade without replacing committed state")
step("Commit stable page and history state")
var session = BrowserSession.new()
expect(session.open_html(
    "https://stable.test/one",
    "<html><head><title>One</title></head><body>one</body></html>"
).is_ok()).to_be(true)
expect(session.open_html(
    "https://stable.test/two",
    "<html><head><title>Stable</title></head><body>stable</body></html>"
).is_ok()).to_be(true)

step("Start a secure document navigation")
expect(session.begin_network_navigation(
    "https://secure.test/start", "GET", "", "", ""
).is_ok()).to_be(true)
val request = session.take_pending_request().unwrap()

step("Return a case-variant secure response that redirects to HTTP")
val blocked = session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: "HTTPS://secure.test/start",
    status: 302,
    headers: "Location: http://secure.test/plain\n",
    body: "",
    error: ""
))

step("Keep the committed page and history after rejecting the downgrade")
match blocked:
    Err(message): expect(message).to_contain("HTTPS downgrade")
    Ok(_): fail("Expected the case-variant document downgrade to fail")
expect(session.can_stop_loading()).to_be(false)
expect(session.has_pending_requests()).to_be(false)
expect(session.current_url).to_equal("https://stable.test/two")
expect(session.current_title).to_equal("Stable")
expect(session.current_body_html).to_contain("stable")
expect(session.can_go_back()).to_be(true)
expect(session.history_back_url()).to_equal("https://stable.test/one")
expect(session.can_go_forward()).to_be(false)
```

</details>

#### should reject a case-variant fetch downgrade

- should reject a case-variant fetch downgrade
- Open a secure page that starts a same-origin fetch
- Take the secure fetch request
   - Expected: request.kind equals `fetch`
- Return a case-variant secure response that redirects to HTTP
- Reject the fetch without scheduling the HTTP request


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a case-variant fetch downgrade")
step("Open a secure page that starts a same-origin fetch")
var session = BrowserSession.new()
expect(session.open_html(
    "https://safe.test/app",
    "<html><body><script>var outcome = 'pending'; fetch('/start').catch(function(e) { outcome = e; })</script></body></html>"
).is_ok()).to_be(true)

step("Take the secure fetch request")
val request = session.take_pending_request().unwrap()
expect(request.kind).to_equal("fetch")

step("Return a case-variant secure response that redirects to HTTP")
expect(session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: "HTTPS://safe.test/start",
    status: 302,
    headers: "Location: http://safe.test/plain\n",
    body: "",
    error: ""
)).is_ok()).to_be(true)

step("Reject the fetch without scheduling the HTTP request")
expect(session.has_pending_requests()).to_be(false)
match session.eval_script("outcome"):
    Ok(JsValue.String(message)):
        expect(message).to_contain("redirect-blocked:https-downgrade")
    _:
        fail("Expected the downgraded fetch to reject with text")
```

</details>

#### should reject a case-variant stylesheet downgrade

- should reject a case-variant stylesheet downgrade
- Open a secure page that loads a stylesheet
- Take the secure stylesheet request
   - Expected: request.kind equals `style`
- Return a case-variant secure response that redirects to HTTP
- Reject the stylesheet without scheduling the HTTP request


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a case-variant stylesheet downgrade")
step("Open a secure page that loads a stylesheet")
var session = BrowserSession.new()
expect(session.open_html(
    "https://safe.test/app",
    "<html><head><link rel='stylesheet' href='/theme.css'></head><body>safe</body></html>"
).is_ok()).to_be(true)

step("Take the secure stylesheet request")
val request = session.take_pending_request().unwrap()
expect(request.kind).to_equal("style")

step("Return a case-variant secure response that redirects to HTTP")
expect(session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: "HTTPS://safe.test/theme.css",
    status: 302,
    headers: "Location: http://safe.test/theme.css\n",
    body: "",
    error: ""
)).is_ok()).to_be(true)

step("Reject the stylesheet without scheduling the HTTP request")
expect(session.has_pending_requests()).to_be(false)
expect(session.warnings.join("|")).to_contain(
    "stylesheet load error: redirect blocked HTTPS downgrade"
)
```

</details>

#### should continue following an HTTPS redirect

- should continue following an HTTPS redirect
- Start an ordinary secure document navigation
- Take the secure document request
   - Expected: request.kind equals `document`
- Return a case-variant response with an HTTPS target
- Follow the secure target unchanged
   - Expected: redirected.url equals `https://secure.test/done`
   - Expected: redirected.kind equals `document`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should continue following an HTTPS redirect")
step("Start an ordinary secure document navigation")
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://secure.test/start", "GET", "", "", ""
).is_ok()).to_be(true)

step("Take the secure document request")
val request = session.take_pending_request().unwrap()
expect(request.kind).to_equal("document")

step("Return a case-variant response with an HTTPS target")
expect(session.commit_network_response(BrowserResponse.create(
    request_id: request.id,
    kind: request.kind,
    url: "HTTPS://secure.test/start",
    status: 302,
    headers: "Location: https://secure.test/done\n",
    body: "",
    error: ""
)).is_ok()).to_be(true)

step("Follow the secure target unchanged")
val redirected = session.take_pending_request().unwrap()
expect(redirected.url).to_equal("https://secure.test/done")
expect(redirected.kind).to_equal("document")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35e8b36e12e19c03ece6fdf4ca54f75c259a6c62ac0a33d3e79c0544c688e508`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35e8b36e12e19c03ece6fdf4ca54f75c259a6c62ac0a33d3e79c0544c688e508`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35e8b36e12e19c03ece6fdf4ca54f75c259a6c62ac0a33d3e79c0544c688e508`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a loopback stylesheet redirect to ordinary HTTP without replacing committed state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a loopback stylesheet redirect to ordinary HTTP without replacing committed state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a loopback fetch redirect to ordinary HTTP without replacing committed state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a loopback fetch redirect to ordinary HTTP without replacing committed state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:124:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should continue following a brokered loopback fetch redirect to loopback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should continue following a brokered loopback fetch redirect to loopback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:158:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should continue following a loopback stylesheet redirect to loopback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:189:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should continue following a loopback stylesheet redirect to HTTPS' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl:220:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a case-variant document downgrade without replacing committed state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
