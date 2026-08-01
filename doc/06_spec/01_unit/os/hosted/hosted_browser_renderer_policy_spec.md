# Hosted browser renderer policy

> Treats decoded renderer protocol messages as untrusted input at the hosted browser broker. The scenarios cover navigation permits, origin and CSP admission, cookie ownership, HSTS, redirects, resource limits, lifecycle, and site-swap state without granting the renderer direct network authority.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 57 | 57 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted browser renderer policy

Treats decoded renderer protocol messages as untrusted input at the hosted browser broker. The scenarios cover navigation permits, origin and CSP admission, cookie ownership, HSTS, redirects, resource limits, lifecycle, and site-swap state without granting the renderer direct network authority.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/01_unit/os/hosted/hosted_browser_renderer_policy_spec.spl` |
| Updated | 2026-07-30 |
| Generator | Manual mirror; admitted pure-Simple docgen pending |

## Overview

Treats decoded renderer protocol messages as untrusted input at the hosted
browser broker. The scenarios cover navigation permits, origin and CSP
admission, cookie ownership, HSTS, redirects, resource limits, lifecycle, and
site-swap state without granting the renderer direct network authority.

## Examples

The primary adversarial flow decodes SBRQ4 requests through the production
dispatcher and proves rejected cookie or navigation side effects occur before
trusted broker state changes. Explicit controls retain the parent-authorized
initial document load and route top-level HTTPS-to-HTTP navigation through the
navigation policy rather than subresource mixed-content policy.

## Scenarios

### hosted browser renderer transport host

#### unwraps only a canonical IPv6 address for socket and TLS

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hosted_browser_transport_host(
    "[2606:4700:4700::1111]"
)).to_equal("2606:4700:4700::1111")
expect(hosted_browser_transport_host(
    "example.com"
)).to_equal("example.com")
expect(hosted_browser_transport_host(
    "192.0.2.1"
)).to_equal("192.0.2.1")
expect(hosted_browser_transport_host(
    "[not:v6]"
)).to_equal("[not:v6]")
expect(hosted_browser_transport_host(
    "[[::1]]"
)).to_equal("[[::1]]")
expect(hosted_browser_transport_host("[::1")).to_equal("[::1")
```

</details>

#### normalizes every hosted browser transport boundary

- "hosted browser transport host
- "hosted browser transport host


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = rt_file_read_text(
    "src/os/hosted/hosted_browser_renderer_process.spl"
) ?? ""
val content = rt_file_read_text(
    "src/os/hosted/hosted_web_content_session.spl"
) ?? ""
expect(renderer).to_contain(
    "hosted_browser_transport_host(url.host)"
)
expect(content).to_contain(
    "hosted_browser_transport_host(url.host)"
)
```

</details>

### hosted browser renderer broker policy

#### keeps Favorite bound to the committed page during navigation

- Admit one deterministic secondary browser entry
- var profile = BrowserProfileStore memory
- Enter a new address through production registry routing
- Reject Favorite while the navigation command is pending
   - Expected: command_busy.callback_count equals `0`
   - Expected: command_busy.reason equals `renderer-busy`
   - Expected: profile.load_bookmarks()?.entries.len() equals `0`
- Reject Favorite while the navigation transport is pending
   - Expected: network_busy.callback_count equals `0`
   - Expected: network_busy.reason equals `renderer-busy`
   - Expected: profile.load_bookmarks()?.entries.len() equals `0`
- Commit the target page before admitting Favorite
   - Expected: admitted.reason equals `favorite-parent`
- Persist only the newly committed URL
   - Expected: saved.entries.len() equals `1`
   - Expected: saved.entries[0].first equals `https://new.test/`
- profile close
   - Expected: registry.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 91 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Admit one deterministic secondary browser entry")
var registry = HostedBrowserRendererRegistry.create(
    "/definitely/missing/simple-browser-renderer",
    "https://home.test/"
)
expect(registry.ensure(
    91, "", 320, 200, 1000, 1000
)).to_equal("failed")
var entry = registry.entries[0]
entry.ready = true
entry.failure_reason = ""
entry.renderer.state = "active"
entry.renderer.document_url = "https://old.test/"
entry.renderer.document_origin = "https://old.test"
registry.entries[0] = entry
var profile = BrowserProfileStore.memory()?

step("Enter a new address through production registry routing")
expect(registry.dispatch_chrome_pointer(
    1, 91, "address", true
).reason).to_equal("chrome-pressed")
expect(registry.dispatch_chrome_pointer(
    2, 91, "address", false
).reason).to_equal("address-focused")
expect(registry.dispatch_text(
    3, 91, "https://new.test/"
).callback_count).to_equal(1)
expect(registry.dispatch_key_with_shift(
    4, 91, 13, true, false
).callback_count).to_equal(1)
expect(registry.address_text(91)).to_equal(
    "https://new.test/"
)
expect(
    registry.entries[0].renderer.command_deadline_ms
).to_be_greater_than(0)

step("Reject Favorite while the navigation command is pending")
val _ = registry.dispatch_chrome_pointer(
    5, 91, "favorite", true
)
val command_busy = registry.dispatch_chrome_pointer(
    6, 91, "favorite", false
)
expect(command_busy.callback_count).to_equal(0)
expect(command_busy.reason).to_equal("renderer-busy")
if command_busy.reason == "favorite-parent":
    val url = registry.document_url(91)
    val _ = profile.toggle_bookmark(url, url)?
expect(profile.load_bookmarks()?.entries.len()).to_equal(0)

step("Reject Favorite while the navigation transport is pending")
entry = registry.entries[0]
entry.renderer.command_deadline_ms = 0
entry.renderer.pending_wire = ""
entry.renderer.network_job_handle = 77
registry.entries[0] = entry
val _ = registry.dispatch_chrome_pointer(
    7, 91, "favorite", true
)
val network_busy = registry.dispatch_chrome_pointer(
    8, 91, "favorite", false
)
expect(network_busy.callback_count).to_equal(0)
expect(network_busy.reason).to_equal("renderer-busy")
expect(profile.load_bookmarks()?.entries.len()).to_equal(0)

step("Commit the target page before admitting Favorite")
entry = registry.entries[0]
entry.renderer.network_job_handle = 0
entry.renderer.document_url = "https://new.test/"
entry.renderer.document_origin = "https://new.test"
registry.entries[0] = entry
val _ = registry.dispatch_chrome_pointer(
    9, 91, "favorite", true
)
val admitted = registry.dispatch_chrome_pointer(
    10, 91, "favorite", false
)
expect(admitted.reason).to_equal("favorite-parent")
val committed_url = registry.document_url(91)
val _ = profile.toggle_bookmark(
    committed_url, committed_url
)?

step("Persist only the newly committed URL")
val saved = profile.load_bookmarks()?
expect(saved.entries.len()).to_equal(1)
expect(saved.entries[0].first).to_equal("https://new.test/")
profile.close()?
expect(registry.close()).to_equal(true)
```

</details>

#### admits decoded renderer side effects only through trusted CSP state

- var mocks = MockResponseRegistry create
- mocks register
- mocks register
- set mock registry
- Reject an opaque sandbox document that forges a cookie write
- var opaque = HostedBrowserRendererProcess create
- fail
- Some
- Reject missing and invalid CSP before cookie mutation
- source origin, "/", Some
- rt time now unix micros
- cookie broker document csp policy = "x" repeat
- source origin, "/", Some
- rt time now unix micros
- Reject base-policy errors before forged cookie writes
- var malformed = HostedBrowserRendererProcess create
- fail
- Some
- Reject renderer navigation when active CSP is unavailable
- var navigation = HostedBrowserRendererProcess create
- fail
- Some
- Allow only the parent-authorized initial document bootstrap
- var bootstrap = HostedBrowserRendererProcess create
- Route an opaque HTTPS to HTTP document through navigation policy
- var downgrade = HostedBrowserRendererProcess create
- set mock registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 138 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mocks = MockResponseRegistry.create()
mocks.register("https://bootstrap.test/", 200, "bootstrap")
mocks.register("http://destination.test/", 200, "destination")
set_mock_registry(mocks)

step("Reject an opaque sandbox document that forges a cookie write")
var opaque = HostedBrowserRendererProcess.create(7, 640, 480)
opaque.document_url = "https://source.test/"
opaque.document_origin = "https://source.test"
opaque.document_csp_policy = (
    "sandbox allow-scripts allow-forms allow-top-navigation; " +
    "default-src *"
)
opaque.document_csp_ready = true
opaque.navigation_permit = permit(
    true, "https://source.test/next"
)
opaque.expected_reply_to_request_id = 1
match opaque._dispatch_renderer_fetch(decoded_request(
    7, "opaque-cookie", "document",
    "https://source.test/next", "include",
    ["sid=forged; Path=/"], "null"
)):
    nil:
        fail("Opaque sandbox cookie forgery reached transport")
    Some(result):
        expect(result.reason).to_equal(
            "invalid-renderer-initiator"
        )
expect(observed_mock_request(
    "https://source.test/next"
)).to_be_nil()

step("Reject missing and invalid CSP before cookie mutation")
var cookie_broker = HostedBrowserRendererProcess.create(
    7, 640, 480
)
cookie_broker.document_url = "https://source.test/"
cookie_broker.document_origin = "https://source.test"
cookie_broker.expected_reply_to_request_id = 1
expect(cookie_broker._dispatch_renderer_fetch(decoded_request(
    7, "missing-csp-cookie", "fetch",
    "https://source.test/data", "include",
    ["missing=forged; Path=/"], "https://source.test"
))).to_be_nil()
val source_origin = Origin(
    scheme: "https", host: "source.test", port: 443
)
expect(cookie_broker.network.cookie_store.get_header_for_origin(
    source_origin, "/", Some(source_origin), "GET", false,
    rt_time_now_unix_micros() / 1000000
)).to_equal("")
cookie_broker.pending_wire = ""
cookie_broker.pending_wire_offset = 0
cookie_broker.pending_wire_reply_to_request_id = 0
cookie_broker.pending_wire_is_command = false
cookie_broker.document_csp_ready = true
cookie_broker.document_csp_policy = "x".repeat(65537)
expect(cookie_broker._dispatch_renderer_fetch(decoded_request(
    7, "invalid-csp-cookie", "fetch",
    "https://source.test/data", "include",
    ["invalid=forged; Path=/"], "https://source.test"
))).to_be_nil()
expect(cookie_broker.network.cookie_store.get_header_for_origin(
    source_origin, "/", Some(source_origin), "GET", false,
    rt_time_now_unix_micros() / 1000000
)).to_equal("")

step("Reject base-policy errors before forged cookie writes")
var malformed = HostedBrowserRendererProcess.create(7, 640, 480)
malformed.document_url = "https://source.test/"
malformed.document_origin = "https://source.test"
malformed.expected_reply_to_request_id = 1
match malformed._dispatch_renderer_fetch(decoded_request(
    7, "base-policy-cookie", "fetch",
    "https://source.test/data", "include",
    ["base=forged; Path=/"], "https://source.test",
    "Cookie: renderer-forged"
)):
    nil:
        fail("Base-policy rejection reached cookie mutation")
    Some(result):
        expect(result.reason).to_equal(
            "forbidden-request-header"
        )

step("Reject renderer navigation when active CSP is unavailable")
var navigation = HostedBrowserRendererProcess.create(7, 640, 480)
navigation.document_url = "https://source.test/"
navigation.document_origin = "https://source.test"
navigation.expected_reply_to_request_id = 1
match navigation._dispatch_renderer_fetch(decoded_request(
    7, "missing-csp-navigation", "document",
    "https://destination.test/", "include", [],
    "https://source.test"
)):
    nil:
        fail("Renderer navigation bypassed missing CSP")
    Some(result):
        expect(result.reason).to_equal(
            "csp-policy-unavailable"
        )

step("Allow only the parent-authorized initial document bootstrap")
var bootstrap = HostedBrowserRendererProcess.create(7, 640, 480)
bootstrap.navigation_permit = permit(
    true, "https://bootstrap.test/"
)
bootstrap.expected_reply_to_request_id = 1
expect(bootstrap._dispatch_renderer_fetch(decoded_request(
    7, "trusted-bootstrap", "document",
    "https://bootstrap.test/"
))).to_be_nil()
expect(observed_mock_request(
    "https://bootstrap.test/"
).?).to_be(true)

step("Route an opaque HTTPS to HTTP document through navigation policy")
var downgrade = HostedBrowserRendererProcess.create(7, 640, 480)
downgrade.document_url = "https://source.test/"
downgrade.document_origin = "https://source.test"
downgrade.document_csp_policy = (
    "sandbox allow-scripts allow-forms allow-top-navigation; " +
    "default-src *"
)
downgrade.document_csp_ready = true
downgrade.navigation_permit = permit(
    true, "http://destination.test/"
)
downgrade.expected_reply_to_request_id = 1
expect(downgrade._dispatch_renderer_fetch(decoded_request(
    7, "document-downgrade", "document",
    "http://destination.test/", "include", [], "null"
))).to_be_nil()
expect(observed_mock_request(
    "http://destination.test/"
).?).to_be(true)
set_mock_registry(MockResponseRegistry.create())
```

</details>

#### blocks forged renderer requests with committed CSP before transport

- var mocks = MockResponseRegistry create
- mocks register
- set mock registry
- var broker = HostedBrowserRendererProcess create
- url: Url parse or opaque
- broker  commit document url
- broker navigation permit = permit
- Treat a sandboxed document as an opaque network origin
   - Expected: opaque_fetch.mode equals `RequestMode.Cors`
   - Expected: opaque_fetch.sanitized_headers equals `Origin: null`
- Apply a pending sandbox before the first frame commit
- Tighten rather than discard committed CSP on 304
- url: Url parse or opaque
- broker  commit document url
- Reject a same-origin forged fetch
- browser renderer decoder new
   - Expected: blocked_fetch_message.status equals `message`
   - Expected: blocked_fetch.reason equals `csp-connect-src-blocked`
   - Expected: broker.network_job_handle equals `0`
- Reject a cross-origin forged image beacon
- browser renderer decoder new
   - Expected: blocked_image_message.status equals `message`
   - Expected: blocked_image.reason equals `csp-img-src-blocked`
   - Expected: broker.network_job_handle equals `0`
- Fail closed when committed policy state is missing
   - Expected: missing.reason equals `csp-policy-unavailable`
   - Expected: broker.network_job_handle equals `0`
- Fail closed when committed policy state is invalid
- broker document csp policy = "x" repeat
   - Expected: invalid.reason equals `csp-policy-unavailable`
- Allow only an explicitly admitted control
- browser renderer decoder new
- browser renderer decoder new
   - Expected: broker.network_job_handle equals `0`
- Stage target history CSP and URL before resource dispatch
- broker history urls push
- broker history csp ready push
- broker  stage history document csp
- Restore the broker CSP ledger with history
- broker  restore history document
- Preserve the CSP ledger across production site swaps
- set mock registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 321 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mocks = MockResponseRegistry.create()
for url in [
    "https://app.test/private",
    "https://images.test/beacon",
    "https://app.test/data",
    "https://images.test/pixel.png"
]:
    mocks.register(url, 200, "observed")
set_mock_registry(mocks)
var broker = HostedBrowserRendererProcess.create(7, 640, 480)
val document_url = "https://app.test/index"
val document_request = request(
    "document", document_url, "GET", "", "", "",
    "include", [], ""
)
val document_policy = HostedBrowserRequestPolicy(
    ok: true, reason: "ok", mode: RequestMode.Navigate,
    credentials: "include", canonical_url: document_url,
    sanitized_headers: "", consumes_navigation: true
)
val document_response = broker._finalize_network(
    "document",
    FetchRequest(
        url: Url.parse_or_opaque(document_url),
        method: "GET", headers: "", body: [],
        mode: RequestMode.Navigate, credentials: "include"
    ),
    FetchResponse(
        status: 200,
        headers: (
            "Content-Security-Policy: sandbox; " +
            "default-src 'none'; img-src 'none'"
        ),
        body: rt_text_to_bytes(
            "<meta http-equiv='content-security-policy' " +
            "content=\"connect-src 'none'\">"
        )
    )
)
expect(broker._record_document_response(
    document_request, document_policy, document_response, 0
).is_ok()).to_be(true)
broker.pending_history_action = "push"
broker._commit_document_url(document_url)
expect(broker.document_csp_ready).to_be(true)
expect(broker.document_csp_policy).to_contain(
    "connect-src 'none'"
)
expect(broker._renderer_initiator_valid(request(
    "fetch", "https://app.test/private", "GET", "", "", "",
    "include", [], "https://app.test"
))).to_be(false)
expect(broker.authorize_renderer_navigation(request(
    "document", "https://app.test/next", "GET", "", "", "",
    "include", [], "https://app.test"
))).to_be(false)
expect(broker._renderer_initiator_valid(request(
    "fetch", "https://app.test/private", "GET", "", "", "",
    "omit", ["session=forged"], "null"
))).to_be(false)
broker.navigation_permit = permit(
    true, "https://app.test/next"
)
expect(broker._renderer_initiator_valid(request(
    "document", "https://app.test/next", "GET", "", "", "",
    "include", ["session=forged"], "null"
))).to_be(false)
broker.navigation_permit = permit(false, "")

step("Treat a sandboxed document as an opaque network origin")
broker.document_csp_policy = "sandbox; connect-src *"
val opaque_fetch = broker._renderer_request_policy(
    request(
        "fetch", "https://app.test/private", "GET", "", "", "",
        "omit", [], "null"
    ),
    "https://app.test/private"
)
expect(opaque_fetch.ok).to_be(true)
expect(opaque_fetch.mode).to_equal(RequestMode.Cors)
expect(opaque_fetch.sanitized_headers).to_equal("Origin: null")

step("Apply a pending sandbox before the first frame commit")
broker.document_csp_policy = ""
broker.pending_document_csp_policy = "sandbox"
broker.pending_document_csp_ready = true
broker.provisional_document_origin = "https://app.test"
expect(broker.authorize_renderer_navigation(request(
    "document", "https://app.test/next", "GET", "", "", "",
    "include", [], "null"
))).to_be(false)
broker.document_csp_policy = (
    "sandbox; default-src 'none'; img-src 'none'; " +
    "connect-src 'none'"
)
broker.pending_document_csp_policy = ""
broker.pending_document_csp_ready = false
broker.provisional_document_origin = ""

step("Tighten rather than discard committed CSP on 304")
val not_modified = broker._finalize_network(
    "document",
    FetchRequest(
        url: Url.parse_or_opaque(document_url),
        method: "GET", headers: "", body: [],
        mode: RequestMode.Navigate, credentials: "include"
    ),
    FetchResponse(
        status: 304,
        headers: "Content-Security-Policy: connect-src 'self'",
        body: []
    )
)
expect(broker._record_document_response(
    document_request, document_policy, not_modified, 0
).is_ok()).to_be(true)
broker.pending_history_action = "replace"
broker._commit_document_url(document_url)
expect(broker.document_csp_policy).to_contain(
    "connect-src 'none'"
)
expect(broker.document_csp_policy).to_contain(
    "connect-src 'self'"
)

step("Reject a same-origin forged fetch")
broker.expected_reply_to_request_id = 1
val blocked_fetch_wire = browser_renderer_fetch_request_encode(
    7, 2, 1, "forged-fetch", "fetch",
    "https://app.test/private", "GET", "", "", "",
    "omit", [], "null"
)
expect(blocked_fetch_wire.ok).to_be(true)
val blocked_fetch_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), blocked_fetch_wire.wire
)
expect(blocked_fetch_message.status).to_equal("message")
val blocked_fetch_request = browser_renderer_fetch_request_decode(
    blocked_fetch_message.message
)
val blocked_fetch = broker._renderer_request_policy(
    blocked_fetch_request,
    "https://app.test/private"
)
expect(blocked_fetch.ok).to_be(false)
expect(blocked_fetch.reason).to_equal("csp-connect-src-blocked")
expect(broker._dispatch_renderer_fetch(
    blocked_fetch_request
)).to_be_nil()
expect(observed_mock_request(
    "https://app.test/private"
)).to_be_nil()
expect(broker.network_job_handle).to_equal(0)
expect(broker.pending_wire != "").to_be(true)
broker.pending_wire = ""
broker.pending_wire_offset = 0
broker.pending_wire_reply_to_request_id = 0
broker.pending_wire_is_command = false

step("Reject a cross-origin forged image beacon")
val blocked_image_wire = browser_renderer_fetch_request_encode(
    7, 3, 1, "forged-image", "image",
    "https://images.test/beacon", "GET", "", "", "",
    "omit", [], "null"
)
expect(blocked_image_wire.ok).to_be(true)
val blocked_image_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), blocked_image_wire.wire
)
expect(blocked_image_message.status).to_equal("message")
val blocked_image_request = browser_renderer_fetch_request_decode(
    blocked_image_message.message
)
val blocked_image = broker._renderer_request_policy(
    blocked_image_request,
    "https://images.test/beacon"
)
expect(blocked_image.ok).to_be(false)
expect(blocked_image.reason).to_equal("csp-img-src-blocked")
expect(broker._dispatch_renderer_fetch(
    blocked_image_request
)).to_be_nil()
expect(observed_mock_request(
    "https://images.test/beacon"
)).to_be_nil()
expect(broker.network_job_handle).to_equal(0)
expect(broker.pending_wire != "").to_be(true)
broker.pending_wire = ""
broker.pending_wire_offset = 0
broker.pending_wire_reply_to_request_id = 0
broker.pending_wire_is_command = false

step("Fail closed when committed policy state is missing")
broker.document_csp_ready = false
val missing = broker._renderer_request_policy(
    request(
        "fetch", "https://app.test/private", "GET", "", "", "",
        "omit", [], "https://app.test"
    ),
    "https://app.test/private"
)
expect(missing.ok).to_be(false)
expect(missing.reason).to_equal("csp-policy-unavailable")
expect(broker.network_job_handle).to_equal(0)

step("Fail closed when committed policy state is invalid")
broker.document_csp_ready = true
broker.document_csp_policy = "x".repeat(65537)
val invalid = broker._renderer_request_policy(
    request(
        "fetch", "https://app.test/private", "GET", "", "", "",
        "omit", [], "https://app.test"
    ),
    "https://app.test/private"
)
expect(invalid.ok).to_be(false)
expect(invalid.reason).to_equal("csp-policy-unavailable")
expect(observed_mock_request(
    "https://app.test/private"
)).to_be_nil()

step("Allow only an explicitly admitted control")
broker.document_csp_ready = true
broker.document_csp_policy = (
    "default-src 'none'; connect-src 'self'; " +
    "img-src https://images.test/"
)
val allowed_fetch_wire = browser_renderer_fetch_request_encode(
    7, 4, 1, "allowed-fetch", "fetch",
    "https://app.test/data", "GET", "", "", "",
    "omit", [], "https://app.test"
)
expect(allowed_fetch_wire.ok).to_be(true)
val allowed_fetch_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), allowed_fetch_wire.wire
)
val allowed_fetch_request = browser_renderer_fetch_request_decode(
    allowed_fetch_message.message
)
expect(broker._dispatch_renderer_fetch(
    allowed_fetch_request
)).to_be_nil()
expect(observed_mock_request(
    "https://app.test/data"
).?).to_be(true)
broker.pending_wire = ""
broker.pending_wire_offset = 0
broker.pending_wire_reply_to_request_id = 0
broker.pending_wire_is_command = false

val allowed_image_wire = browser_renderer_fetch_request_encode(
    7, 5, 1, "allowed-image", "image",
    "https://images.test/pixel.png", "GET", "", "", "",
    "omit", [], "https://app.test"
)
expect(allowed_image_wire.ok).to_be(true)
val allowed_image_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), allowed_image_wire.wire
)
val allowed_image_request = browser_renderer_fetch_request_decode(
    allowed_image_message.message
)
expect(broker._dispatch_renderer_fetch(
    allowed_image_request
)).to_be_nil()
expect(observed_mock_request(
    "https://images.test/pixel.png"
).?).to_be(true)
expect(broker.network_job_handle).to_equal(0)

step("Stage target history CSP and URL before resource dispatch")
val original_history_csp = broker.history_csp_policies[0]
broker.history_urls.push("https://next.test/page")
broker.history_csp_policies.push(
    "default-src 'none'; connect-src 'self'"
)
broker.history_csp_ready.push(true)
broker.pending_history_target_url = "https://next.test/page"
broker.provisional_document_origin = "https://next.test"
broker._stage_history_document_csp(1)
expect(broker.pending_document_csp_ready).to_be(true)
expect(broker._renderer_request_policy(
    request(
        "fetch", "https://next.test/data", "GET", "", "", "",
        "omit", [], "https://next.test"
    ),
    "https://next.test/data"
).ok).to_be(true)
expect(broker._renderer_request_policy(
    request(
        "fetch", "https://app.test/private", "GET", "", "", "",
        "omit", [], "null"
    ),
    "https://app.test/private"
).reason).to_equal("csp-connect-src-blocked")
broker.history_urls = [document_url]
broker.history_csp_policies = [original_history_csp]
broker.history_csp_ready = [true]
broker.pending_history_target_url = ""

step("Restore the broker CSP ledger with history")
broker._restore_history_document(0)
expect(broker.document_csp_ready).to_be(true)
expect(broker.document_csp_policy).to_contain(
    "connect-src 'none'"
)

step("Preserve the CSP ledger across production site swaps")
val registry_source = rt_file_read_text(
    "src/os/hosted/hosted_browser_renderer_registry.spl"
) ?? ""
expect(registry_source).to_contain(
    "replacement.history_csp_policies = history_csp_policies"
)
expect(registry_source).to_contain(
    "replacement.document_csp_policy = document_csp_policy"
)
expect(registry_source).to_contain(
    "replacement.pending_document_csp_policy ="
)
set_mock_registry(MockResponseRegistry.create())
```

</details>

#### issues only bounded canonical http navigation permits

- var broker = HostedBrowserRendererProcess create


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
expect(broker.poll()).to_be_nil()
expect(broker.authorize_navigation(
    "file:///etc/passwd", "GET", "", "", ""
)).to_be(false)
expect(broker.authorize_navigation(
    "https://Example.Test/path#section", "GET", "", "", ""
)).to_be(true)
expect(broker.navigation_permit.url).to_equal(
    "https://example.test/path"
)
```

</details>

#### loads persisted HSTS into the trusted navigation permit

- var broker = HostedBrowserRendererProcess create
- BrowserHstsSnapshot create


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val now_ms = rt_time_now_unix_micros() / 1000
var entries: [BrowserHstsSnapshotEntry] = []
entries.push(BrowserHstsSnapshotEntry(
    host: "secure.test",
    received_at_unix_ms: now_ms,
    expires_at_unix_ms: now_ms + 60000,
    include_subdomains: true
))
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
expect(broker.load_hsts_snapshot(
    BrowserHstsSnapshot.create(entries), now_ms
)).to_equal(1)
expect(broker.authorize_navigation(
    "http://sub.secure.test/path", "GET", "", "", ""
)).to_be(true)
expect(broker.navigation_permit.url).to_equal(
    "https://sub.secure.test/path"
)
```

</details>

#### rewrites one trusted redirect location after HSTS upgrade

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = hosted_browser_replace_response_header(
    "Location: http://secure.test/a\nX-Test: yes\n" +
    "location: http://evil.test/",
    "Location",
    "https://secure.test/a"
)
expect(headers).to_equal(
    "Location: https://secure.test/a\r\nX-Test: yes"
)
```

</details>

#### rejects a malformed HTTPS redirect before creating a navigation permit

- Receive a hostile `Location: https:///missing-host` response from the
  authenticated transport.
- Reject it as `invalid-navigation-redirect` without creating a broker navigation
  permit, pending document commit, or provisional origin.

Docgen: pending — this reviewed manual mirror reflects the executable SSpec;
the isolated worktree has no deployed self-hosted runtime.

#### never learns HSTS from generic response finalization

- var broker = HostedBrowserRendererProcess create
- broker network set requester origin
- fetch request
- sts response
   - Expected: denied.error equals `CORS response validation failed`
- sts response
   - Expected: not_found.status equals `404`
- fetch request
- sts response
   - Expected: plaintext.status equals `200`
- fetch request
- sts response
   - Expected: untrusted.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.network.set_requester_origin("https://origin.test")
val denied = broker._finalize_network(
    "fetch",
    fetch_request("https://secure.test/cors", RequestMode.Cors),
    sts_response(200)
)
expect(denied.error).to_equal("CORS response validation failed")
expect(broker.hsts_dirty).to_be(false)
expect(broker.authorize_navigation(
    "http://secure.test/after-cors", "GET", "", "", ""
)).to_be(true)
expect(broker.navigation_permit.url).to_equal(
    "http://secure.test/after-cors"
)

val not_found = broker._finalize_network(
    "document",
    fetch_request(
        "https://status.test/not-found", RequestMode.Navigate
    ),
    sts_response(404)
)
expect(not_found.status).to_equal(404)
expect(broker.hsts_dirty).to_be(false)
expect(broker.authorize_navigation(
    "http://status.test/after-404", "GET", "", "", ""
)).to_be(true)
expect(broker.navigation_permit.url).to_equal(
    "http://status.test/after-404"
)

val plaintext = broker._finalize_network(
    "document",
    fetch_request("http://plaintext.test/", RequestMode.Navigate),
    sts_response(200)
)
expect(plaintext.status).to_equal(200)
expect(broker.authorize_navigation(
    "http://plaintext.test/next", "GET", "", "", ""
)).to_be(true)
expect(broker.navigation_permit.url).to_equal(
    "http://plaintext.test/next"
)

val untrusted = broker._finalize_network(
    "document",
    fetch_request("https://untrusted.test/", RequestMode.Navigate),
    sts_response(200)
)
expect(untrusted.status).to_equal(200)
expect(broker.hsts_dirty).to_be(false)
expect(broker.authorize_navigation(
    "http://untrusted.test/next", "GET", "", "", ""
)).to_be(true)
expect(broker.navigation_permit.url).to_equal(
    "http://untrusted.test/next"
)
```

</details>

#### caps wasm before hex encoding can double the IPC body

- var broker = HostedBrowserRendererProcess create
   - Expected: encoded.body equals `000f10ff`
- body push


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
val encoded = broker._finalize_network(
    "wasm",
    fetch_request(
        "https://example.test/module.wasm", RequestMode.SameOrigin
    ),
    FetchResponse(
        status: 200,
        headers: "Content-Type: application/wasm",
        body: [0u8, 15u8, 16u8, 255u8]
    )
)
expect(encoded.body).to_equal("000f10ff")

var body: [u8] = []
var index = 0
while index < 262145:
    body.push(0u8)
    index = index + 1
expect(hosted_browser_network_response_limit_reason(
    "wasm", "", body
)).to_equal("renderer-network-body-too-large")
```

</details>

#### does not start asynchronous navigation before renderer readiness

- var broker = HostedBrowserRendererProcess create
- Err
   - Expected: reason equals `invalid-renderer-state`
- Ok
   - Expected: broker.command_deadline_ms equals `0`
   - Expected: broker.pending_operation equals ``
   - Expected: broker.pending_document_commit_url equals ``
   - Expected: broker.provisional_document_origin equals ``
   - Expected: broker.network_job_handle equals `0`
   - Expected: broker.pending_wire equals ``
   - Expected: broker.next_request_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
match broker.begin_navigate(
    "https://example.test/", "GET", "", "", "", 1000
):
    Err(reason):
        expect(reason).to_equal("invalid-renderer-state")
    Ok(_):
        expect(false).to_be(true)
expect(broker.command_deadline_ms).to_equal(0)
expect(broker.pending_operation).to_equal("")
expect(broker.pending_document_commit_url).to_equal("")
expect(broker.provisional_document_origin).to_equal("")
expect(broker.network_job_handle).to_equal(0)
expect(broker.pending_wire).to_equal("")
expect(broker.next_request_id).to_equal(2)
expect(broker.navigation_permit.active).to_be(false)
```

</details>

#### treats repeated asynchronous Stop as idempotent

- var broker = HostedBrowserRendererProcess create
- Err
- Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.command_deadline_ms = 100
broker.pending_operation = "stop"
match broker.begin_stop(1000):
    Err(_):
        expect(false).to_be(true)
    Ok(started):
        expect(started).to_be(false)
```

</details>

#### replaces a fully sent slow navigation before stale completion

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.deferred_commands.len() equals `1`
   - Expected: broker.network_job_handle equals `0`
   - Expected: broker.network_job_redirect_count equals `0`
   - Expected: broker.deferred_commands.len() equals `0`
   - Expected: broker.next_animation_ms equals `-1`
   - Expected: broker.pending_document_commit_url equals ``
   - Expected: broker.provisional_document_origin equals ``
- browser renderer decoder new
   - Expected: navigation.action equals `open`
   - Expected: navigation.url equals `https://example.test/new`
   - Expected: broker.pending_wire_reply_to_request_id equals `3`
- browser renderer decoder new
- Err
- fail
- Ok
   - Expected: broker.network_job_handle equals `0`
   - Expected: broker.pending_document_commit_url equals ``
- draw ir composition
- browser renderer decoder new
- Err
- fail
- Ok
   - Expected: broker.pending_history_action equals `push`
   - Expected: broker.pending_document_commit_url equals ``
   - Expected: broker.provisional_document_origin equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 146 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.document_url = "https://example.test/current"
broker.document_origin = "https://example.test"
broker.site_lock = "https://example.test"
broker.history_urls = ["https://example.test/current"]
broker.history_index = 0
broker.history_current_url = "https://example.test/current"
broker.history_back_url = "https://example.test/back"
broker.history_forward_url = "https://example.test/forward"
expect(broker.begin_advance(16, 1000).is_ok()).to_be(true)
broker.pending_wire = ""
broker.pending_wire_is_command = false
broker.expected_reply_to_request_id = 2
broker.next_request_id = 3
broker.pending_operation = "advance"
expect(broker.begin_pointer(
    7, 4, 5, true, 1000
).is_ok()).to_be(true)
expect(broker.deferred_commands.len()).to_equal(1)
broker.pending_operation = "navigation"
broker.network_job_handle = 424242
broker.network_job_fetch = Some(request(
    "document", "https://example.test/slow"
))
broker.network_job_policy = Some(HostedBrowserRequestPolicy(
    ok: true,
    reason: "ok",
    mode: RequestMode.Navigate,
    credentials: "include",
    canonical_url: "https://example.test/slow",
    sanitized_headers: "",
    consumes_navigation: true
))
broker.network_job_request = Some(fetch_request(
    "https://example.test/slow", RequestMode.Navigate
))
broker.network_job_redirect_count = 3
broker.next_animation_ms = 16
broker.navigation_permit = permit(
    true, "https://example.test/slow"
)
broker.pending_history_action = "push"
broker.pending_document_commit_url = (
    "https://example.test/slow"
)
broker.provisional_document_origin = "https://example.test"
broker.stop_after_write = true

val replaced = broker.begin_navigate(
    "https://example.test/new", "GET", "", "", "", 1000
)

expect(replaced.is_ok()).to_be(true)
expect(broker.network_job_handle).to_equal(0)
expect(broker.network_job_fetch).to_be_nil()
expect(broker.network_job_policy).to_be_nil()
expect(broker.network_job_request).to_be_nil()
expect(broker.network_job_redirect_count).to_equal(0)
expect(broker.deferred_commands.len()).to_equal(0)
expect(broker.next_animation_ms).to_equal(-1)
expect(broker.stop_after_write).to_be(false)
expect(broker.pending_document_commit_url).to_equal("")
expect(broker.provisional_document_origin).to_equal("")
expect(broker.navigation_permit.url).to_equal(
    "https://example.test/new"
)
val replacement = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
val navigation = browser_renderer_navigation_decode(
    replacement.message
)
expect(navigation.action).to_equal("open")
expect(navigation.url).to_equal("https://example.test/new")
expect(broker.pending_wire_reply_to_request_id).to_equal(3)
broker.expected_reply_to_request_id = (
    broker.pending_wire_reply_to_request_id
)
val old_wire = browser_renderer_fetch_request_encode(
    1, 50, 2, "stale-fetch", "document",
    "https://example.test/slow", "GET", "", "", "",
    "include", [], "https://example.test"
)
expect(old_wire.ok).to_be(true)
val old_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), old_wire.wire
)
val old_fetch = browser_renderer_fetch_request_decode(
    old_message.message
)
match broker._poll_renderer_reply(
    old_fetch.reply_to_request_id, "stale-renderer-request"
):
    Err(reason):
        fail(reason)
    Ok(current):
        expect(current).to_be(false)
expect(broker.network_job_handle).to_equal(0)
expect(broker.pending_document_commit_url).to_equal("")
expect(broker.navigation_permit.url).to_equal(
    "https://example.test/new"
)
val stale_frame_wire = (
    browser_renderer_frame_encode_with_state_and_images(
        draw_ir_composition("", "", "", []),
        1, 51, 2, -1, 0, "", 0, "", "",
        "https://attacker.test/stale",
        "https://attacker.test/back",
        "https://attacker.test/forward",
        []
    )
)
expect(stale_frame_wire.ok).to_be(true)
val stale_frame = browser_renderer_frame_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(1), stale_frame_wire.wire
    ).message,
    640, 480
)
expect(stale_frame.ok).to_be(true)
match broker._poll_renderer_reply(
    stale_frame.reply_to_request_id, "stale-renderer-frame"
):
    Err(reason):
        fail(reason)
    Ok(current):
        expect(current).to_be(false)
expect(broker.document_url).to_equal(
    "https://example.test/current"
)
expect(broker.pending_history_action).to_equal("push")
expect(broker.history_current_url).to_equal(
    "https://example.test/current"
)
expect(broker.history_back_url).to_equal(
    "https://example.test/back"
)
expect(broker.history_forward_url).to_equal(
    "https://example.test/forward"
)
expect(broker.pending_document_commit_url).to_equal("")
expect(broker.provisional_document_origin).to_equal("")
expect(broker.navigation_permit.url).to_equal(
    "https://example.test/new"
)
```

</details>

#### preserves a slow navigation when its replacement is invalid

- var broker = HostedBrowserRendererProcess create
- "javascript:alert
   - Expected: rejected.unwrap_err() equals `invalid-navigation`
   - Expected: broker.network_job_handle equals `424243`
   - Expected: broker.network_job_redirect_count equals `4`
   - Expected: broker.next_animation_ms equals `32`
   - Expected: broker.pending_operation equals `navigation`
   - Expected: broker.pending_history_action equals `push`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.document_url = "https://example.test/current"
broker.document_origin = "https://example.test"
broker.command_deadline_ms = 9000000000000
broker.pending_operation = "navigation"
broker.expected_reply_to_request_id = 2
broker.next_request_id = 3
broker.network_job_handle = 424243
broker.network_job_fetch = Some(request(
    "document", "https://example.test/slow"
))
broker.network_job_policy = Some(HostedBrowserRequestPolicy(
    ok: true,
    reason: "ok",
    mode: RequestMode.Navigate,
    credentials: "include",
    canonical_url: "https://example.test/slow",
    sanitized_headers: "",
    consumes_navigation: true
))
broker.network_job_request = Some(fetch_request(
    "https://example.test/slow", RequestMode.Navigate
))
broker.network_job_redirect_count = 4
broker.next_animation_ms = 32
broker.navigation_permit = permit(
    true, "https://example.test/slow"
)
broker.pending_history_action = "push"
broker.pending_document_commit_url = (
    "https://example.test/slow"
)
broker.provisional_document_origin = "https://example.test"

val rejected = broker.begin_navigate(
    "javascript:alert(1)", "GET", "", "", "", 1000
)

expect(rejected.is_err()).to_be(true)
expect(rejected.unwrap_err()).to_equal("invalid-navigation")
expect(broker.network_job_handle).to_equal(424243)
expect(broker.network_job_fetch.is_some()).to_be(true)
expect(broker.network_job_policy.is_some()).to_be(true)
expect(broker.network_job_request.is_some()).to_be(true)
expect(broker.network_job_redirect_count).to_equal(4)
expect(broker.next_animation_ms).to_equal(32)
expect(broker.pending_operation).to_equal("navigation")
expect(broker.pending_history_action).to_equal("push")
expect(broker.pending_document_commit_url).to_equal(
    "https://example.test/slow"
)
expect(broker.provisional_document_origin).to_equal(
    "https://example.test"
)
expect(broker.navigation_permit.url).to_equal(
    "https://example.test/slow"
)
```

</details>

#### preserves a partially written navigation frame

- var broker = HostedBrowserRendererProcess create
   - Expected: replacement.unwrap_err() equals `renderer-busy`
   - Expected: broker.pending_wire_offset equals `1`
   - Expected: broker.pending_wire_reply_to_request_id equals `2`
   - Expected: broker.pending_operation equals `navigation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.command_deadline_ms = 9000000000000
broker.pending_operation = "navigation"
broker.pending_wire = "partially-written-navigation"
broker.pending_wire_offset = 1
broker.pending_wire_reply_to_request_id = 2
broker.pending_wire_is_command = true
broker.navigation_permit = permit(
    true, "https://example.test/slow"
)

val replacement = broker.begin_navigate(
    "https://example.test/new", "GET", "", "", "", 1000
)

expect(replacement.is_err()).to_be(true)
expect(replacement.unwrap_err()).to_equal("renderer-busy")
expect(broker.pending_wire).to_equal(
    "partially-written-navigation"
)
expect(broker.pending_wire_offset).to_equal(1)
expect(broker.pending_wire_reply_to_request_id).to_equal(2)
expect(broker.pending_operation).to_equal("navigation")
expect(broker.navigation_permit.url).to_equal(
    "https://example.test/slow"
)
```

</details>

#### defers Stop until a partially written navigation command is complete

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.pending_operation equals `navigation`
   - Expected: broker._begin_stop_after_write() equals ``
   - Expected: broker.pending_operation equals `stop`
- browser renderer decoder new
   - Expected: broker.pending_history_action equals ``
   - Expected: broker.pending_document_commit_url equals ``
   - Expected: broker.provisional_document_origin equals ``
   - Expected: broker.network_job_redirect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.command_deadline_ms = 9000000000000
broker.pending_operation = "navigation"
broker.pending_wire = "partially-written-navigation"
broker.pending_wire_offset = 1
broker.pending_wire_reply_to_request_id = 2
broker.pending_wire_is_command = true
broker.navigation_permit = permit(
    true, "https://example.test/pending"
)
broker.pending_history_action = "push"
broker.pending_document_commit_url = (
    "https://example.test/pending"
)
broker.provisional_document_origin = "https://example.test"
broker.network_job_fetch = Some(request(
    "document", "https://example.test/pending"
))
broker.network_job_redirect_count = 3

val scheduled = broker.begin_stop(1000)
expect(scheduled.is_ok()).to_be(true)
expect(scheduled.unwrap()).to_be(true)
expect(broker.stop_after_write).to_be(true)
expect(broker.pending_operation).to_equal("navigation")
val repeated = broker.begin_stop(1000)
expect(repeated.is_ok()).to_be(true)
expect(repeated.unwrap()).to_be(false)

# Simulate the bounded writer completing the stale command.
broker.expected_reply_to_request_id = 2
broker.next_request_id = 3
broker.pending_wire = ""
broker.pending_wire_offset = 0
broker.pending_wire_reply_to_request_id = 0
broker.pending_wire_is_command = false
expect(broker._begin_stop_after_write()).to_equal("")

expect(broker.stop_after_write).to_be(false)
expect(broker.pending_operation).to_equal("stop")
val decoded = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
expect(browser_renderer_navigation_decode(
    decoded.message
).action).to_equal("stop")
expect(broker.navigation_permit.active).to_be(false)
expect(broker.pending_history_action).to_equal("")
expect(broker.pending_document_commit_url).to_equal("")
expect(broker.provisional_document_origin).to_equal("")
expect(broker.network_job_fetch).to_be_nil()
expect(broker.network_job_redirect_count).to_equal(0)
```

</details>

#### authorizes Reload and replaces its current history entry

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.pending_history_action equals `replace`
- broker  commit document url
   - Expected: broker.history_urls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.document_url = "https://example.test/old"
broker.document_origin = "https://example.test"
broker.history_urls = ["https://example.test/old"]
broker.history_index = 0
expect(broker.begin_reload(1000).is_ok()).to_be(true)
expect(broker.navigation_permit.active).to_be(true)
expect(broker.navigation_permit.url).to_equal(
    "https://example.test/old"
)
expect(broker.pending_history_action).to_equal("replace")
broker._commit_document_url("https://example.test/new")
expect(broker.history_urls.len()).to_equal(1)
expect(broker.history_urls[0]).to_equal(
    "https://example.test/new"
)
```

</details>

#### synchronizes same-origin history state into parent Back and Forward

- var broker = HostedBrowserRendererProcess create
- browser renderer decoder new
   - Expected: back_navigation.action equals `back`
   - Expected: back_navigation.url equals `https://example.test/start`
- browser renderer decoder new
   - Expected: forward_navigation.action equals `forward`


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.document_url = "https://example.test/start"
broker.document_origin = "https://example.test"
broker.history_urls = ["https://example.test/start"]
broker.history_index = 0
expect(broker._frame_history_state_valid(
    "https://example.test/next#view",
    "https://example.test/start",
    ""
)).to_be(true)
expect(broker._frame_history_state_valid(
    "https://attacker.test/", "", ""
)).to_be(false)
expect(broker._frame_history_state_valid(
    "https://example.test/next", "https://attacker.test/", ""
)).to_be(false)
broker.history_urls = [
    "https://unrelated.test/",
    "https://previous.test/",
    "https://example.test/start"
]
broker.history_index = 2
expect(broker._frame_history_state_valid(
    "https://example.test/next",
    "https://previous.test/",
    ""
)).to_be(true)
expect(broker._frame_history_state_valid(
    "https://example.test/next",
    "https://unrelated.test/",
    ""
)).to_be(false)
broker.history_urls = ["https://example.test/start"]
broker.history_index = 0
broker._apply_frame_history_state(
    "https://example.test/next#view",
    "https://example.test/start",
    ""
)
expect(broker.document_url).to_equal(
    "https://example.test/next#view"
)
expect(broker.begin_go_back(1000).is_ok()).to_be(true)
val back = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
val back_navigation = browser_renderer_navigation_decode(back.message)
expect(back_navigation.ok).to_be(true)
expect(back_navigation.action).to_equal("back")
expect(back_navigation.url).to_equal("https://example.test/start")

broker.pending_wire = ""
broker.pending_wire_is_command = false
broker.command_deadline_ms = 0
broker.pending_operation = ""
broker._apply_frame_history_state(
    "https://example.test/start",
    "",
    "https://example.test/next#view"
)
expect(broker.begin_go_forward(1000).is_ok()).to_be(true)
val forward = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
val forward_navigation = browser_renderer_navigation_decode(
    forward.message
)
expect(forward_navigation.ok).to_be(true)
expect(forward_navigation.action).to_equal("forward")
expect(forward_navigation.url).to_equal(
    "https://example.test/next#view"
)
```

</details>

#### accepts the previous displayed URL across a network commit

- var broker = HostedBrowserRendererProcess create


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.document_url = "https://a.test/start"
broker.document_origin = "https://a.test"
broker.history_urls = ["https://a.test/start"]
broker.history_index = 0
broker.history_current_url = "https://a.test/start#view"
broker.pending_document_commit_url = "https://b.test/next"
broker.pending_history_action = "push"
expect(broker._frame_history_state_valid(
    "https://b.test/next",
    "https://a.test/start#view",
    ""
)).to_be(true)
```

</details>

#### rejects a forged legacy frame before committing a pending document

A legacy `SBRF2` frame has no history state. While a broker-authorized
document response is pending, that omission fails and tears down the broker
before it can commit the target URL or advance history. Only a state-bearing
renderer reply may complete the transition.

- Send a state-less renderer frame while a document is pending
   - Expected: the decoded frame has no history state
- Fail closed before the forged frame can commit the target
   - Expected: rejection reason equals `missing-frame-history`
   - Expected: broker is failed and closed without committing the target

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send a state-less renderer frame while a document is pending")
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.document_url = "https://source.test/start"
broker.document_origin = "https://source.test"
broker.history_urls = ["https://source.test/start"]
broker.history_index = 0
broker.history_current_url = "https://source.test/start"
broker.pending_history_action = "push"
broker.pending_document_commit_url = "https://target.test/private"
broker.provisional_document_origin = "https://target.test"
broker.expected_reply_to_request_id = 2
val forged_wire = browser_renderer_frame_encode(
    draw_ir_composition("", "", "", []), 1, 2
)
expect(forged_wire.ok).to_be(true)
val forged = browser_renderer_frame_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(1), forged_wire.wire
    ).message,
    640, 480
)
expect(forged.history_state_present).to_be(false)

step("Fail closed before the forged frame can commit the target")
val rejected = broker._accept_decoded_frame(forged, 1)
expect(rejected.ok).to_be(false)
expect(rejected.reason).to_equal("missing-frame-history")
expect(broker.state).to_equal("failed")
expect(broker.document_url).to_equal("")
expect(broker.history_urls.len()).to_equal(0)
```

</details>

#### resolves duplicate history URLs in the requested direction

- var back = HostedBrowserRendererProcess create
   - Expected: back.pending_history_index equals `0`
- var forward = HostedBrowserRendererProcess create
   - Expected: forward.pending_history_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var back = HostedBrowserRendererProcess.create(1, 640, 480)
back.state = "active"
back.history_urls = ["https://a.test/", "https://a.test/"]
back.history_index = 1
back.history_current_url = "https://a.test/"
back.history_back_url = "https://a.test/"
expect(back.begin_go_back(1000).is_ok()).to_be(true)
expect(back.pending_history_index).to_equal(0)

var forward = HostedBrowserRendererProcess.create(1, 640, 480)
forward.state = "active"
forward.history_urls = ["https://a.test/", "https://a.test/"]
forward.history_index = 0
forward.history_current_url = "https://a.test/"
forward.history_forward_url = "https://a.test/"
expect(forward.begin_go_forward(1000).is_ok()).to_be(true)
expect(forward.pending_history_index).to_equal(1)
```

</details>

#### queues asynchronous page input without draining the pipe

- var broker = HostedBrowserRendererProcess create
- Err
- Ok
   - Expected: broker.pending_wire_offset equals `0`
   - Expected: broker.pending_wire_reply_to_request_id equals `2`
   - Expected: broker.expected_reply_to_request_id equals `0`
   - Expected: broker.next_request_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
match broker.begin_pointer(1, 20, 30, true, 1000):
    Err(_):
        expect(false).to_be(true)
    Ok(started):
        expect(started).to_be(true)
expect(broker.pending_wire).to_start_with("SBR1\tpointer")
expect(broker.pending_wire_offset).to_equal(0)
expect(broker.pending_wire_reply_to_request_id).to_equal(2)
expect(broker.expected_reply_to_request_id).to_equal(0)
expect(broker.next_request_id).to_equal(2)
```

</details>

#### coalesces wheel input without occupying the discrete command slot

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.pending_scroll_delta_milli_y equals `1250`
   - Expected: broker.pending_wire equals ``
   - Expected: broker.pending_scroll_delta_milli_y equals `1250`
   - Expected: broker.pending_operation equals `navigation`
   - Expected: broker.pending_scroll_delta_milli_y equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
expect(broker.queue_scroll(1, 500).is_ok()).to_be(true)
expect(broker.queue_scroll(2, 750).is_ok()).to_be(true)
expect(broker.pending_scroll_delta_milli_y).to_equal(1250)
expect(broker.pending_wire).to_equal("")

broker.command_deadline_ms = 100
broker.pending_operation = "navigation"
expect(broker.flush_scroll(1000).is_err()).to_be(true)
expect(broker.pending_scroll_delta_milli_y).to_equal(1250)
expect(broker.pending_operation).to_equal("navigation")

broker.command_deadline_ms = 0
broker.pending_operation = ""
expect(broker.flush_scroll(1000).is_ok()).to_be(true)
expect(broker.pending_wire).to_start_with("SBR1\tscroll")
expect(broker.pending_scroll_delta_milli_y).to_equal(0)
```

</details>

#### does not let page input replace a pending navigation

- var broker = HostedBrowserRendererProcess create
- Err
   - Expected: reason equals `renderer-busy`
- Ok
   - Expected: broker.state equals `active`
   - Expected: broker.pending_operation equals `navigation`
   - Expected: broker.deferred_commands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.command_deadline_ms = 100
broker.pending_operation = "navigation"
match broker.begin_pointer(1, 4, 5, true, 1000):
    Err(reason):
        expect(reason).to_equal("renderer-busy")
    Ok(_):
        expect(false).to_be(true)
expect(broker.state).to_equal("active")
expect(broker.pending_operation).to_equal("navigation")
expect(broker.deferred_commands.len()).to_equal(0)
```

</details>

#### should preserve immediate pointer press and release in order

1. Queue a primary page pointer press.
2. Cancel the page press before chrome takes ownership.
3. Decode the deferred renderer cancellation.
4. Ignore a redundant cancellation without queuing a command.


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Queue a primary page pointer press")
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
expect(broker.begin_pointer(
    1, 4, 5, true, 1000
).is_ok()).to_be(true)
expect(broker.pointer_pressed).to_be(true)
val pressed_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
expect(browser_renderer_action_decode(
    pressed_message.message
).pressed).to_be(true)

step("Cancel the page press before chrome takes ownership")
expect(broker.cancel_pointer(
    2, 1000
).is_ok()).to_be(true)
expect(broker.pointer_pressed).to_be(false)
expect(broker.deferred_commands.len()).to_equal(1)

step("Decode the deferred renderer cancellation")
broker.pending_wire = ""
broker.pending_wire_is_command = false
broker.command_deadline_ms = 0
broker.pending_operation = ""
broker.next_request_id = 3
expect(broker._activate_deferred_command()).to_equal("")
val released_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
val released = browser_renderer_action_decode(
    released_message.message
)
expect(released.event_id).to_equal(2)
expect(released.pressed).to_be(false)
expect(broker.deferred_commands.len()).to_equal(0)

step("Ignore a redundant cancellation without queuing a command")
var idle = HostedBrowserRendererProcess.create(2, 640, 480)
idle.state = "active"
match idle.cancel_pointer(3, 1000):
    Err(reason):
        fail("redundant pointer cancellation failed: {reason}")
    Ok(queued):
        expect(queued).to_be(false)
expect(idle.pending_wire).to_equal("")
```

</details>

#### should retry a page pointer cancellation after renderer work drains

1. Queue a page press while a resource job becomes active.
2. Retain one cancellation while the renderer is busy.
3. Drain prior work and emit the retained pointer release.
4. Acknowledge the cancellation before releasing its owner state.


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Queue a page press while a resource job becomes active")
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
expect(broker.begin_pointer(
    1, 4, 5, true, 1000
).is_ok()).to_be(true)
broker.network_job_handle = 41

step("Retain the cancellation while the renderer is busy")
expect(broker.cancel_pointer(
    2, 1000
).is_ok()).to_be(true)
expect(broker.pointer_pressed).to_be(false)
expect(broker.pending_pointer_cancel_event_id).to_equal(2)
match broker.cancel_pointer(99, 1000):
    Err(reason):
        fail("retained pointer cancellation failed: {reason}")
    Ok(queued):
        expect(queued).to_be(false)
expect(broker.pending_pointer_cancel_event_id).to_equal(2)
match broker.begin_pointer(3, 5, 5, true, 1000):
    Err(reason):
        expect(reason).to_equal("pointer-cancel-pending")
    Ok(_):
        fail("page press replaced a retained pointer cancellation")

step("Drain prior work and emit the retained pointer release")
broker.network_job_handle = 0
broker.pending_wire = ""
broker.pending_wire_is_command = false
broker.command_deadline_ms = 0
broker.pending_operation = ""
broker.next_request_id = 3
expect(broker.flush_pointer_cancel(
    1000
).is_ok()).to_be(true)
val canceled_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
val canceled = browser_renderer_action_decode(
    canceled_message.message
)
expect(canceled.event_id).to_equal(2)
expect(canceled.pressed).to_be(false)
expect(broker.pointer_pressed).to_be(false)
expect(broker.pending_operation).to_equal("pointer-cancel")
expect(broker.pending_pointer_cancel_event_id).to_equal(2)

step("Acknowledge the cancellation before releasing its owner state")
val ack_wire = browser_renderer_frame_encode_with_state_and_images(
    draw_ir_composition("", "", "", []),
    1, 41, 3, -1, 0, "", 0, "", "", "", "", "", []
)
val ack = browser_renderer_frame_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(1), ack_wire.wire
    ).message,
    640, 480
)
broker.expected_reply_to_request_id = 3
expect(broker._accept_decoded_frame(ack, 1).ok).to_be(true)
expect(broker.pending_pointer_cancel_event_id).to_equal(0)
```

</details>

#### coalesces an unsent animation but defers after it is sent

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.pending_operation equals `pointer`
   - Expected: broker.pending_operation equals `advance`
   - Expected: broker.deferred_commands.len() equals `1`
   - Expected: broker.expected_reply_to_request_id equals `2`
   - Expected: broker.next_request_id equals `3`
   - Expected: broker._activate_deferred_command() equals ``
- browser renderer decoder new
   - Expected: activated.message.kind equals `key`
   - Expected: activated.message.request_id equals `4`
   - Expected: broker.pending_wire_reply_to_request_id equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
expect(broker.begin_advance(16, 1000).is_ok()).to_be(true)
expect(broker.begin_pointer(1, 4, 5, true, 1000).is_ok()).to_be(true)
expect(broker.pending_operation).to_equal("pointer")
expect(broker.pending_wire).to_start_with("SBR1\tpointer")

broker.pending_wire = ""
broker.pending_wire_is_command = false
broker.expected_reply_to_request_id = 2
broker.next_request_id = 3
broker.pending_operation = "advance"
expect(broker.begin_key(2, 65, true, 1000).is_ok()).to_be(true)
expect(broker.pending_operation).to_equal("advance")
expect(broker.deferred_commands.len()).to_equal(1)
expect(broker.expected_reply_to_request_id).to_equal(2)
expect(broker.next_request_id).to_equal(3)
broker.next_request_id = 4
expect(broker._activate_deferred_command()).to_equal("")
val activated = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
expect(activated.message.kind).to_equal("key")
expect(activated.message.request_id).to_equal(4)
expect(broker.pending_wire_reply_to_request_id).to_equal(4)
```

</details>

#### coalesces a resize storm to the latest deferred dimensions

- var broker = HostedBrowserRendererProcess create
- Err
- Ok
   - Expected: broker.deferred_commands.len() equals `1`
   - Expected: broker._activate_deferred_command() equals ``
   - Expected: broker.pending_operation equals `resize`
   - Expected: broker.pending_resize_width equals `800`
   - Expected: broker.pending_resize_height equals `600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
expect(broker.begin_pointer(
    1, 4, 5, true, 1000
).is_ok()).to_be(true)
var i: i32 = 1
while i <= 100:
    expect(broker.begin_resize(
        700 + i, 500 + i, 1000
    ).is_ok()).to_be(true)
    i = i + 1
match broker.begin_resize(800, 600, 1000):
    Err(_):
        expect(false).to_be(true)
    Ok(started):
        expect(started).to_be(false)
expect(broker.deferred_commands.len()).to_equal(1)

broker.pending_wire = ""
broker.pending_wire_is_command = false
broker.command_deadline_ms = 0
broker.pending_operation = ""
broker.next_request_id = 3
expect(broker._activate_deferred_command()).to_equal("")
expect(broker.pending_operation).to_equal("resize")
expect(broker.pending_resize_width).to_equal(800)
expect(broker.pending_resize_height).to_equal(600)
```

</details>

#### does not erase an animation network response to queue input

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.pending_wire equals `network-response`
   - Expected: broker.deferred_commands.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.state = "active"
broker.command_deadline_ms = 100
broker.pending_operation = "advance"
broker.pending_wire = "network-response"
broker.pending_wire_is_command = false
broker.next_request_id = 3
expect(broker.begin_text_input(3, "x", 1000).is_ok()).to_be(true)
expect(broker.pending_wire).to_equal("network-response")
expect(broker.deferred_commands.len()).to_equal(1)
```

</details>

#### retains the process handle when native close fails

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.pid equals `999999999`
   - Expected: broker.state equals `active`
   - Expected: broker.state equals `closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.pid = 999999999
broker.state = "active"
expect(broker.close()).to_be(false)
expect(broker.pid).to_equal(999999999)
expect(broker.state).to_equal("active")
broker.pid = 0
expect(broker.close()).to_be(true)
expect(broker.state).to_equal("closed")
```

</details>

#### clears a renderer handle already reaped by liveness

- var broker = HostedBrowserRendererProcess create
- Some
   - Expected: result.reason equals `renderer-crashed`
   - Expected: "missing-result" equals `renderer-crashed`
   - Expected: broker.pid equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.pid = 999999999
broker.state = "active"
broker.command_deadline_ms = 9000000000000
val polled = broker.poll()
match polled:
    Some(result):
        expect(result.reason).to_equal("renderer-crashed")
    nil:
        expect("missing-result").to_equal("renderer-crashed")
expect(broker.pid).to_equal(0)
```

</details>

#### denies a renderer document request without a parent permit

- permit
- request
   - Expected: policy.reason equals `unauthorized-document-request`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = hosted_browser_renderer_request_policy(
    "",
    permit(false, ""),
    request("document", "https://example.test/")
)
expect(policy.ok).to_be(false)
expect(policy.reason).to_equal("unauthorized-document-request")
```

</details>

#### authorizes only canonical renderer link and supported form shapes

- var initial = HostedBrowserRendererProcess create
- var link = HostedBrowserRendererProcess create
- var forged = HostedBrowserRendererProcess create
- var parent = HostedBrowserRendererProcess create


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var initial = HostedBrowserRendererProcess.create(1, 640, 480)
expect(initial.authorize_renderer_navigation(request(
    "document", "https://destination.test/"
))).to_be(false)

var link = HostedBrowserRendererProcess.create(1, 640, 480)
link.document_url = "https://source.test/page"
link.document_origin = "https://source.test"
link.document_csp_policy = "default-src *"
link.document_csp_ready = true
expect(link.authorize_renderer_navigation(request(
    "document", "https://destination.test/"
))).to_be(true)
expect(link.navigation_permit.url).to_equal(
    "https://destination.test/"
)

var forged = HostedBrowserRendererProcess.create(1, 640, 480)
forged.document_url = "https://source.test/page"
forged.document_origin = "https://source.test"
forged.document_csp_policy = "default-src *"
forged.document_csp_ready = true
expect(forged.authorize_renderer_navigation(request(
    "document", "https://destination.test/", "GET",
    "X-Renderer: forged"
))).to_be(false)
expect(forged.authorize_renderer_navigation(request(
    "document", "https://destination.test/", "GET",
    "", "body"
))).to_be(false)
expect(forged.authorize_renderer_navigation(request(
    "document", "https://destination.test/", "POST",
    "", "name=value", "text/plain"
))).to_be(false)

var parent = HostedBrowserRendererProcess.create(1, 640, 480)
parent.document_url = "https://source.test/page"
parent.document_origin = "https://source.test"
parent.document_csp_policy = "default-src *"
parent.document_csp_ready = true
expect(parent.authorize_navigation(
    "https://allowed.test/", "GET", "", "", ""
)).to_be(true)
expect(parent.authorize_renderer_navigation(request(
    "document", "https://attacker.test/"
))).to_be(false)
expect(parent.navigation_permit.url).to_equal(
    "https://allowed.test/"
)
```

</details>

#### accepts exactly one matching parent navigation shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = hosted_browser_renderer_request_policy(
    "",
    permit(
        true,
        "https://example.test/form",
        "POST",
        "Content-Type: application/x-www-form-urlencoded",
        "name=value",
        "application/x-www-form-urlencoded"
    ),
    request(
        "document",
        "https://example.test/form",
        "POST",
        "",
        "name=value",
        "application/x-www-form-urlencoded"
    )
)
expect(policy.ok).to_be(true)
expect(policy.mode == RequestMode.Navigate).to_be(true)
expect(policy.consumes_navigation).to_be(true)
```

</details>

#### rejects a document request that changes the permitted target

- permit
- request
   - Expected: policy.reason equals `unauthorized-document-request`
- permit
- request


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = hosted_browser_renderer_request_policy(
    "",
    permit(true, "https://example.test/allowed"),
    request("document", "https://example.test/other")
)
expect(policy.ok).to_be(false)
expect(policy.reason).to_equal("unauthorized-document-request")
val split_transport = hosted_browser_renderer_request_policy(
    "",
    permit(true, "https://example.test/allowed"),
    request("document", "http://example.test/allowed"),
    "https://example.test/allowed"
)
expect(split_transport.ok).to_be(false)
expect(split_transport.reason).to_equal(
    "unauthorized-document-request"
)
```

</details>

#### derives same-origin mode from broker committed state

- permit
   - Expected: policy.credentials equals `credentials`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for credentials in ["omit", "same-origin", "include"]:
    val policy = hosted_browser_renderer_request_policy(
        "https://example.test",
        permit(false, ""),
        request(
            "script", "https://example.test/app.js", "GET",
            "", "", "", credentials
        )
    )
    expect(policy.ok).to_be(true)
    expect(policy.mode == RequestMode.SameOrigin).to_be(true)
    expect(policy.credentials).to_equal(credentials)
```

</details>

#### requires exact supported renderer credentials

- permit
   - Expected: policy.reason equals `invalid-request-credentials`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for credentials in ["Include", "same_origin", "", " include"]:
    val policy = hosted_browser_renderer_request_policy(
        "https://example.test",
        permit(false, ""),
        request(
            "script", "https://example.test/app.js", "GET",
            "", "", "", credentials
        )
    )
    expect(policy.ok).to_be(false)
    expect(policy.reason).to_equal("invalid-request-credentials")
```

</details>

#### requires include credentials for parent-authorized documents

- permit


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for credentials in ["omit", "same-origin"]:
    val policy = hosted_browser_renderer_request_policy(
        "",
        permit(true, "https://example.test/"),
        request(
            "document", "https://example.test/", "GET",
            "", "", "", credentials
        )
    )
    expect(policy.ok).to_be(false)
    expect(policy.reason).to_equal(
        "unauthorized-document-request"
    )
```

</details>

#### requires cors for simple cross-origin resources

- permit
   - Expected: policy.credentials equals `omit`
- url: Url parse or opaque
- permit
   - Expected: forged.reason equals `forbidden-request-header`
- permit
   - Expected: same_origin_credentials.credentials equals `same-origin`
- permit
   - Expected: credentialed.credentials equals `include`


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = hosted_browser_renderer_request_policy(
    "https://example.test",
    permit(false, ""),
    request(
        "style", "https://cdn.test/app.css", "GET",
        "", "", "", "omit"
    )
)
expect(policy.ok).to_be(true)
expect(policy.mode == RequestMode.Cors).to_be(true)
expect(policy.credentials).to_equal("omit")
expect(policy.sanitized_headers).to_equal(
    "Origin: https://example.test"
)
val wire = build_request_bytes(FetchRequest(
    method: "GET",
    url: Url.parse_or_opaque(policy.canonical_url),
    headers: policy.sanitized_headers,
    body: [],
    mode: policy.mode,
    credentials: "omit"
))
expect(wire).to_contain(
    "\r\nOrigin: https://example.test\r\n"
)

val forged = hosted_browser_renderer_request_policy(
    "https://example.test",
    permit(false, ""),
    request(
        "style", "https://cdn.test/app.css", "GET",
        "Origin: https://evil.test"
    )
)
expect(forged.ok).to_be(false)
expect(forged.reason).to_equal("forbidden-request-header")
expect(wire.contains("evil.test")).to_be(false)

val same_origin_credentials = hosted_browser_renderer_request_policy(
    "https://example.test",
    permit(false, ""),
    request(
        "style", "https://cdn.test/app.css", "GET",
        "", "", "", "same-origin"
    )
)
expect(same_origin_credentials.ok).to_be(true)
expect(same_origin_credentials.credentials).to_equal("same-origin")

val credentialed = hosted_browser_renderer_request_policy(
    "https://example.test",
    permit(false, ""),
    request(
        "style", "https://cdn.test/app.css", "GET",
        "", "", "", "include"
    )
)
expect(credentialed.ok).to_be(true)
expect(credentialed.credentials).to_equal("include")
```

</details>

#### rejects renderer-authored cookie request headers

- permit
   - Expected: policy.reason equals `forbidden-request-header`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for header in [
    "Cookie: sid=secret", "cOoKiE2: sid=secret",
    "Sec-Fetch-Site: same-origin", "Proxy-Authorization: secret",
    "Accept-Encoding: gzip", "Access-Control-Request-Method: PUT",
    "Referer: https://forged.test/", "Via: forged"
]:
    val policy = hosted_browser_renderer_request_policy(
        "https://example.test",
        permit(false, ""),
        request(
            "fetch", "https://example.test/data", "GET", header
        )
    )
    expect(policy.ok).to_be(false)
    expect(policy.reason).to_equal("forbidden-request-header")
```

</details>

#### binds ordered script cookie writes to the active document origin

- var broker = HostedBrowserRendererProcess create
- old origin, "/next", Some
- rt time now unix micros
- new origin, "/next", Some
- rt time now unix micros
- old origin, "/next", Some
- rt time now unix micros


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.document_url = "https://old.test/app"
broker.document_origin = "https://old.test"
expect(broker._apply_script_cookie_writes([
    "first=one; Path=/", "second=two; Path=/"
])).to_be(true)
val old_origin = Origin(
    scheme: "https", host: "old.test", port: 443
)
expect(broker.network.cookie_store.get_header_for_origin(
    old_origin, "/next", Some(old_origin), "GET", false,
    rt_time_now_unix_micros() / 1000000
)).to_equal("first=one; second=two")

broker.pending_document_commit_url = "https://new.test/page"
broker.provisional_document_origin = "https://new.test"
expect(broker._apply_script_cookie_writes([
    "fresh=yes; Path=/"
])).to_be(true)
val new_origin = Origin(
    scheme: "https", host: "new.test", port: 443
)
expect(broker.network.cookie_store.get_header_for_origin(
    new_origin, "/next", Some(new_origin), "GET", false,
    rt_time_now_unix_micros() / 1000000
)).to_equal("fresh=yes")
expect(broker.network.cookie_store.get_header_for_origin(
    old_origin, "/next", Some(old_origin), "GET", false,
    rt_time_now_unix_micros() / 1000000
).contains("fresh=yes")).to_be(false)
```

</details>

#### partitions script cookies by the active broker document not a stale request

- Seed the broker transport with hostile requester `https://stale.test`.
- Write a `Secure; SameSite=None; Partitioned` script cookie from
  `https://app.test/page`.
- Expected: the cookie is visible only through `cookie_partition_key(app)`;
  the stale partition remains empty.

Docgen: pending — reviewed manual mirror because this isolated worktree has no
deployed self-hosted runtime.

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.document_url = "https://app.test/page"
broker.document_origin = "https://app.test"
broker.network.set_requester_origin("https://stale.test")

expect(broker._apply_script_cookie_writes([
    "part=active; Secure; SameSite=None; Partitioned; Path=/"
])).to_equal(true)
val app = Origin(scheme: "https", host: "app.test", port: 443)
val stale = Origin(scheme: "https", host: "stale.test", port: 443)
val now = rt_time_now_unix_micros() / 1000000
expect(broker.network.cookie_store.get_header_for_origin(
    app, "/", Some(app), "GET", false, now,
    cookie_partition_key(app)
)).to_equal("part=active")
expect(broker.network.cookie_store.get_header_for_origin(
    app, "/", Some(stale), "GET", false, now,
    cookie_partition_key(stale)
)).to_equal("")
```

</details>

#### validates renderer initiators before cookie writes or fetch

- var broker = HostedBrowserRendererProcess create


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.document_url = "https://trusted.test/app"
broker.document_origin = "https://trusted.test"

expect(broker._renderer_initiator_valid(request(
    "fetch", "https://trusted.test/data", credentials: "include",
    initiator_origin: "https://trusted.test"
))).to_be(true)
expect(broker._renderer_initiator_valid(request(
    "fetch", "https://trusted.test/data", credentials: "omit",
    initiator_origin: "null"
))).to_be(true)
expect(broker._renderer_initiator_valid(request(
    "fetch", "https://trusted.test/data", credentials: "omit",
    initiator_origin: "https://forged.test"
))).to_be(false)
expect(broker._renderer_initiator_valid(request(
    "fetch", "https://trusted.test/data", credentials: "include",
    initiator_origin: "null"
))).to_be(false)
expect(broker._renderer_initiator_valid(request(
    "fetch", "https://trusted.test/data", credentials: "omit",
    script_cookie_writes: ["sid=forged"],
    initiator_origin: "null"
))).to_be(false)
```

</details>

#### keeps all cookies in the broker transport only

- var broker = HostedBrowserRendererProcess create
- broker network set requester origin
- broker document origin, permit
- url: Url parse or opaque
   - Expected: finalized.error equals ``
- browser renderer decoder new
- Err
- Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
broker.document_url = "https://secure.test/app"
broker.document_origin = "https://secure.test"
broker.network.set_requester_origin(broker.document_origin)
val fetch = request(
    "fetch", "https://secure.test/data", "GET",
    "", "", "", "include"
)
val policy = hosted_browser_renderer_request_policy(
    broker.document_origin, permit(false, ""), fetch
)
expect(policy.ok).to_be(true)
val transport = FetchRequest(
    method: "GET",
    url: Url.parse_or_opaque("https://secure.test/data"),
    headers: "",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "include"
)
val finalized = broker._finalize_network(
    "fetch",
    transport,
    FetchResponse(
        status: 200,
        headers: "Set-Cookie: public=yes; Secure; Path=/\r\n" +
            "Set-Cookie: secret=token; Secure; HttpOnly; Path=/",
        body: [111u8, 107u8]
    )
)
expect(finalized.error).to_equal("")
expect(broker._write_network_response(
    fetch, policy, finalized, 0
)).to_equal("")
val decoded = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
val response = browser_renderer_network_response_decode(
    decoded.message
)
expect(response.ok).to_be(true)
expect(response.headers.lower().contains("set-cookie")).to_be(false)
expect(response.headers.contains("public=yes")).to_be(false)
expect(response.headers.contains("secret=token")).to_be(false)

match broker.network.prepare_single_hop(
    transport, broker.document_url, false
):
    Err(error): fail(error.message)
    Ok(prepared):
        expect(prepared.request.headers).to_contain(
            "Cookie: public=yes; secret=token"
        )
```

</details>

#### blocks active and passive mixed content at the trusted broker

- permit
- request
   - Expected: policy.reason equals `mixed-content-blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for kind in ["script", "style", "image", "fetch"]:
    val policy = hosted_browser_renderer_request_policy(
        "https://example.test",
        permit(false, ""),
        request(kind, "http://cdn.test/resource")
    )
    expect(policy.ok).to_be(false)
    expect(policy.reason).to_equal("mixed-content-blocked")
```

</details>

#### renders an HSTS-upgraded external PNG and blocks its mixed-content control

- Load an HTTPS document with an HTTP image under includeSubDomains HSTS
   - Artifact capture: after_step
- var broker = HostedBrowserRendererProcess create
   - Artifact capture: after_step
- BrowserHstsSnapshot create
   - Artifact capture: after_step
- var session = BrowserSession new
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: original.kind equals `image`
   - Expected: original.url equals `image_url`
- broker document origin, permit
   - Artifact capture: after_step
- browser renderer decoder new
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: transport_upgrade.status equals `307`
- Fetch and decode the upgraded PNG through the broker
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: upgraded.url equals `effective_url`
   - Expected: upgraded.redirect_count equals `20`
   - Expected: session.image_resources.len() equals `1`
-  external png pixels
   - Artifact capture: after_step
- Render the decoded image through Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: pixels.len() equals `16`
   - Expected: pixels[0] equals `0xFFCC3020u32`
   - Expected: pixels[1] equals `0xFF112233u32`
   - Expected: pixels[4] equals `0xFF445566u32`
   - Expected: pixels[5] equals `0xFF778899u32`
- Block the same mixed-content image without HSTS
   - Artifact capture: after_step
- var blocked = BrowserSession new
   - Artifact capture: after_step
- "https://source test", permit
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: blocked_policy.reason equals `mixed-content-blocked`
   - Expected: blocked.image_resources.len() equals `0`
- var csp = BrowserSession new
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: csp.image_resources.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 119 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load an HTTPS document with an HTTP image under includeSubDomains HSTS")
val image_url = "http://cdn.secure.test/pixel.png"
val image_html = (
    "<html><body style='margin:0;background:#ffffff'>" +
    "<img src='{image_url}' style='width:2px;height:2px'>" +
    "</body></html>"
)
val now_ms = rt_time_now_unix_micros() / 1000
var entries: [BrowserHstsSnapshotEntry] = []
entries.push(BrowserHstsSnapshotEntry(
    host: "secure.test",
    received_at_unix_ms: now_ms - 1000,
    expires_at_unix_ms: now_ms + 60000,
    include_subdomains: true
))
var broker = HostedBrowserRendererProcess.create(1, 4, 4)
expect(broker.load_hsts_snapshot(
    BrowserHstsSnapshot.create(entries), now_ms
)).to_equal(1)
broker.document_url = "https://source.test/page"
broker.document_origin = "https://source.test"

var session = BrowserSession.new()
session.broker_network_policy = true
expect(session.open_html(
    broker.document_url, image_html
).is_ok()).to_be(true)
session.pending_requests[0].redirect_count = 20
val original = session.take_pending_request().unwrap()
expect(original.kind).to_equal("image")
expect(original.url).to_equal(image_url)

val fetch = BrowserRendererNetworkDecodeResult(
    ok: true,
    reason: "ok",
    reply_to_request_id: 1,
    request_id: original.id,
    kind: original.kind,
    url: original.url,
    method: original.method,
    headers: original.headers,
    body: original.body,
    content_type: original.content_type,
    credentials: original.credentials,
    script_cookie_writes: [],
    status: 0,
    error: ""
)
val effective_url = broker._hsts_upgrade_url(fetch.url)
expect(effective_url).to_equal(
    "https://cdn.secure.test/pixel.png"
)
val policy = hosted_browser_renderer_request_policy(
    broker.document_origin, permit(false, ""), fetch, effective_url
)
expect(policy.ok).to_be(true)
expect(policy.mode == RequestMode.NoCors).to_be(true)
expect(broker._queue_hsts_transport_upgrade(
    fetch, policy, 20
)).to_equal("")
val transport_upgrade = browser_renderer_network_response_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(1), broker.pending_wire
    ).message
)
expect(transport_upgrade.status).to_equal(307)
expect(transport_upgrade.headers).to_contain(
    "X-Simple-Broker-Transport-Upgrade: 1"
)

step("Fetch and decode the upgraded PNG through the broker")
val upgraded = _commit_broker_image_response(
    session, original, transport_upgrade
)
expect(upgraded.url).to_equal(effective_url)
expect(upgraded.redirect_count).to_equal(20)
expect(session.image_resources.len()).to_equal(1)
expect(session.image_resources[0].pixels).to_equal(
    _external_png_pixels()
)

step("Render the decoded image through Draw IR")
val pixels = _render_image_resource_draw_ir(session)
expect(pixels.len()).to_equal(16)
expect(pixels[0]).to_equal(0xFFCC3020u32)
expect(pixels[1]).to_equal(0xFF112233u32)
expect(pixels[4]).to_equal(0xFF445566u32)
expect(pixels[5]).to_equal(0xFF778899u32)

step("Block the same mixed-content image without HSTS")
var blocked = BrowserSession.new()
blocked.broker_network_policy = true
expect(blocked.open_html(
    "https://source.test/page", image_html
).is_ok()).to_be(true)
val blocked_request = blocked.take_pending_request().unwrap()
val blocked_policy = hosted_browser_renderer_request_policy(
    "https://source.test", permit(false, ""), fetch
)
expect(blocked_policy.ok).to_be(false)
expect(blocked_policy.reason).to_equal("mixed-content-blocked")
expect(blocked.commit_network_response(BrowserResponse.create(
    blocked_request.id, "image", blocked_request.url, 0, "", "",
    blocked_policy.reason
)).is_ok()).to_be(true)
expect(blocked.image_resources.len()).to_equal(0)

var csp = BrowserSession.new()
expect(csp.begin_network_navigation(
    "https://source.test/page", "GET", "", "", ""
).is_ok()).to_be(true)
val csp_document = csp.take_pending_request().unwrap()
expect(csp.commit_network_response(BrowserResponse.create(
    csp_document.id, "document", csp_document.url, 200,
    "Content-Security-Policy: img-src 'none'", image_html, ""
)).is_ok()).to_be(true)
expect(csp.take_pending_request()).to_be_nil()
expect(csp.image_resources.len()).to_equal(0)
expect(csp.warnings.join("|")).to_contain("CSP blocked image")
```

</details>

#### loads brokered CSS background images and renders their exact pixels

- Load inline and linked CSS background images through the broker
- "background-image:url
- var broker = HostedBrowserRendererProcess create
- BrowserHstsSnapshot create
- var session = BrowserSession new
   - Expected: style.kind equals `style`
- " unused{background-image:url
   - Expected: original.kind equals `image`
   - Expected: original.url equals `image_url`
- broker document origin, permit
- browser renderer decoder new
   - Expected: transport_upgrade.status equals `307`
- session, original, transport upgrade,  background png hex
   - Expected: upgraded.redirect_count equals `20`
   - Expected: linked.kind equals `image`
   - Expected: linked.url equals `linked_image_url`
- broker document origin, permit
-  commit png response
   - Expected: session.image_resources.len() equals `2`
- Apply background size position repeat origin and clip
- Render the background image behind element content
   - Expected: pixels.len() equals `64`
   - Expected: pixels[1 * 8 + 1] equals `0xFF0000FFu32`
   - Expected: pixels[2 * 8 + 1] equals `0xFF80007Fu32`
   - Expected: pixels[2 * 8 + 2] equals `0xFF0000FFu32`
   - Expected: pixels[2 * 8 + 3] equals `0xFF00FF00u32`
   - Expected: pixels[3 * 8 + 1] equals `0xFF0000FFu32`
   - Expected: pixels[3 * 8 + 2] equals `0xFF80007Fu32`
   - Expected: pixels[4 * 8 + 1] equals `0xFF0000FFu32`
   - Expected: pixels[2 * 8 + 7] equals `0xFF123456u32`
- Block background images denied by CSP or mixed-content policy
- "<div style='background-image:url
- var blocked = BrowserSession new
- broker document origin, permit
   - Expected: blocked_policy.reason equals `mixed-content-blocked`
   - Expected: blocked.image_resources.len() equals `0`
- var csp = BrowserSession new
   - Expected: csp.image_resources.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 166 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load inline and linked CSS background images through the broker")
val image_url = "http://cdn.secure.test/tile.png"
val linked_image_url = "https://assets.test/unused.png"
val html = (
    "<html style='margin:0;padding:0'><head>" +
    "<link rel='stylesheet' href='https://styles.test/theme.css'>" +
    "</head><body style='margin:0;padding:0'>" +
    "<div id='tile' style='width:4px;height:4px;padding:1px;" +
    "border:1px solid #123456;background-color:#0000ff;" +
    "background-image:url({image_url});background-repeat:repeat-x;" +
    "background-size:2px 2px;background-position:1px 0px;" +
    "background-origin:content-box;background-clip:border-box'>" +
    "<div style='width:1px;height:1px;margin-left:1px;" +
    "background:#00ff00'></div></div></body></html>"
)
val now_ms = rt_time_now_unix_micros() / 1000
var entries: [BrowserHstsSnapshotEntry] = []
entries.push(BrowserHstsSnapshotEntry(
    host: "secure.test",
    received_at_unix_ms: now_ms - 1000,
    expires_at_unix_ms: now_ms + 60000,
    include_subdomains: true
))
var broker = HostedBrowserRendererProcess.create(1, 8, 8)
expect(broker.load_hsts_snapshot(
    BrowserHstsSnapshot.create(entries), now_ms
)).to_equal(1)
broker.document_url = "https://source.test/page"
broker.document_origin = "https://source.test"

var session = BrowserSession.new()
session.broker_network_policy = true
expect(session.open_html(broker.document_url, html).is_ok()).to_be(true)
val style = session.take_pending_request().unwrap()
expect(style.kind).to_equal("style")
expect(session.commit_network_response(BrowserResponse.create(
    style.id, style.kind, style.url, 200, "Content-Type: text/css",
    ".unused{background-image:url({linked_image_url})}", ""
)).is_ok()).to_be(true)

session.pending_requests[0].redirect_count = 20
val original = session.take_pending_request().unwrap()
expect(original.kind).to_equal("image")
expect(original.url).to_equal(image_url)
val fetch = BrowserRendererNetworkDecodeResult(
    ok: true,
    reason: "ok",
    reply_to_request_id: 1,
    request_id: original.id,
    kind: original.kind,
    url: original.url,
    method: original.method,
    headers: original.headers,
    body: original.body,
    content_type: original.content_type,
    credentials: original.credentials,
    script_cookie_writes: [],
    status: 0,
    error: ""
)
val effective_url = broker._hsts_upgrade_url(fetch.url)
val policy = hosted_browser_renderer_request_policy(
    broker.document_origin, permit(false, ""), fetch, effective_url
)
expect(policy.ok).to_be(true)
expect(broker._queue_hsts_transport_upgrade(
    fetch, policy, 20
)).to_equal("")
val transport_upgrade = browser_renderer_network_response_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(1), broker.pending_wire
    ).message
)
expect(transport_upgrade.status).to_equal(307)
val upgraded = _commit_broker_image_response(
    session, original, transport_upgrade, _background_png_hex()
)
expect(upgraded.redirect_count).to_equal(20)

val linked = session.take_pending_request().unwrap()
expect(linked.kind).to_equal("image")
expect(linked.url).to_equal(linked_image_url)
val linked_fetch = BrowserRendererNetworkDecodeResult(
    ok: true,
    reason: "ok",
    reply_to_request_id: 1,
    request_id: linked.id,
    kind: linked.kind,
    url: linked.url,
    method: linked.method,
    headers: linked.headers,
    body: linked.body,
    content_type: linked.content_type,
    credentials: linked.credentials,
    script_cookie_writes: [],
    status: 0,
    error: ""
)
expect(hosted_browser_renderer_request_policy(
    broker.document_origin, permit(false, ""), linked_fetch
).ok).to_be(true)
_commit_png_response(session, linked, _background_png_hex())
expect(session.image_resources.len()).to_equal(2)

step("Apply background size position repeat origin and clip")
step("Render the background image behind element content")
val pixels = _render_background_image_pixels(session)
expect(pixels.len()).to_equal(64)
expect(pixels[1 * 8 + 1]).to_equal(0xFF0000FFu32)
expect(pixels[2 * 8 + 1]).to_equal(0xFF80007Fu32)
expect(pixels[2 * 8 + 2]).to_equal(0xFF0000FFu32)
expect(pixels[2 * 8 + 3]).to_equal(0xFF00FF00u32)
expect(pixels[3 * 8 + 1]).to_equal(0xFF0000FFu32)
expect(pixels[3 * 8 + 2]).to_equal(0xFF80007Fu32)
expect(pixels[4 * 8 + 1]).to_equal(0xFF0000FFu32)
expect(pixels[2 * 8 + 7]).to_equal(0xFF123456u32)

step("Block background images denied by CSP or mixed-content policy")
val blocked_html = (
    "<div style='background-image:url({image_url})'></div>"
)
var blocked = BrowserSession.new()
blocked.broker_network_policy = true
expect(blocked.open_html(
    broker.document_url, blocked_html
).is_ok()).to_be(true)
val blocked_request = blocked.take_pending_request().unwrap()
val blocked_fetch = BrowserRendererNetworkDecodeResult(
    ok: true,
    reason: "ok",
    reply_to_request_id: 1,
    request_id: blocked_request.id,
    kind: blocked_request.kind,
    url: blocked_request.url,
    method: blocked_request.method,
    headers: blocked_request.headers,
    body: blocked_request.body,
    content_type: blocked_request.content_type,
    credentials: blocked_request.credentials,
    script_cookie_writes: [],
    status: 0,
    error: ""
)
val blocked_policy = hosted_browser_renderer_request_policy(
    broker.document_origin, permit(false, ""), blocked_fetch
)
expect(blocked_policy.ok).to_be(false)
expect(blocked_policy.reason).to_equal("mixed-content-blocked")
expect(blocked.commit_network_response(BrowserResponse.create(
    blocked_request.id, blocked_request.kind, blocked_request.url,
    0, "", "", blocked_policy.reason
)).is_ok()).to_be(true)
expect(blocked.image_resources.len()).to_equal(0)

var csp = BrowserSession.new()
expect(csp.begin_network_navigation(
    broker.document_url, "GET", "", "", ""
).is_ok()).to_be(true)
val csp_document = csp.take_pending_request().unwrap()
expect(csp.commit_network_response(BrowserResponse.create(
    csp_document.id, "document", csp_document.url, 200,
    "Content-Security-Policy: img-src 'none'", blocked_html, ""
)).is_ok()).to_be(true)
expect(csp.take_pending_request()).to_be_nil()
expect(csp.image_resources.len()).to_equal(0)
expect(csp.warnings.join("|")).to_contain("CSP blocked image")
```

</details>

#### loads ordinary cross-origin images without exposing a CORS fetch

- permit
- request
   - Expected: image.credentials equals `include`
   - Expected: image.sanitized_headers equals ``
- permit
- request


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = hosted_browser_renderer_request_policy(
    "https://example.test",
    permit(false, ""),
    request("image", "https://cdn.test/pixel.png")
)
expect(image.ok).to_be(true)
expect(image.mode == RequestMode.NoCors).to_be(true)
expect(image.credentials).to_equal("include")
expect(image.sanitized_headers).to_equal("")

val script = hosted_browser_renderer_request_policy(
    "https://example.test",
    permit(false, ""),
    request("script", "https://cdn.test/app.js")
)
expect(script.ok).to_be(true)
expect(script.mode == RequestMode.Cors).to_be(true)
expect(script.sanitized_headers).to_equal(
    "Origin: https://example.test"
)
```

</details>

#### accepts only exact broker-owned HSTS transport upgrades

- permit
- request
- permit
- request
   - Expected: forged_policy.reason equals `invalid-request-url`
- Logger new
- Err
- fail
- Ok
- origin, "/", Some
- rt time now unix micros


<details>
<summary>Executable SSpec</summary>

Runnable source: 93 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hosted_browser_hsts_upgrade_valid(
    "http://secure.test/app.js",
    "https://secure.test/app.js"
)).to_be(true)
expect(hosted_browser_hsts_upgrade_valid(
    "http://secure.test:80/app.js",
    "https://secure.test:443/app.js"
)).to_be(true)
expect(hosted_browser_hsts_upgrade_valid(
    "http://secure.test:8080/app.js?x=1",
    "https://secure.test:8080/app.js?x=1"
)).to_be(true)
for forged in [
    "https://other.test/app.js",
    "https://secure.test/other.js",
    "https://secure.test/app.js?x=2",
    "https://secure.test:444/app.js"
]:
    expect(hosted_browser_hsts_upgrade_valid(
        "http://secure.test/app.js?x=1", forged
    )).to_be(false)

val upgraded = hosted_browser_renderer_request_policy(
    "https://secure.test",
    permit(false, ""),
    request("script", "http://secure.test/app.js"),
    "https://secure.test/app.js"
)
expect(upgraded.ok).to_be(true)
expect(upgraded.mode == RequestMode.SameOrigin).to_be(true)
expect(upgraded.canonical_url).to_equal(
    "https://secure.test/app.js"
)
val forged_policy = hosted_browser_renderer_request_policy(
    "https://secure.test",
    permit(false, ""),
    request("script", "http://secure.test/app.js"),
    "https://other.test/app.js"
)
expect(forged_policy.ok).to_be(false)
expect(forged_policy.reason).to_equal("invalid-request-url")
expect(hosted_browser_remove_response_header(
    "Content-Type: text/css\r\n" +
    "Strict-Transport-Security: max-age=60\r\n" +
    "Cache-Control: no-store",
    "strict-transport-security"
)).to_equal(
    "Content-Type: text/css\r\nCache-Control: no-store"
)
expect(hosted_browser_cors_response_headers(
    "Content-Type: text/plain\r\n" +
    "Set-Cookie: stolen=yes\r\n" +
    "X-Visible: yes\r\nX-Secret: no\r\n" +
    "Location: https://secure.test/next\r\n" +
    "Access-Control-Expose-Headers: X-Visible",
    false
)).to_equal(
    "Content-Type: text/plain\r\nX-Visible: yes"
)
expect(hosted_browser_cors_response_headers(
    "Set-Cookie2: stolen=yes\r\n" +
    "Location: https://secure.test/next",
    true
)).to_equal("Location: https://secure.test/next")
expect(hosted_browser_cors_response_headers(
    "X-Secret: no\r\nAccess-Control-Expose-Headers: *",
    false,
    "include"
)).to_equal("")
var credential_free = FetchEngine.new_for_origin(
    Logger.new("cors-cookie-test", BrowserLogLevel.Error),
    "https://secure.test"
)
match credential_free.finalize_single_hop(
    fetch_request(
        "https://secure.test/data", RequestMode.SameOrigin
    ),
    FetchResponse(
        status: 200,
        headers: "Set-Cookie: stolen=yes; Path=/",
        body: []
    )
):
    Err(error):
        fail(error.message)
    Ok(_):
        val origin = Origin(
            scheme: "https", host: "secure.test", port: 443
        )
        expect(credential_free.cookie_store.get_header_for_origin(
            origin, "/", Some(origin), "GET", false,
            rt_time_now_unix_micros() / 1000000
        )).to_equal("")
```

</details>

#### round trips broker HSTS upgrades without spending redirect state

- var broker = HostedBrowserRendererProcess create
- BrowserHstsSnapshot create
- permit
   - Expected: broker.network_job_handle equals `0`
- browser renderer decoder new
   - Expected: response.url equals `http://secure.test/app.js`
   - Expected: response.status equals `307`
- BrowserHstsSnapshot create
- var document = BrowserSession new
- fail
- Some
- fail
- Some
   - Expected: next.url equals `https://secure.test/form`
   - Expected: next.redirect_count equals `20`
   - Expected: next.method equals `POST`
   - Expected: next.body equals `name=value`
   - Expected: next.credentials equals `include`
- var unmarked = BrowserSession new
- fail
- Some
- var session = BrowserSession new
- session pending requests push
- fail
- Some
- Err
- fail
- Ok
- fail
- Some
   - Expected: next.redirect_count equals `20`
   - Expected: next.method equals `method`
   - Expected: next.body equals `body`
   - Expected: next.headers equals ``
- url: Url parse or opaque
- Err
- Ok
- Err
- Ok
- var blocked = BrowserSession new
- Err
- fail
- Ok
- fail
- Some
- Err
- fail
- Ok
- Some
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 274 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val now_ms = rt_time_now_unix_micros() / 1000
var entries: [BrowserHstsSnapshotEntry] = []
entries.push(BrowserHstsSnapshotEntry(
    host: "secure.test",
    received_at_unix_ms: now_ms - 1000,
    expires_at_unix_ms: now_ms + 60000,
    include_subdomains: true
))
var broker = HostedBrowserRendererProcess.create(1, 640, 480)
expect(broker.load_hsts_snapshot(
    BrowserHstsSnapshot.create(entries), now_ms
)).to_equal(1)
val fetch = request("script", "http://secure.test/app.js")
val effective_url = broker._hsts_upgrade_url(fetch.url)
val policy = hosted_browser_renderer_request_policy(
    "https://secure.test",
    permit(false, ""),
    fetch,
    effective_url
)
expect(policy.ok).to_be(true)
expect(broker._queue_hsts_transport_upgrade(
    fetch, policy, 20
)).to_equal("")
expect(broker.network_job_handle).to_equal(0)
val decoded = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(1), broker.pending_wire
)
val response = browser_renderer_network_response_decode(
    decoded.message
)
expect(response.ok).to_be(true)
expect(response.url).to_equal("http://secure.test/app.js")
expect(response.status).to_equal(307)
expect(response.headers).to_contain(
    "Location: https://secure.test/app.js"
)
expect(response.headers).to_contain(
    "X-Simple-Broker-Transport-Upgrade: 1"
)

var renderer_document = HostedBrowserRendererProcess.create(
    2, 640, 480
)
expect(renderer_document.load_hsts_snapshot(
    BrowserHstsSnapshot.create(entries), now_ms
)).to_equal(1)
renderer_document.document_url = "https://source.test/page"
renderer_document.document_origin = "https://source.test"
renderer_document.document_csp_policy = "default-src *"
renderer_document.document_csp_ready = true
val renderer_request = request(
    "document", "http://secure.test/page"
)
expect(renderer_document.authorize_renderer_navigation(
    renderer_request
)).to_be(true)
expect(renderer_document._queue_hsts_transport_upgrade(
    renderer_request,
    HostedBrowserRequestPolicy(
        ok: true,
        reason: "ok",
        mode: RequestMode.Navigate,
        credentials: "include",
        canonical_url: "https://secure.test/page",
        sanitized_headers: "",
        consumes_navigation: true
    ),
    -1
)).to_equal("")
expect(renderer_document.navigation_permit.url).to_equal(
    "https://secure.test/page"
)
expect(renderer_document.navigation_permit.redirect_count).to_equal(
    0
)

var document = BrowserSession.new()
document.broker_network_policy = true
expect(document.begin_network_navigation(
    "http://secure.test/form", "POST", "", "name=value",
    "application/x-www-form-urlencoded"
).is_ok()).to_be(true)
document.pending_requests[0].redirect_count = 20
match document.take_pending_request():
    nil:
        fail("Expected broker-bound document request")
    Some(original):
        expect(document.commit_network_response(
            BrowserResponse.create(
                original.id, "document", original.url, 307,
                "Location: https://secure.test/form\r\n" +
                "X-Simple-Broker-Transport-Upgrade: 1",
                "", ""
            )
        ).is_ok()).to_be(true)
match document.take_pending_request():
    nil:
        fail("Expected upgraded document request")
    Some(next):
        expect(next.url).to_equal("https://secure.test/form")
        expect(next.redirect_count).to_equal(20)
        expect(next.method).to_equal("POST")
        expect(next.body).to_equal("name=value")
        expect(next.site_for_cookies_url).to_equal(
            "http://secure.test/form"
        )
        expect(next.credentials).to_equal("include")

var unmarked = BrowserSession.new()
unmarked.broker_network_policy = true
expect(unmarked.begin_network_navigation(
    "http://secure.test/limit", "GET", "", "", ""
).is_ok()).to_be(true)
unmarked.pending_requests[0].redirect_count = 20
match unmarked.take_pending_request():
    nil:
        fail("Expected limited document request")
    Some(original):
        expect(unmarked.commit_network_response(
            BrowserResponse.create(
                original.id, "document", original.url, 307,
                "Location: https://secure.test/limit", "", ""
            )
        ).is_err()).to_be(true)
expect(unmarked.has_pending_requests()).to_be(false)

for kind in ["style", "script", "module", "wasm", "fetch"]:
    var session = BrowserSession.new()
    session.broker_network_policy = true
    session.document_url = "https://secure.test/"
    session.content_security_policy = (
        "style-src 'self'; script-src 'self'; connect-src 'self'"
    )
    if kind == "fetch":
        session.apply_set_cookie_header(
            "secure_token=secret; Secure; Path=/",
            "https://secure.test/"
        )
    val method = if kind == "fetch": "POST" else: "GET"
    val headers = if kind == "fetch":
        "X-Test: retained"
    else:
        ""
    val body = if kind == "fetch": "payload" else: ""
    var pending = BrowserRequest.create(
        "request-{kind}", kind,
        "http://secure.test/resource", method, headers, body,
        if kind == "fetch": "text/plain" else: ""
    )
    pending.redirect_count = 20
    session.pending_requests.push(pending)
    val emitted = session.take_pending_request()
    match emitted:
        nil:
            fail("Expected broker-bound HTTP candidate")
        Some(original):
            val committed = session.commit_network_response(
                BrowserResponse.create(
                    original.id, kind, original.url, 307,
                    "Location: https://secure.test/resource\r\n" +
                    "X-Simple-Broker-Transport-Upgrade: 1",
                    "", ""
                )
            )
            match committed:
                Err(reason):
                    fail(reason)
                Ok(done):
                    expect(done).to_be(true)
    val redirected = session.take_pending_request()
    match redirected:
        nil:
            fail("Expected correlated HTTPS request")
        Some(next):
            expect(next.url).to_equal(
                "https://secure.test/resource"
            )
            expect(next.redirect_count).to_equal(20)
            expect(next.method).to_equal(method)
            expect(next.body).to_equal(body)
            if kind == "fetch":
                expect(next.headers).to_contain("X-Test: retained")
                expect(next.headers.contains("Cookie:")).to_equal(
                    false
                )
            else:
                expect(next.headers).to_equal("")

var redirect_broker = HostedBrowserRendererProcess.create(
    1, 640, 480
)
redirect_broker.document_url = "https://source.test/page"
redirect_broker.document_origin = "https://source.test"
expect(redirect_broker.network.store_script_cookies(
    ["source=one; SameSite=None; Secure; Path=/"],
    "https://source.test/page"
)).to_equal(true)
expect(redirect_broker.network.store_script_cookies(
    ["destination=two; SameSite=None; Secure; Path=/"],
    "https://destination.test/page"
)).to_equal(true)
redirect_broker.network.set_requester_origin(
    redirect_broker.document_origin
)
val redirect_request = FetchRequest(
    method: "GET",
    url: Url.parse_or_opaque("https://destination.test/resource"),
    headers: "",
    body: [],
    mode: RequestMode.Cors,
    credentials: "include"
)
match redirect_broker.network.prepare_single_hop(
    redirect_request, redirect_broker.document_url, false
):
    Err(error): fail(error.message)
    Ok(prepared):
        expect(prepared.request.headers).to_contain(
            "Cookie: destination=two"
        )
        expect(prepared.request.headers.contains("source=one")).to_equal(
            false
        )
val same_origin_redirect = FetchRequest(
    method: "GET",
    url: redirect_request.url,
    headers: "",
    body: [],
    mode: RequestMode.Cors,
    credentials: "same-origin"
)
match redirect_broker.network.prepare_single_hop(
    same_origin_redirect, redirect_broker.document_url, false
):
    Err(error): fail(error.message)
    Ok(prepared):
        expect(prepared.request.headers.contains("Cookie:")).to_equal(
            false
        )

var blocked = BrowserSession.new()
blocked.broker_network_policy = true
match blocked.begin_network_navigation(
    "http://plain.test/", "GET", "", "", ""
):
    Err(reason):
        fail(reason)
    Ok(done):
        expect(done).to_be(true)
val document_request = blocked.take_pending_request()
match document_request:
    nil:
        fail("Expected document request")
    Some(document):
        match blocked.commit_network_response(
            BrowserResponse.create(
                document.id, "document", document.url, 200,
                "Content-Security-Policy: script-src 'none'",
                "<script src='http://plain.test/blocked.js'></script>",
                ""
            )
        ):
            Err(reason):
                fail(reason)
            Ok(done):
                expect(done).to_be(true)
match blocked.take_pending_request():
    nil:
        expect(blocked.warnings.join("\n")).to_contain(
            "CSP blocked script"
        )
    Some(unexpected):
        fail("CSP bypassed for {unexpected.url}")
```

</details>

#### denies cross-origin requests that need an unbrokered preflight

- permit


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = hosted_browser_renderer_request_policy(
    "https://example.test",
    permit(false, ""),
    request(
        "fetch",
        "https://api.test/update",
        "POST",
        "",
        "value",
        "text/plain"
    )
)
expect(policy.ok).to_be(false)
expect(policy.reason).to_equal(
    "cross-origin-preflight-unavailable"
)
```

</details>

#### requires a fresh renderer generation before a cross-site document

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.site_lock equals `https://example.test`
   - Expected: broker.site_swap_site equals `https://victim.test`
   - Expected: broker.network_job_handle equals `0`
   - Expected: broker.pending_wire equals ``
   - Expected: broker.provisional_document_origin equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(7, 640, 480)
expect(broker._document_site_swap_required(
    "https://app.example.test/start"
)).to_be(false)
expect(broker._document_site_swap_required(
    "https://account.victim.test/"
)).to_be(true)
expect(broker.site_lock).to_equal("https://example.test")
expect(broker.site_swap_pending).to_be(true)
expect(broker.site_swap_site).to_equal("https://victim.test")
expect(broker.network_job_handle).to_equal(0)
expect(broker.pending_wire).to_equal("")
expect(broker.provisional_document_origin).to_equal("")
```

</details>

#### retains one generation for same schemeful-site navigation

- var broker = HostedBrowserRendererProcess create
   - Expected: broker.generation equals `7`
   - Expected: broker.site_lock equals `https://example.test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = HostedBrowserRendererProcess.create(7, 640, 480)
expect(broker._document_site_swap_required(
    "https://app.example.test/start"
)).to_be(false)
expect(broker._document_site_swap_required(
    "https://cdn.example.test:8443/asset"
)).to_be(false)
expect(broker.generation).to_equal(7)
expect(broker.site_lock).to_equal("https://example.test")
expect(broker.site_swap_pending).to_be(false)
```

</details>

#### withholds a cross-site redirect body and credentials from the old child

- var broker = HostedBrowserRendererProcess create
- broker navigation permit = permit
- url: Url parse or opaque
   - Expected: reason equals `HOSTED_BROWSER_SITE_SWAP_REQUIRED`
   - Expected: broker.navigation_permit.url equals `target_url`
   - Expected: broker.site_swap_site equals `https://victim.test`
   - Expected: broker.pending_wire equals ``
   - Expected: broker.network_job_handle equals `0`
   - Expected: broker.provisional_document_origin equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_url = "https://app.example.test/start"
val target_url = "https://account.victim.test/private"
var broker = HostedBrowserRendererProcess.create(7, 640, 480)
expect(broker._document_site_swap_required(source_url)).to_be(false)
broker.document_url = source_url
broker.document_origin = "https://app.example.test"
broker.navigation_permit = permit(true, source_url)
val response = broker._finalize_network(
    "document",
    FetchRequest(
        url: Url.parse_or_opaque(source_url),
        method: "GET", headers: "", body: [],
        mode: RequestMode.Navigate, credentials: "include"
    ),
    FetchResponse(
        status: 302,
        headers: "Location: {target_url}",
        body: [115u8, 101u8, 99u8, 114u8, 101u8, 116u8]
    )
)
val reason = broker._write_network_response(
    request(
        "document", source_url, "GET", "", "", "",
        "include", [], "https://app.example.test"
    ),
    HostedBrowserRequestPolicy(
        ok: true, reason: "ok", mode: RequestMode.Navigate,
        credentials: "include", canonical_url: source_url,
        sanitized_headers: "", consumes_navigation: true
    ),
    response,
    0
)
expect(reason).to_equal(HOSTED_BROWSER_SITE_SWAP_REQUIRED)
expect(broker.navigation_permit.url).to_equal(target_url)
expect(broker.site_swap_site).to_equal("https://victim.test")
expect(broker.pending_wire).to_equal("")
expect(broker.network_job_handle).to_equal(0)
expect(broker.provisional_document_origin).to_equal("")
```

</details>

#### rejects old-generation SBRQ4 after a site swap

- browser renderer decoder new
   - Expected: stale.status equals `violation`
   - Expected: stale.decoder.error equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_request = browser_renderer_fetch_request_encode(
    7, 2, 1, "fetch-1", "fetch",
    "https://account.victim.test/private", "GET", "", "", "",
    "include", [], "https://account.victim.test"
)
expect(old_request.ok).to_be(true)
val stale = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(8), old_request.wire
)
expect(stale.status).to_equal("violation")
expect(stale.decoder.error).to_equal("stale-generation")
```

</details>

#### binds a bookmark title to generation reply and canonical URL

- var renderer = HostedBrowserRendererProcess create
   - Expected: renderer.bookmark_stored_title() equals `Bound title`
   - Expected: renderer.bookmark_stored_title() equals ``
   - Expected: renderer.bookmark_stored_title() equals ``
   - Expected: renderer.bookmark_stored_title() equals ``
   - Expected: renderer.bookmark_stored_title() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = HostedBrowserRendererProcess.create(7, 64, 48)
renderer.expected_reply_to_request_id = 41
renderer.document_url = "https://title.test/"
renderer.document_title = "Bound title"
renderer.document_title_url = "https://title.test/"
renderer.document_title_generation = 7
renderer.document_title_reply_to_request_id = 41
expect(renderer.bookmark_stored_title()).to_equal("Bound title")

renderer.document_title_generation = 6
expect(renderer.bookmark_stored_title()).to_equal("")
renderer.document_title_generation = 7
renderer.document_title_reply_to_request_id = 40
expect(renderer.bookmark_stored_title()).to_equal("")
renderer.document_title_reply_to_request_id = 41
renderer.document_title_url = "https://other.test/"
expect(renderer.bookmark_stored_title()).to_equal("")
renderer.document_title_url = renderer.document_url
expect(renderer.close()).to_be(true)
expect(renderer.bookmark_stored_title()).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>
