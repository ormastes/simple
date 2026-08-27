# Production Simple Browser Security Envelope

> Treats pages, scripts, URLs, redirects, responses, and renderer messages as

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production Simple Browser Security Envelope

Treats pages, scripts, URLs, redirects, responses, and renderer messages as

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/simple_web_browser_engine_security_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Treats pages, scripts, URLs, redirects, responses, and renderer messages as
hostile. Proves HTTPS, origin/storage policy, bounded IPC, and an OS-sandboxed
renderer without ambient host capabilities.

## Scenarios

### Production Simple browser security envelope

#### should isolate positive-owner rendering and input behind exact-window frames

**Scenario capture:** protocol after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-010..019
```

</details>

#### should persist shared preloaded HSTS without trusting generic responses

- should persist shared preloaded HSTS without trusting generic responses
   - Protocol capture: after_step
- Navigate through verified HTTPS
   - Protocol capture: after_step
- Share secondary-window HSTS through the existing registry
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: untrusted.error equals ``
   - Expected: registry.hsts_revision() equals `0`
- Persist shared HSTS before every browser window closes
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: restarted.hsts_revision() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 99 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should persist shared preloaded HSTS without trusting generic responses")
step("Navigate through verified HTTPS")
val now_ms: i64 = 100000
val artifact = _production_browser_artifact()
var initial_entries: [BrowserHstsSnapshotEntry] = []
initial_entries.push(BrowserHstsSnapshotEntry(
    host: "preload.test",
    received_at_unix_ms: now_ms,
    expires_at_unix_ms: now_ms + 60000,
    include_subdomains: true
))
var registry = HostedBrowserRendererRegistry.create(
    artifact, "https://example.com/"
)
expect(registry.load_hsts_snapshot(
    BrowserHstsSnapshot.create(initial_entries), now_ms
)).to_equal(1)
expect(registry.hsts_upgrade_url(
    "http://sub.preload.test/path"
)).to_equal("https://sub.preload.test/path")

step("Share secondary-window HSTS through the existing registry")
var secondary = HostedBrowserRendererProcess.create(42, 64, 48)
expect(secondary.load_hsts_snapshot(
    registry.hsts_snapshot(now_ms), now_ms
)).to_equal(1)
val untrusted = secondary._finalize_network(
    "document",
    FetchRequest(
        url: Url.parse_or_opaque(
            "https://secondary.test/account"
        ),
        method: "GET",
        headers: "",
        body: [],
        mode: RequestMode.Navigate,
        credentials: "include"
    ),
    FetchResponse(
        status: 200,
        headers: "Strict-Transport-Security: max-age=60",
        body: []
    )
)
expect(untrusted.error).to_equal("")
expect(secondary.hsts_dirty).to_be(false)
expect(secondary.hsts_snapshot(
    now_ms + 1000
).entries.len()).to_equal(1)
expect(registry.hsts_upgrade_url(
    "http://secondary.test/account"
)).to_equal("http://secondary.test/account")
expect(registry.hsts_dirty()).to_be(false)
expect(registry.hsts_revision()).to_equal(0)

step("Persist shared HSTS before every browser window closes")
var profile = match BrowserProfileStore.memory():
    Err(error):
        fail("memory profile creation failed: {error.message()}")
    Ok(opened):
        opened
match profile.save_hsts(
    registry.hsts_snapshot(now_ms + 1000), now_ms + 1000
):
    Err(error):
        fail("HSTS save failed: {error.message()}")
    Ok(_):
        pass_dn("preloaded HSTS snapshot persisted")
expect(registry.hsts_dirty()).to_be(false)
val persisted = match profile.load_hsts(now_ms + 2000):
    Err(error):
        fail("HSTS reload failed: {error.message()}")
    Ok(snapshot):
        snapshot
var restarted = HostedBrowserRendererRegistry.create(
    artifact, "https://example.com/"
)
expect(restarted.load_hsts_snapshot(
    persisted, now_ms + 2000
)).to_equal(1)
expect(restarted.hsts_upgrade_url(
    "http://sub.preload.test/account"
)).to_equal("https://sub.preload.test/account")
match profile.close():
    Err(error):
        fail("memory profile close failed: {error.message()}")
    Ok(_):
        pass_dn("memory profile closed")
expect(restarted.hsts_dirty()).to_be(false)
expect(restarted.hsts_revision()).to_equal(0)
expect(restarted.ensure(
    84, "<div>secondary</div>", 64, 48, 0, now_ms + 2000
)).to_equal("none")
expect(restarted.contains(84)).to_be(true)
expect(restarted.remove_window(84)).to_be(true)
expect(restarted.contains(84)).to_be(false)
expect(restarted.hsts_dirty()).to_be(false)
expect(restarted.close()).to_be(true)
```

</details>

#### should learn HSTS only from the completed platform HTTPS job

- should learn HSTS only from the completed platform HTTPS job
   - Protocol capture: after_step
- Reject generic mock and ordinary HTTPS finalization
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: mock.status equals `200`
   - Expected: mock.error equals ``
- Reject failed TLS without response or policy state
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: broker.hsts_snapshot(100000).entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should learn HSTS only from the completed platform HTTPS job")
_two_origin_https_fixture()
step("Reject generic mock and ordinary HTTPS finalization")
var broker = HostedBrowserRendererProcess.create(43, 64, 48)
val mock = broker._finalize_network(
    "document",
    FetchRequest(
        url: Url.parse_or_opaque("https://mock.test/"),
        method: "GET", headers: "", body: [],
        mode: RequestMode.Navigate, credentials: "include"
    ),
    FetchResponse(
        status: 200,
        headers: "Strict-Transport-Security: max-age=60", body: []
    )
)
expect(mock.status).to_equal(200)
expect(mock.error).to_equal("")
expect(broker.hsts_dirty).to_be(false)
expect(broker._hsts_upgrade_url(
    "http://mock.test/next"
)).to_equal("http://mock.test/next")

step("Reject failed TLS without response or policy state")
expect(broker.hsts_snapshot(100000).entries.len()).to_equal(0)
fail(
    "REQ-WEB-BROWSER-011: trusted HTTPS learn/save/clean and " +
    "invalid TLS failure/retry evidence not implemented"
)
```

</details>

#### should validate opaque renderer initiators before cookie writes

- should validate opaque renderer initiators before cookie writes


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate opaque renderer initiators before cookie writes")
var broker = HostedBrowserRendererProcess.create(44, 64, 48)
broker.document_url = "https://trusted.test/app"
broker.document_origin = "https://trusted.test"

expect(broker._renderer_initiator_valid(
    _broker_initiator_request(
        "https://trusted.test", "include", ["sid=trusted"]
    )
)).to_be(true)
expect(broker._renderer_initiator_valid(
    _broker_initiator_request("null", "omit", [])
)).to_be(true)
expect(broker._renderer_initiator_valid(
    _broker_initiator_request("https://forged.test", "omit", [])
)).to_be(false)
expect(broker._renderer_initiator_valid(
    _broker_initiator_request("null", "include", [])
)).to_be(false)
expect(broker._renderer_initiator_valid(
    _broker_initiator_request("null", "omit", ["sid=forged"])
)).to_be(false)
```

</details>

#### should replace a forged CORS Origin with the requester origin

- should replace a forged CORS Origin with the requester origin
   - Protocol capture: after_step
- Construct browser-owned CORS request identity
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should replace a forged CORS Origin with the requester origin")
step("Construct browser-owned CORS request identity")
var fetch = FetchEngine.new_for_origin(
    Logger.new("cors-origin", BrowserLogLevel.Error),
    "https://app.test"
)
val request = FetchRequest(
    url: Url.parse_or_opaque("https://api.test/data"),
    method: "GET",
    headers: (
        "Origin: https://attacker.test\r\n" +
        "Accept: text/plain\r\n"
    ),
    body: [],
    mode: RequestMode.Cors,
    credentials: "omit"
)
match fetch.prepare_single_hop(request):
    Err(error):
        fail(error.message)
    Ok(prepared):
        expect(prepared.request.headers).to_equal(
            "Accept: text/plain\r\n" +
            "Origin: https://app.test\r\n"
        )
        expect(prepared.request.headers.contains(
            "https://attacker.test"
        )).to_be(false)
```

</details>

#### should apply head meta CSP in source order to every active resource

- should apply head meta CSP in source order to every active resource
   - Protocol capture: after_step
- Enforce CSP host paths and head meta policies
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: first_image.kind equals `image`
   - Expected: session.current_title equals `before-meta-script-ran`


<details>
<summary>Executable SSpec</summary>

Runnable source: 83 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply head meta CSP in source order to every active resource")
step("Enforce CSP host paths and head meta policies")
var session = BrowserSession.new()
session.register_resource(
    "https://safe.test/before.css",
    "@import '/before-import.css'; .before{background-image:url('/before-background.png')}"
)
session.register_resource(
    "https://safe.test/before-import.css",
    ".imported{background-image:url('/import-background.png')}"
)
session.register_resource(
    "https://safe.test/before.js",
    "document.title = 'before-meta-script-ran'"
)
expect(session.begin_network_navigation(
    "https://safe.test/app", "GET", "", "", ""
).is_ok()).to_be(true)
val document = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document.id, "document", document.url, 200,
    "Content-Security-Policy: default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; img-src 'self'",
    "<html><head>" +
    "<link rel='stylesheet' href='/before.css'>" +
    "<script src='/before.js'></script>" +
    "<img src='/before-image.png'>" +
    "<meta http-equiv='Content-Security-Policy' content=\"sandbox allow-scripts; frame-ancestors 'none'; report-uri /report; script-src 'none'; style-src 'unsafe-inline'; img-src 'none'\">" +
    "<meta http-equiv='content-security-policy' content=\"script-src *; style-src 'unsafe-inline'; img-src *\">" +
    "<style>.after{background-image:url('/after-background.png')}</style>" +
    "<link rel='stylesheet' href='/after.css'>" +
    "<script>document.title='after-inline-ran'</script>" +
    "<script src='/after.js'></script>" +
    "<img src='/after-image.png'>" +
    "</head><body></body></html>",
    ""
)).is_ok()).to_be(true)

val first_image = session.take_pending_request().unwrap()
expect(first_image.kind).to_equal("image")
expect(first_image.url).to_equal(
    "https://safe.test/before-image.png"
)

expect(session.commit_network_response(BrowserResponse.create(
    first_image.id, "image", first_image.url, 302,
    "Location: https://evil.test/stolen.png", "", ""
)).is_ok()).to_be(true)
val linked_background = session.take_pending_request().unwrap()
expect(linked_background.url).to_equal(
    "https://safe.test/before-background.png"
)
expect(session.commit_network_response(BrowserResponse.create(
    linked_background.id, "image", linked_background.url,
    404, "", "", ""
)).is_ok()).to_be(true)
val imported_background = session.take_pending_request().unwrap()
expect(imported_background.url).to_equal(
    "https://safe.test/import-background.png"
)
expect(session.commit_network_response(BrowserResponse.create(
    imported_background.id, "image", imported_background.url,
    404, "", "", ""
)).is_ok()).to_be(true)
expect(session.take_pending_request()).to_be_nil()
expect(session.current_title).to_equal("before-meta-script-ran")
val warnings = session.warnings.join("|")
expect(warnings).to_contain(
    "CSP blocked style: https://safe.test/after.css"
)
expect(warnings).to_contain("CSP blocked inline script")
expect(warnings).to_contain(
    "CSP blocked script: https://safe.test/after.js"
)
expect(warnings).to_contain(
    "CSP blocked image: https://safe.test/after-image.png"
)
expect(warnings).to_contain(
    "CSP blocked image: https://safe.test/after-background.png"
)
expect(session.warnings.join("|")).to_contain(
    "image load error: CSP blocked redirect: https://evil.test/stolen.png"
)
```

</details>

<details>
<summary>Advanced: should bound malformed meta CSP without widening following loads</summary>

#### should bound malformed meta CSP without widening following loads

- should bound malformed meta CSP without widening following loads
- Enforce CSP host paths and head meta policies


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound malformed meta CSP without widening following loads")
step("Enforce CSP host paths and head meta policies")
var session = BrowserSession.new()
expect(session.open_html(
    "https://safe.test/app",
    "<html><head><meta http-equiv='content-security-policy' content=\"" +
    "x".repeat(4097) +
    "\"><script src='/after-limit.js'></script></head></html>"
).is_ok()).to_be(true)
expect(session.take_pending_request()).to_be_nil()
expect(session.warnings.join("|")).to_contain(
    "meta CSP exceeds 4096-byte limit; following resources blocked"
)
expect(session.warnings.join("|")).to_contain(
    "CSP blocked script: https://safe.test/after-limit.js"
)
```

</details>


</details>

#### should enforce response-header sandbox capabilities before runtime creation

- should enforce response-header sandbox capabilities before runtime creation
- Intersect repeated sandbox headers before admitting scripts
   - Expected: denied.document_cookie() equals ``
   - Expected: denied_dispatch.actions.len() equals `0`
- Allow script execution while retaining opaque-origin gates
   - Expected: scripted.current_title equals `script-ran`
   - Expected: scripted.document_cookie() equals ``
   - Expected: opaque_fetch.initiator_origin equals `null`
   - Expected: opaque_fetch.site_for_cookies_url equals ``
   - Expected: opaque_fetch.credentials equals `omit`
   - Expected: opaque_fetch.script_cookie_writes.len() equals `0`
   - Expected: dispatch.default_action equals `button-activate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce response-header sandbox capabilities before runtime creation")
step("Intersect repeated sandbox headers before admitting scripts")
var denied = BrowserSession.new()
expect(denied.begin_network_navigation(
    "https://safe.test/sandbox-denied", "GET", "", "", ""
).is_ok()).to_be(true)
val denied_document = denied.take_pending_request().unwrap()
expect(denied.commit_network_response(BrowserResponse.create(
    denied_document.id, "document", denied_document.url, 200,
    "Content-Security-Policy: sandbox allow-scripts; " +
    "script-src 'unsafe-inline'\n" +
    "Content-Security-Policy: sandbox; script-src 'unsafe-inline'",
    "<html><body><button id='denied-handler' " +
    "onclick='set-attr:data-fired=yes'>run</button>" +
    "<script>document.title='escaped'</script>" +
    "<script src='/escaped.js'></script></body></html>",
    ""
)).is_ok()).to_be(true)
expect(denied.current_title).to_equal(
    "https://safe.test/sandbox-denied"
)
expect(denied.take_pending_request()).to_be_nil()
expect(denied.local_storage_item("secret")).to_be_nil()
expect(denied.document_cookie()).to_equal("")
val denied_dispatch = denied.dispatch_dom_event(
    "denied-handler", "click", true, true
)
expect(denied_dispatch.actions.len()).to_equal(0)
expect(denied.warnings.join("|")).to_contain(
    "CSP sandbox blocked script execution"
)

step("Allow script execution while retaining opaque-origin gates")
var scripted = BrowserSession.new()
expect(scripted.begin_network_navigation(
    "https://safe.test/sandbox-scripted", "GET", "", "", ""
).is_ok()).to_be(true)
val scripted_document = scripted.take_pending_request().unwrap()
expect(scripted.commit_network_response(BrowserResponse.create(
    scripted_document.id, "document", scripted_document.url, 200,
    "Content-Security-Policy: sandbox allow-scripts; " +
    "script-src 'unsafe-inline'",
    "<html><body><form id='save' action='/submit'>" +
    "<button id='send' type='submit'>save</button></form>" +
    "<script>document.cookie='secret=x';" +
    "document.title='script-ran';location.href='/escaped';" +
    "fetch('/data',{credentials:'include'})</script>" +
    "</body></html>",
    ""
)).is_ok()).to_be(true)
expect(scripted.current_title).to_equal("script-ran")
expect(scripted.current_url).to_equal(
    "https://safe.test/sandbox-scripted"
)
expect(scripted.local_storage_item("secret")).to_be_nil()
expect(scripted.document_cookie()).to_equal("")
val opaque_fetch = scripted.take_pending_request().unwrap()
expect(opaque_fetch.initiator_origin).to_equal("null")
expect(opaque_fetch.site_for_cookies_url).to_equal("")
expect(opaque_fetch.credentials).to_equal("omit")
expect(opaque_fetch.headers.lower().contains("cookie:")).to_be(false)
expect(opaque_fetch.script_cookie_writes.len()).to_equal(0)

val dispatch = scripted.dispatch_dom_event(
    "send", "click", true, true
)
expect(dispatch.default_action).to_equal("button-activate")
expect(scripted.take_pending_request()).to_be_nil()
expect(scripted.warnings.join("|")).to_contain(
    "CSP sandbox blocked form submission"
)
expect(scripted.warnings.join("|")).to_contain(
    "CSP sandbox blocked top navigation"
)
```

</details>

#### should apply final document CSP to body inline event handlers

- should apply final document CSP to body inline event handlers
- Enforce CSP host paths and head meta policies
   - Expected: denied_dispatch.actions.len() equals `0`
   - Expected: denied_dispatch.event.default_prevented is false
   - Expected: denied_dispatch.default_action_allowed is true
   - Expected: denied_dispatch.default_action equals `navigate:/default`
   - Expected: denied.pending_request_count() equals `1`
   - Expected: allowed_dispatch.actions equals `["prevent-default"]`
   - Expected: allowed_dispatch.event.default_prevented is true
   - Expected: allowed_dispatch.default_action_allowed is false
   - Expected: allowed.pending_request_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply final document CSP to body inline event handlers")
step("Enforce CSP host paths and head meta policies")
var denied = BrowserSession.new()
expect(denied.open_html(
    "https://safe.test/app",
    "<html><head><meta http-equiv='content-security-policy' " +
    "content=\"script-src 'none'\"></head><body>" +
    "<a id='denied-handler' href='/default' " +
    "onclick='prevent-default'>denied</a></body></html>"
).is_ok()).to_be(true)
val denied_dispatch = denied.dispatch_dom_event(
    "denied-handler", "click", true, true
)
expect(denied_dispatch.actions.len()).to_equal(0)
expect(denied_dispatch.event.default_prevented).to_equal(false)
expect(denied_dispatch.default_action_allowed).to_equal(true)
expect(denied_dispatch.default_action).to_equal("navigate:/default")
expect(denied.pending_request_count()).to_equal(1)
expect(denied.warnings.join("|")).to_contain(
    "CSP blocked inline event handler"
)

var allowed = BrowserSession.new()
expect(allowed.open_html(
    "https://safe.test/app",
    "<html><head><meta http-equiv='content-security-policy' " +
    "content=\"script-src 'unsafe-inline'\"></head><body>" +
    "<a id='allowed-handler' href='/default' " +
    "onclick='prevent-default'>allowed</a></body></html>"
).is_ok()).to_be(true)
val allowed_dispatch = allowed.dispatch_dom_event(
    "allowed-handler", "click", true, true
)
expect(allowed_dispatch.actions).to_equal(["prevent-default"])
expect(allowed_dispatch.event.default_prevented).to_equal(true)
expect(allowed_dispatch.default_action_allowed).to_equal(false)
expect(allowed.pending_request_count()).to_equal(0)
```

</details>

#### should bind identical image URLs to each node CSP decision

- should bind identical image URLs to each node CSP decision
   - Artifact capture: after_step
- Load the earlier identical image under its source-position CSP
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: session.image_resources.len() equals `1`
   - Expected: session.admitted_image_sources.len() equals `2`
- Bind each image command to its admitted node identity
   - Artifact capture: after_step
- Render the allowed node without painting the blocked alias
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind identical image URLs to each node CSP decision")
step("Load the earlier identical image under its source-position CSP")
var session = BrowserSession.new()
session.register_resource(
    "https://safe.test/shared.png",
    _csp_alias_png_hex(0xFFFF00FFu32)
)
expect(session.open_html(
    "https://safe.test/app",
    "<html><head>" +
    "<style>#allowed{display:block;width:2px;height:2px;" +
    "background-image:url('/shared.png');background-repeat:no-repeat}" +
    "</style>" +
    "<meta http-equiv='content-security-policy' " +
    "content=\"img-src 'none'; style-src 'unsafe-inline'\">" +
    "</head><body style='margin:0'>" +
    "<div id='allowed'></div>" +
    "<div id='blocked' style=\"display:block;width:2px;height:2px;" +
    "background-image:url('/shared.png');background-repeat:no-repeat\">" +
    "</div></body></html>"
).is_ok()).to_be(true)
expect(session.image_resources.len()).to_equal(1)
expect(session.admitted_image_sources.len()).to_equal(2)
expect(session.current_body_html).to_contain("/shared.png")
expect(session.image_resources[0].image_uri).to_start_with(
    "simple-render-image:"
)
expect(session.warnings.join("|")).to_contain(
    "CSP blocked image: https://safe.test/shared.png"
)

step("Bind each image command to its admitted node identity")
val render_html = session.render_html_document()
expect(render_html).to_contain(
    session.image_resources[0].image_uri
)
expect(render_html).to_contain("simple-blocked-image:")
val composition = simple_web_layout_render_html_draw_ir_with_images(
    render_html, 4, 4, session.image_resources
)
val commands = composition.batches[0].commands
expect(_csp_alias_command_index(
    commands, "allowed_background_image"
)).to_be_greater_than(-1)
expect(_csp_alias_command_index(
    commands, "blocked_background_image"
)).to_equal(-1)

step("Render the allowed node without painting the blocked alias")
val pixels = session.render_to_pixels(4, 4).pixel_data
expect(_csp_alias_color_count(
    pixels, 0xFFFF00FFu32
)).to_equal(4)
```

</details>

#### should retain CSP image identity after DOM removal and reorder

- should retain CSP image identity after DOM removal and reorder
   - Artifact capture: after_step
- Keep opaque node bindings out of authored DOM serialization
   - Artifact capture: after_step
- Remove the allowed node without admitting the blocked twin
   - Artifact capture: after_step
- Reorder both nodes without swapping their CSP decisions
   - Artifact capture: after_step
- Keep stylesheet-source admission independent of body order
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain CSP image identity after DOM removal and reorder")
step("Keep opaque node bindings out of authored DOM serialization")
var removed = _csp_alias_inline_session()
val authored = be_dom_serialize_html(removed.current_dom)
expect(authored).to_contain("/shared.png")
expect(authored.contains("simple-render-image:")).to_be(false)
expect(authored.contains("simple-blocked-image:")).to_be(false)
expect(removed.current_body_html).to_contain("/shared.png")

step("Remove the allowed node without admitting the blocked twin")
removed.current_dom = _csp_alias_remove_node(
    removed.current_dom, "allowed"
)
val removed_commands = (
    simple_web_layout_render_html_draw_ir_with_images(
        removed.render_html_document(), 4, 4,
        removed.image_resources
    ).batches[0].commands
)
expect(_csp_alias_command_index(
    removed_commands, "allowed_image"
)).to_equal(-1)
expect(_csp_alias_command_index(
    removed_commands, "blocked_image"
)).to_equal(-1)

step("Reorder both nodes without swapping their CSP decisions")
var reordered = _csp_alias_inline_session()
reordered.current_dom = _csp_alias_reverse_pair(
    reordered.current_dom, "allowed", "blocked"
)
val reordered_commands = (
    simple_web_layout_render_html_draw_ir_with_images(
        reordered.render_html_document(), 4, 4,
        reordered.image_resources
    ).batches[0].commands
)
expect(_csp_alias_command_index(
    reordered_commands, "allowed_image"
)).to_be_greater_than(-1)
expect(_csp_alias_command_index(
    reordered_commands, "blocked_image"
)).to_equal(-1)

step("Keep stylesheet-source admission independent of body order")
var stylesheet = BrowserSession.new()
stylesheet.register_resource(
    "https://safe.test/shared.png",
    _csp_alias_png_hex(0xFFFF00FFu32)
)
expect(stylesheet.open_html(
    "https://safe.test/app",
    "<html><head><style>#styled{width:2px;height:2px;" +
    "background-image:url('/shared.png')}</style>" +
    "<meta http-equiv='content-security-policy' " +
    "content=\"img-src 'none';style-src 'unsafe-inline'\">" +
    "</head><body><div id='styled'></div></body></html>"
).is_ok()).to_be(true)
expect(_csp_alias_command_index(
    simple_web_layout_render_html_draw_ir_with_images(
        stylesheet.render_html_document(), 4, 4,
        stylesheet.image_resources
    ).batches[0].commands,
    "styled_background_image"
)).to_be_greater_than(-1)
```

</details>

#### should navigate trusted HTTPS and reject invalid certificate identities

- should navigate trusted HTTPS and reject invalid certificate identities
   - Log capture: after_step
- Inspect TLS chain service identity HSTS and failure evidence
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should navigate trusted HTTPS and reject invalid certificate identities")
_two_origin_https_fixture()
step("Inspect TLS chain service identity HSTS and failure evidence")
_require_production_security_evidence()
```

</details>

#### should enforce origin CORS CSP redirect and mixed-content policy

- should enforce origin CORS CSP redirect and mixed-content policy
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce origin CORS CSP redirect and mixed-content policy")
_two_origin_https_fixture()
_hostile_page_fixture()
_check_security_denial()
_require_production_security_evidence()
```

</details>

<details>
<summary>Advanced: should partition cookies and storage and enforce cookie attributes</summary>

#### should partition cookies and storage and enforce cookie attributes

- should partition cookies and storage and enforce cookie attributes
- Admit one bounded host-only network cookie
- Reject transport site path origin and expiry violations
- Key a Secure Domain cookie by the top-level partition
   - Expected: first_partition equals `https://example.test`
- Keep partitioned and unpartitioned names distinct
   - Expected: other_header does not contain `scope=partition`
   - Expected: other_script does not contain `scope=partition`
- Carry a network-only cookie across a real redirect
   - Expected: fetch.fetch(request).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 184 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should partition cookies and storage and enforce cookie attributes")
val now: i64 = 1000
val origin = Origin(
    scheme: "https", host: "api.example.test", port: 443
)
val insecure = Origin(
    scheme: "http", host: "api.example.test", port: 80
)
val subdomain = Origin(
    scheme: "https", host: "sub.api.example.test", port: 443
)
val same_site = Origin(
    scheme: "https", host: "shop.example.test", port: 443
)
val cross_site = Origin(
    scheme: "https", host: "other.test", port: 443
)
var store = CookieStore.new()

step("Admit one bounded host-only network cookie")
val host_only = apply_max_age(
    parse_set_cookie(
        "host=secret; Secure; HttpOnly; SameSite=Strict;" +
        " Path=/account; Max-Age=60"
    ),
    "host=secret; Secure; HttpOnly; SameSite=Strict;" +
    " Path=/account; Max-Age=60",
    now
)
expect(store.store_from_origin(
    host_only, origin, now
).accepted).to_equal(true)
expect(store.get_header_for_origin(
    origin, "/account/view", Some(same_site), "GET", false, now
)).to_contain("host=secret")
expect(store.script_cookie_header(
    origin, "/account/view", now
)).to_equal("")

step("Reject transport site path origin and expiry violations")
expect(store.get_header_for_origin(
    insecure, "/account/view", Some(same_site), "GET", false, now
)).to_equal("")
expect(store.get_header_for_origin(
    origin, "/public", Some(same_site), "GET", false, now
)).to_equal("")
expect(store.get_header_for_origin(
    origin, "/account/view", Some(cross_site), "GET", false, now
)).to_equal("")
expect(store.get_header_for_origin(
    subdomain, "/account/view", Some(same_site), "GET", false, now
)).to_equal("")
expect(store.get_header_for_origin(
    origin, "/account/view", Some(same_site), "GET", false, now + 60
)).to_equal("")

step("Key a Secure Domain cookie by the top-level partition")
val first_partition = cookie_partition_key(same_site)
val other_partition = cookie_partition_key(cross_site)
expect(first_partition).to_equal("https://example.test")
expect(cookie_partition_key(Origin(
    scheme: "https", host: "checkout.example.test", port: 8443
))).to_equal(first_partition)
expect(cookie_partition_key(Origin(
    scheme: "http", host: "shop.example.test", port: 80
)) == first_partition).to_equal(false)
expect(store.store_from_origin(
    parse_set_cookie(
        "bad_partition=one; Partitioned; SameSite=None; Path=/"
    ),
    origin, now, first_partition
).accepted).to_equal(false)
val partitioned = parse_set_cookie(
    "part=one; Domain=example.test; Secure; HttpOnly;" +
    " SameSite=None; Partitioned; Path=/"
)
expect(store.store_from_origin(
    partitioned, origin, now, first_partition
).accepted).to_equal(true)
expect(store.get_header_for_origin(
    subdomain, "/", Some(same_site), "GET", false, now,
    first_partition
)).to_contain("part=one")
expect(store.get_header_for_origin(
    subdomain, "/", Some(cross_site), "GET", false, now,
    other_partition
)).to_equal("")

step("Keep partitioned and unpartitioned names distinct")
val global_scope = parse_set_cookie(
    "scope=global; Domain=example.test; Secure;" +
    " SameSite=None; Path=/"
)
val partition_scope = parse_set_cookie(
    "scope=partition; Domain=example.test; Secure;" +
    " SameSite=None; Partitioned; Path=/"
)
expect(store.store_from_origin(
    global_scope, origin, now
).accepted).to_equal(true)
expect(store.store_from_origin(
    partition_scope, origin, now, first_partition
).accepted).to_equal(true)
val first_header = store.get_header_for_origin(
    subdomain, "/", Some(same_site), "GET", false, now,
    first_partition
)
val other_header = store.get_header_for_origin(
    subdomain, "/", Some(cross_site), "GET", false, now,
    other_partition
)
expect(first_header).to_contain("scope=global")
expect(first_header).to_contain("scope=partition")
expect(other_header).to_contain("scope=global")
expect(other_header.contains("scope=partition")).to_equal(false)
val first_script = store.script_cookie_header(
    subdomain, "/", now, first_partition
)
val other_script = store.script_cookie_header(
    subdomain, "/", now, other_partition
)
expect(first_script).to_contain("scope=partition")
expect(other_script.contains("scope=partition")).to_equal(false)

step("Carry a network-only cookie across a real redirect")
var registry = MockResponseRegistry.create()
registry.register_with_headers(
    "https://redirect.test/start",
    302,
    [
        Pair("Location", "https://redirect.test/final"),
        Pair(
            "Set-Cookie",
            "hop=one; Secure; HttpOnly; SameSite=Lax; Path=/"
        ),
        Pair(
            "Set-Cookie",
            "partition_hop=one; Secure; HttpOnly; SameSite=None;" +
            " Partitioned; Path=/"
        )
    ],
    ""
)
registry.register("https://redirect.test/final", 200, "ok")
set_mock_registry(registry)
var fetch = FetchEngine.new_for_origin(
    Logger.new("cookie-system", BrowserLogLevel.Error),
    "https://redirect.test"
)
val request = FetchRequest(
    url: Url.parse_or_opaque("https://redirect.test/start"),
    method: "GET",
    headers: "",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "include"
)
expect(fetch.fetch(request).is_ok()).to_equal(true)
match observed_mock_request("https://redirect.test/final"):
    Some(actual_redirect_hop):
        expect(actual_redirect_hop.headers).to_contain(
            "Cookie: hop=one"
        )
        expect(actual_redirect_hop.headers).to_contain(
            "partition_hop=one"
        )
    nil:
        fail("missing observed final redirect hop")
val redirect_origin = Origin(
    scheme: "https", host: "redirect.test", port: 443
)
expect(fetch.cookie_store.script_cookie_header(
    redirect_origin, "/", now
)).to_equal("")
expect(fetch.cookie_store.get_header_for_origin(
    redirect_origin, "/", Some(redirect_origin), "GET", true, now,
    cookie_partition_key(redirect_origin)
)).to_contain("partition_hop=one")
expect(fetch.cookie_store.get_header_for_origin(
    redirect_origin, "/", Some(cross_site), "GET", true, now,
    cookie_partition_key(cross_site)
).contains("partition_hop=one")).to_equal(false)
set_mock_registry(MockResponseRegistry.create())
```

</details>


</details>

#### should enforce partitioned cookies through BrowserSession production paths

- should enforce partitioned cookies through BrowserSession production paths
   - Protocol capture: after_step
- Store same-name network cookies under the active top-level site
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: shop_header does not contain `rejected=insecure`
- Delete only the partitioned row
   - Protocol capture: after_step
- Delete only the unpartitioned row
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: after_global_delete does not contain `scope=global`
- Use the document script surface with the same partition owner
   - Protocol capture: after_step
- Reuse subdomain and port while isolating another schemeful site
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 95 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce partitioned cookies through BrowserSession production paths")
var session = BrowserSession.new()
expect(session.open_html(
    "https://shop.example.test/app",
    "<html><body>shop</body></html>"
).is_ok()).to_equal(true)

step("Store same-name network cookies under the active top-level site")
session.apply_set_cookie_header(
    "scope=global; Secure; SameSite=None; Path=/",
    "https://cdn.third.test/set"
)
session.apply_set_cookie_header(
    "scope=partition; Secure; SameSite=None; Partitioned; Path=/",
    "https://cdn.third.test/set"
)
session.apply_set_cookie_header(
    "rejected=insecure; SameSite=None; Partitioned; Path=/",
    "https://cdn.third.test/set"
)
val shop_header = session.cookie_header_for_request(
    "https://cdn.third.test/data"
)
expect(shop_header).to_contain("scope=global")
expect(shop_header).to_contain("scope=partition")
expect(shop_header.contains("rejected=insecure")).to_equal(false)

step("Delete only the partitioned row")
session.apply_set_cookie_header(
    "scope=gone; Secure; SameSite=None; Partitioned;" +
    " Path=/; Max-Age=0",
    "https://cdn.third.test/set"
)
val after_partition_delete = session.cookie_header_for_request(
    "https://cdn.third.test/data"
)
expect(after_partition_delete).to_contain("scope=global")
expect(after_partition_delete.contains("scope=partition")).to_equal(
    false
)

step("Delete only the unpartitioned row")
session.apply_set_cookie_header(
    "scope=partition; Secure; SameSite=None; Partitioned; Path=/",
    "https://cdn.third.test/set"
)
session.apply_set_cookie_header(
    "scope=gone; Secure; SameSite=None; Path=/; Max-Age=0",
    "https://cdn.third.test/set"
)
val after_global_delete = session.cookie_header_for_request(
    "https://cdn.third.test/data"
)
expect(after_global_delete).to_contain("scope=partition")
expect(after_global_delete.contains("scope=global")).to_equal(false)

step("Use the document script surface with the same partition owner")
expect(session.eval_script(
    "document.cookie = 'script_part=visible; Secure;" +
    " SameSite=None; Partitioned; Path=/'"
).is_ok()).to_equal(true)
session.apply_set_cookie_header(
    "http_only=secret; Secure; HttpOnly; SameSite=None;" +
    " Partitioned; Path=/",
    "https://shop.example.test/set"
)
expect(session.document_cookie()).to_contain("script_part=visible")
expect(session.document_cookie().contains(
    "http_only=secret"
)).to_equal(false)
expect(session.cookie_header_for_request(
    "https://shop.example.test/data"
)).to_contain("http_only=secret")

step("Reuse subdomain and port while isolating another schemeful site")
expect(session.open_html(
    "https://checkout.example.test:8443/next",
    "<html><body>checkout</body></html>"
).is_ok()).to_equal(true)
expect(session.cookie_header_for_request(
    "https://cdn.third.test/data"
)).to_contain("scope=partition")
expect(session.open_html(
    "https://other.test/next", "<html><body>other</body></html>"
).is_ok()).to_equal(true)
val other_session_header = session.cookie_header_for_request(
    "https://cdn.third.test/data"
)
expect(other_session_header.contains("scope=partition")).to_equal(
    false
)
expect(session.document_cookie().contains(
    "script_part=visible"
)).to_equal(false)
```

</details>

<details>
<summary>Advanced: should bound retained broker cookie bytes without replacing a partition</summary>

#### should bound retained broker cookie bytes without replacing a partition

- should bound retained broker cookie bytes without replacing a partition
- Admit exactly 4096 serialized cookie bytes
- Reject 4097 bytes before replacing the partition identity
   - Expected: store.count() equals `1`
   - Expected: retained.len() equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound retained broker cookie bytes without replacing a partition")
val origin = Origin(
    scheme: "https", host: "api.example.test", port: 443
)
val partition_key = "https://example.test"
var store = CookieStore.new()
val boundary = parse_set_cookie(
    "edge=" + "x".repeat(4091) +
    "; Secure; SameSite=None; Partitioned; Path=/"
)
val oversized = parse_set_cookie(
    "edge=" + "y".repeat(4092) +
    "; Secure; SameSite=None; Partitioned; Path=/"
)

step("Admit exactly 4096 serialized cookie bytes")
expect(store.store_from_origin(
    boundary, origin, 1000, partition_key
).accepted).to_be(true)

step("Reject 4097 bytes before replacing the partition identity")
val rejected = store.store_from_origin(
    oversized, origin, 1001, partition_key
)
expect(rejected.accepted).to_be(false)
expect(rejected.reason).to_equal(
    "cookie-exceeds-4096-byte-limit"
)
expect(store.count()).to_equal(1)
val retained = store.get_header_for_origin(
    origin, "/", Some(origin), "GET", false, 1001, partition_key
)
expect(retained.len()).to_equal(4096)
expect(retained).to_start_with("edge=xxxx")
expect(retained.contains("edge=yyyy")).to_be(false)
```

</details>


</details>

<details>
<summary>Advanced: should serialize cookies by path length then stable creation order</summary>

#### should serialize cookies by path length then stable creation order

- should serialize cookies by path length then stable creation order
- Retain stable tie order while excluding HttpOnly from script


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should serialize cookies by path length then stable creation order")
val origin = Origin(
    scheme: "https", host: "example.com", port: 443
)
val top_partition = "https://top.example"
val other_partition = "https://other.example"
var store = CookieStore.new()
val _ = store.store_from_origin(
    parse_set_cookie("root=base; Path=/"), origin, 100
)
val _ = store.store_from_origin(
    parse_set_cookie("same_first=one; Path=/app"), origin, 101
)
val _ = store.store_from_origin(
    parse_set_cookie(
        "private=secret; HttpOnly; Path=/app/admin"
    ),
    origin, 102
)
val _ = store.store_from_origin(
    parse_set_cookie("same_second=two; Path=/app"), origin, 103
)
val _ = store.store_from_origin(
    parse_set_cookie(
        "partition=top; Secure; SameSite=None; Partitioned; " +
        "Path=/app/admin/settings"
    ),
    origin, 104, top_partition
)
val _ = store.store_from_origin(
    parse_set_cookie(
        "partition=other; Secure; SameSite=None; Partitioned; " +
        "Path=/app/admin/settings"
    ),
    origin, 105, other_partition
)
val _ = store.store_from_origin(
    parse_set_cookie("same_first=updated; Path=/app"), origin, 106
)

step("Retain stable tie order while excluding HttpOnly from script")
val path = "/app/admin/settings/page"
expect(store.get_header_for_origin(
    origin, path, Some(origin), "GET", false, 107, top_partition
)).to_equal(
    "partition=top; private=secret; same_first=updated; " +
    "same_second=two; root=base"
)
expect(store.script_cookie_header(
    origin, path, 107, top_partition
)).to_equal(
    "partition=top; same_first=updated; same_second=two; root=base"
)
```

</details>


</details>

#### should deny Node native filesystem process socket environment and IPC access

- should deny Node native filesystem process socket environment and IPC access
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deny Node native filesystem process socket environment and IPC access")
_hostile_page_fixture()
_check_security_denial()
_require_production_security_evidence()
```

</details>

<details>
<summary>Advanced: should deny unaudited file data javascript custom and external schemes</summary>

#### should deny unaudited file data javascript custom and external schemes

- should deny unaudited file data javascript custom and external schemes
- Exercise every supported and denied navigation scheme


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deny unaudited file data javascript custom and external schemes")
_hostile_page_fixture()
step("Exercise every supported and denied navigation scheme")
_require_production_security_evidence()
```

</details>


</details>

#### should run the site renderer in the required platform sandbox

- should run the site renderer in the required platform sandbox
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the site renderer in the required platform sandbox")
_platform_evidence_row()
_check_security_denial()
_require_platform_renderer_sandbox_evidence()
```

</details>

#### should replace the renderer before exposing a cross-site document

- should replace the renderer before exposing a cross-site document
   - Binary capture: after_step
- Start one sandbox generation and commit the source site
   - Binary capture: after_step
- Store a target credential only in broker-owned cookie state
   - Binary capture: after_step
- Navigate cross-site and observe the first target request
   - Binary capture: after_step
- Reject the old generation before target bytes or credentials
   - Binary capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 95 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should replace the renderer before exposing a cross-site document")
_two_origin_https_fixture()
_platform_evidence_row()
val artifact = _production_browser_artifact()
val source_url = "https://app.example.test/start"
val target_url = "https://account.victim.test/private"
var mocks = MockResponseRegistry.create()
mocks.register(source_url, 200, "<p>source generation</p>")
mocks.register(target_url, 200, "<p>target generation</p>")
set_mock_registry(mocks)

step("Start one sandbox generation and commit the source site")
var renderers = HostedBrowserRendererRegistry.create(
    artifact, source_url
)
expect(renderers.ensure(
    91, "<p>initial blank</p>", 64, 48, 0, 100000
)).to_equal("none")
expect(_await_security_registry_document(
    renderers, 91, ""
)).to_be(true)
var source_entry = renderers.entries[0]
expect(source_entry.renderer.begin_navigate(
    source_url, "GET", "", "", "", 2000
).is_ok()).to_be(true)
renderers.entries[0] = source_entry
expect(_await_security_registry_document(
    renderers, 91, source_url
)).to_be(true)
val source_generation = renderers.entries[0].renderer.generation
val source_pid = renderers.entries[0].renderer.pid
expect(source_pid).to_be_greater_than(0)

step("Store a target credential only in broker-owned cookie state")
val target_origin = Origin(
    scheme: "https", host: "account.victim.test", port: 443
)
var credential_entry = renderers.entries[0]
expect(credential_entry.renderer.network.cookie_store.store_from_origin(
    parse_set_cookie(
        "site_secret=broker-only; Secure; SameSite=None; Path=/"
    ),
    target_origin,
    1000
).accepted).to_be(true)
renderers.entries[0] = credential_entry

step("Navigate cross-site and observe the first target request")
var navigation_entry = renderers.entries[0]
expect(navigation_entry.renderer.begin_navigate(
    target_url, "GET", "", "", "", 2000
).is_ok()).to_be(true)
renderers.entries[0] = navigation_entry
var target_generation: i64 = -1
var target_pid: i64 = -1
var target_headers = ""
var target_committed = false
var attempts: i64 = 0
while attempts < 1000 and not target_committed:
    val state = renderers.advance_window(
        91, "", "", 64, 48,
        1000000 + attempts * 1000, 100000, true
    )
    if state == "failed":
        break
    if target_generation < 0:
        match observed_mock_request("/private"):
            Some(observed):
                target_generation = (
                    renderers.entries[0].renderer.generation
                )
                target_pid = renderers.entries[0].renderer.pid
                target_headers = observed.headers
            nil:
                ()
    if (state == "frame" and
        renderers.document_url(91) == target_url):
        target_committed = true
    thread_sleep_ms(1)
    attempts = attempts + 1

step("Reject the old generation before target bytes or credentials")
expect(target_committed).to_be(true)
expect(target_generation).to_be_greater_than(source_generation)
expect(target_pid).to_be_greater_than(0)
expect(target_pid == source_pid).to_be(false)
expect(target_headers).to_contain(
    "Cookie: site_secret=broker-only"
)
expect(renderers.entries[0].renderer.site_lock).to_equal(
    "https://victim.test"
)
expect(renderers.close()).to_be(true)
set_mock_registry(MockResponseRegistry.create())
```

</details>

<details>
<summary>Advanced: should reject malformed late duplicate and oversized renderer messages</summary>

#### should reject malformed late duplicate and oversized renderer messages

- should reject malformed late duplicate and oversized renderer messages
- Send bounded IPC and Draw IR adversarial cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject malformed late duplicate and oversized renderer messages")
_hostile_page_fixture()
step("Send bounded IPC and Draw IR adversarial cases")
_require_production_security_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should contain renderer crash timeout memory and restart-rate failures</summary>

#### should contain renderer crash timeout memory and restart-rate failures

- should contain renderer crash timeout memory and restart-rate failures
- Crash and exhaust only the hostile renderer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should contain renderer crash timeout memory and restart-rate failures")
_platform_evidence_row()
step("Crash and exhaust only the hostile renderer")
_require_production_security_evidence()
```

</details>


</details>

<details>
<summary>Advanced: should account for pinned conformance and fuzz corpora</summary>

#### should account for pinned conformance and fuzz corpora

- should account for pinned conformance and fuzz corpora
- Load pinned WPT Test262 and fuzz manifests
- Retain minimized reproducers for every failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should account for pinned conformance and fuzz corpora")
step("Load pinned WPT Test262 and fuzz manifests")
step("Retain minimized reproducers for every failure")
_require_production_security_evidence()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-011`
- `REQ-WEB-BROWSER-010..019`
- `REQ-SSPEC-SYSTEM..019`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `24fcc815a01c2b00358d96159e40717c633f701728c16dba55e1bec33f12ccd1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24fcc815a01c2b00358d96159e40717c633f701728c16dba55e1bec33f12ccd1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24fcc815a01c2b00358d96159e40717c633f701728c16dba55e1bec33f12ccd1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/simple_web_browser_engine_security_spec.spl
mirror: doc/06_spec/03_system/security/simple_web_browser_engine_security_spec.md (current)
findings: 14 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/03_system/security/simple_web_browser_engine_security_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/simple_web_browser_engine_security_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/simple_web_browser_engine_security_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/security/simple_web_browser_engine_security_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/security/simple_web_browser_engine_security_spec.spl:275:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should isolate positive-owner rendering and input behind exact-window frames' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/security/simple_web_browser_engine_security_spec.spl:275:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should isolate positive-owner rendering and input behind exact-window frames' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/simple_web_browser_engine_security_spec.spl:353:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should persist shared preloaded HSTS without trusting generic responses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/simple_web_browser_engine_security_spec.spl:353:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should persist shared preloaded HSTS without trusting generic responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/simple_web_browser_engine_security_spec.spl:457:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should learn HSTS only from the completed platform HTTPS job' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/simple_web_browser_engine_security_spec.spl:457:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should learn HSTS only from the completed platform HTTPS job' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/simple_web_browser_engine_security_spec.spl:491:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate opaque renderer initiators before cookie writes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/simple_web_browser_engine_security_spec.spl:491:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should validate opaque renderer initiators before cookie writes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/simple_web_browser_engine_security_spec.spl:519:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should replace a forged CORS Origin with the requester origin' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/simple_web_browser_engine_security_spec.spl:553:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply head meta CSP in source order to every active resource' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
