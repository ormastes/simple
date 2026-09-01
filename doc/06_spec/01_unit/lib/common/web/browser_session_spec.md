# Browser Session Specification

> Tests covering BrowserSession lifecycle, BrowserSession page loading, BrowserSession script bridge, BrowserSession history and rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 86 | 86 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Specification

## Scenarios

### BrowserSession lifecycle

#### drains a large request batch without copying the queue per pop

- var session = BrowserSession new
- index to text
- "https://example test/" + index to text
- "GET", "", "payload-" + index to text
- fail
- Some
   - Expected: request.id equals `0`
   - Expected: session.pending_requests.len() equals `1024`
   - Expected: session.pending_request_head equals `1`
   - Expected: session.pending_request_count() equals `1023`
   - Expected: session.pending_requests[0].body equals ``
- fail
- Some
   - Expected: request.id equals `index.to_text()`
   - Expected: session.pending_requests.len() equals `512`
   - Expected: session.pending_request_head equals `0`
   - Expected: session.pending_request_count() equals `512`
   - Expected: session.pending_requests.len() equals `0`
   - Expected: session.pending_request_head equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
var index: i64 = 0
while index < 1024:
    session.pending_requests.push(BrowserRequest.create(
        index.to_text(), "document",
        "https://example.test/" + index.to_text(),
        "GET", "", "payload-" + index.to_text(), "text/plain"
    ))
    index = index + 1

match session.take_pending_request():
    nil:
        fail("Expected the first queued request")
    Some(request):
        expect(request.id).to_equal("0")
expect(session.pending_requests.len()).to_equal(1024)
expect(session.pending_request_head).to_equal(1)
expect(session.pending_request_count()).to_equal(1023)
expect(session.pending_requests[0].body).to_equal("")

index = 1
while index < 1024:
    match session.take_pending_request():
        nil:
            fail("Expected queued request " + index.to_text())
        Some(request):
            expect(request.id).to_equal(index.to_text())
    if index == 511:
        expect(session.pending_requests.len()).to_equal(512)
        expect(session.pending_request_head).to_equal(0)
        expect(session.pending_request_count()).to_equal(512)
    index = index + 1
expect(session.has_pending_requests()).to_be(false)
expect(session.pending_requests.len()).to_equal(0)
expect(session.pending_request_head).to_equal(0)
```

</details>

#### opens about blank

- var session = BrowserSession new
- Ok
   - Expected: session.current_url equals `about:blank`
   - Expected: session.current_title equals `about:blank`
   - Expected: session.history.len() equals `1`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_url("about:blank")
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:blank")
        expect(session.current_title).to_equal("about:blank")
        expect(session.history.len()).to_equal(1)
    Err(e) =>
        fail("Expected about:blank navigation to succeed: {e}")
```

</details>

#### stops pending navigation before commit

- var session = BrowserSession new
- session begin navigation
- session stop loading
- Ok
- fail
- Err
   - Expected: e equals `no pending navigation`
   - Expected: session.history.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.begin_navigation("about:pending")
session.stop_loading()
val result = session.commit_navigation_html("<html><body>ignored</body></html>")
match result:
    Ok(_) =>
        fail("Expected stopped pending navigation to reject commit")
    Err(e) =>
        expect(e).to_equal("no pending navigation")
        expect(session.history.len()).to_equal(0)
```

</details>

#### rejects a network response after stop and releases request state

- var session = BrowserSession new
- session begin network navigation
- Some
- session stop loading
- Ok
   - Expected: session.inflight_requests.len() equals `0`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.begin_network_navigation("https://example.com/pending", "GET", "", "", "")
match session.take_pending_request():
    Some(request):
        session.stop_loading()
        val result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "document",
            url: request.url,
            status: 200,
            headers: "",
            body: "<html><body>late</body></html>",
            error: ""
        ))
        match result:
            Ok(_): fail("Expected canceled response to be rejected")
            Err(e): expect(e).to_contain("canceled request")
        expect(session.inflight_requests.len()).to_equal(0)
    nil:
        fail("Expected pending document request")
```

</details>

#### rejects network navigation honestly

- var session = BrowserSession new
- Ok
- fail
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_url("https://example.com")
match result:
    Ok(_) =>
        fail("Expected network navigation to remain explicitly unimplemented")
    Err(e) =>
        expect(e).to_contain("network navigation is not implemented")
```

</details>

### BrowserSession page loading

#### extracts title and body from html

- var session = BrowserSession new
- Ok
   - Expected: session.current_url equals `about:test`
   - Expected: session.current_title equals `Test Page`
   - Expected: session.history.len() equals `1`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "about:test",
    "<!DOCTYPE html><html><head><title>Test Page</title></head><body><h1>Hello</h1></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:test")
        expect(session.current_title).to_equal("Test Page")
        expect(session.current_body_html).to_contain("<h1>Hello</h1>")
        expect(session.history.len()).to_equal(1)
    Err(e) =>
        fail("Expected HTML title/body extraction to succeed: {e}")
```

</details>

#### runs inline scripts against document and body

- var session = BrowserSession new
- Ok
   - Expected: session.current_title equals `After`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "about:scripted",
    "<html><head><title>Before</title></head><body><p>Old</p><script>document.title = 'After'; document.body.innerHTML = '<section>New</section>';</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("After")
        expect(session.current_body_html).to_contain("<section>New</section>")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected inline document/body script execution to succeed: {e}")
```

</details>

#### runs zero-delay timer callbacks after inline scripts

- var session = BrowserSession new
- "<html><head><title>Before</title></head><body><p>Old</p><script>setTimeout
- Ok
   - Expected: session.current_title equals `Timer`
   - Expected: session.current_body_html equals `Done`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "about:timer",
    "<html><head><title>Before</title></head><body><p>Old</p><script>setTimeout(function(){ document.title = 'Timer'; document.body.textContent = 'Done'; }, 0);</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("Timer")
        expect(session.current_body_html).to_equal("Done")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected zero-delay timer callbacks to run after inline scripts: {e}")
```

</details>

#### loads registered external scripts in source order

- var session = BrowserSession new
- session register resource
- Ok
   - Expected: session.current_title equals `Loaded`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/app.js", "document.body.innerHTML = '<h2>External</h2>'; document.title = 'Loaded';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><title>Before</title><script src='/app.js'></script></head><body><p>Old</p></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("Loaded")
        expect(session.current_body_html).to_contain("<h2>External</h2>")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected registered external scripts to load in source order: {e}")
```

</details>

#### preserves inline style blocks in the rendered session document

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "about:styles",
    "<html><head><style>body { color: red; }</style></head><body>styled</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_style_html).to_contain("body { color: red; }")
        expect(session.render_html_document()).to_contain("<style>body { color: red; }</style>")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected inline style blocks to remain in rendered session document: {e}")
```

</details>

#### bounds cumulative stylesheet source and retained HTML bytes

- [BrowserStylesheetSource external
- BROWSER RENDERER MAX PAYLOAD BYTES - accepted html len
- nil: fail
- Some
   - Expected: load.stylesheet_html() equals `accepted_html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var load = BrowserLoadState.create(
    "https://example.com/", "", -1, true, [],
    [BrowserStylesheetSource.external("/later.css")], []
)
val accepted_html = "<style>x</style>"
load.stylesheet_source_bytes = BROWSER_RENDERER_MAX_PAYLOAD_BYTES - 1
load.stylesheet_html_bytes = (
    BROWSER_RENDERER_MAX_PAYLOAD_BYTES - accepted_html.len()
)

match load.admit_stylesheet(
    "https://example.com/", "https://example.com/", "x", "", -1
):
    Some(expanded): expect(expanded.html).to_equal(accepted_html)
    nil: fail("Expected exact stylesheet byte boundary to be admitted")
expect(load.stylesheet_source_bytes).to_equal(
    BROWSER_RENDERER_MAX_PAYLOAD_BYTES
)
expect(load.stylesheet_html_bytes).to_equal(
    BROWSER_RENDERER_MAX_PAYLOAD_BYTES
)
match load.admit_stylesheet(
    "https://example.com/", "https://example.com/", "y", "", -1
):
    Some(_): fail("Expected stylesheet overflow to be rejected")
    nil: expect(load.next_style_idx).to_equal(1)
expect(load.stylesheet_html()).to_equal(accepted_html)
expect(load.warnings.join("|")).to_contain(
    "stylesheet byte limit reached; remaining styles ignored"
)
```

</details>

#### loads linked stylesheets through the session request pump

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource(
    "https://example.com/site.css",
    ".card { width: 12px; height: 8px; background-color: #2563eb; }"
)
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><link rel='stylesheet' href='/site.css'></head><body><div class='card'></div></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_style_html).to_contain("background-color: #2563eb;")
        expect(session.render(32, 24).pixel_data).to_contain(
            0xFF2563EBu32
        )
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected linked stylesheet resource to load through the session pump: {e}")
```

</details>

#### discovers, redirects, and commits bounded PNG image resources

- var session = BrowserSession new
   - Expected: first.kind equals `image`
   - Expected: first.url equals `https://example.com/start.png`
   - Expected: redirected.url equals `https://example.com/final.png`
-  browser image png hex
   - Expected: session.image_resources.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val document = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document.id, "document", document.url, 200, "",
    "<html><body><img src='/start.png'></body></html>", ""
)).is_ok()).to_be(true)

val first = session.take_pending_request().unwrap()
expect(first.kind).to_equal("image")
expect(first.url).to_equal("https://example.com/start.png")
expect(session.commit_network_response(BrowserResponse.create(
    first.id, "image", first.url, 302,
    "Location: /final.png", "", ""
)).is_ok()).to_be(true)

val redirected = session.take_pending_request().unwrap()
expect(redirected.url).to_equal("https://example.com/final.png")
expect(redirected.redirect_origin_url).to_equal(
    "https://example.com/start.png"
)
expect(session.commit_network_response(BrowserResponse.create(
    redirected.id, "image", redirected.url, 200,
    "Content-Type: image/png; charset=binary",
    _browser_image_png_hex(0xFFCC3020u32), ""
)).is_ok()).to_be(true)
expect(session.image_resources.len()).to_equal(1)
expect(session.image_resources[0].image_uri).to_equal(
    "/start.png"
)
expect(session.image_resources[0].pixels).to_equal(
    [0xFFCC3020u32]
)
```

</details>

#### invalidates render resources on image completion and failure

- var loaded = BrowserSession new
- "document getElementById
- "'url
-  browser image png hex
- var failed = BrowserSession new
- "document getElementById
- "'url
   - Expected: failed.admitted_image_sources.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loaded = BrowserSession.new()
expect(loaded.open_html(
    "https://example.com/loaded.html",
    "<div id='stage'></div>"
).is_ok()).to_be(true)
expect(loaded.eval_script(
    "document.getElementById('stage').style.backgroundImage = " +
    "'url(loaded.png)'"
).is_ok()).to_be(true)
val loaded_image = loaded.take_pending_request().unwrap()
val before_loaded = loaded.render_revisions()
expect(loaded.commit_network_response(BrowserResponse.create(
    loaded_image.id, "image", loaded_image.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFF123456u32), ""
)).is_ok()).to_be(true)
val loaded_snapshot = loaded.render_snapshot_since(
    before_loaded.document_revision,
    before_loaded.style_revision,
    before_loaded.resource_revision
)
expect(loaded_snapshot.resources_changed).to_be(true)
expect(loaded_snapshot.document_html).to_be_nil()
expect(
    loaded_snapshot.revisions.resource_revision
).to_equal(before_loaded.resource_revision + 1)

var failed = BrowserSession.new()
expect(failed.open_html(
    "https://example.com/failed.html",
    "<div id='stage'></div>"
).is_ok()).to_be(true)
expect(failed.eval_script(
    "document.getElementById('stage').style.backgroundImage = " +
    "'url(failed.png)'"
).is_ok()).to_be(true)
val failed_image = failed.take_pending_request().unwrap()
val before_failed = failed.render_revisions()
expect(failed.commit_network_response(BrowserResponse.create(
    failed_image.id, "image", failed_image.url, 503, "", "", ""
)).is_ok()).to_be(true)
val failed_snapshot = failed.render_snapshot_since(
    before_failed.document_revision,
    before_failed.style_revision,
    before_failed.resource_revision
)
expect(failed_snapshot.resources_changed).to_be(true)
expect(failed_snapshot.document_html).to_be_nil()
expect(
    failed_snapshot.revisions.resource_revision
).to_equal(before_failed.resource_revision + 1)
expect(failed.admitted_image_sources.len()).to_equal(0)
```

</details>

#### keeps repeated same-key image updates bounded across navigation and close

- var session = BrowserSession new
-  browser image png hex
   - Expected: session.image_resources.len() equals `1`
   - Expected: session.image_resources[0].pixels.len() equals `1`
   - Expected: session.image_resources.len() equals `0`
   - Expected: session.image_resources.len() equals `1`
- session close
   - Expected: session.image_resources.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val response = BrowserResponse.create(
    "image-soak", "image", "https://example.com/live.png", 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFF123456u32), ""
)
val before_revision = session.render_revisions().resource_revision
var update = 0
while update < 256:
    expect(session._store_image_response(
        response, "simple-render-image:live"
    )).to_equal("")
    expect(session.image_resources.len()).to_equal(1)
    expect(session.image_resources[0].pixels.len()).to_equal(1)
    update = update + 1
expect(session.render_revisions().resource_revision).to_equal(
    before_revision + 256
)

expect(session.open_html(
    "https://example.com/next", "<p>next</p>"
).is_ok()).to_be(true)
expect(session.image_resources.len()).to_equal(0)
expect(session._store_image_response(
    response, "simple-render-image:live"
)).to_equal("")
expect(session.image_resources.len()).to_equal(1)
session.close()
expect(session.image_resources.len()).to_equal(0)
```

</details>

#### invalidates the first frame when linked CSS completes

- var session = BrowserSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val document = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document.id, "document", document.url, 200, "",
    "<link rel='stylesheet' href='/late.css'><main>late</main>", ""
)).is_ok()).to_be(true)
val stylesheet = session.take_pending_request().unwrap()
val before = session.render_revisions()
expect(session.commit_network_response(BrowserResponse.create(
    stylesheet.id, "style", stylesheet.url, 200, "",
    "main { color: #2563eb; }", ""
)).is_ok()).to_be(true)
val snapshot = session.render_snapshot_since(
    before.document_revision,
    before.style_revision,
    before.resource_revision
)
expect(snapshot.resources_changed).to_be(false)
expect(snapshot.document_html != nil).to_be(true)
expect(snapshot.revisions.style_revision).to_equal(
    before.style_revision + 1
)
```

</details>

#### resolves stylesheet and inline background images with stable keys

- var linked = BrowserSession new
- " hero { background-image: url
   - Expected: linked_image.kind equals `image`
- "url
-  browser image png hex
- var inline = BrowserSession new without runtime
- "<html><body><div style=\"background-image:url
-  browser image png hex
   - Expected: inline.image_resources[0].image_uri equals `hero.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linked = BrowserSession.new()
expect(linked.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val document = linked.take_pending_request().unwrap()
expect(linked.commit_network_response(BrowserResponse.create(
    document.id, "document", document.url, 200, "",
    "<html><head><link rel='stylesheet' href='/css/start.css'></head><body><div class='hero'></div></body></html>",
    ""
)).is_ok()).to_be(true)
val first_style = linked.take_pending_request().unwrap()
expect(linked.commit_network_response(BrowserResponse.create(
    first_style.id, "style", first_style.url, 302,
    "Location: /themes/final.css", "", ""
)).is_ok()).to_be(true)
val final_style = linked.take_pending_request().unwrap()
expect(linked.commit_network_response(BrowserResponse.create(
    final_style.id, "style", final_style.url, 200, "",
    ".hero { background-image: url('../img/hero.png'); }", ""
)).is_ok()).to_be(true)
val linked_image = linked.take_pending_request().unwrap()
expect(linked_image.kind).to_equal("image")
expect(linked_image.url).to_equal(
    "https://example.com/img/hero.png"
)
expect(linked.active_load.unwrap().stylesheet_html()).to_contain(
    "url(\"https://example.com/img/hero.png\")"
)
expect(linked.commit_network_response(BrowserResponse.create(
    linked_image.id, "image", linked_image.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFF123456u32), ""
)).is_ok()).to_be(true)
expect(linked.image_resources[0].image_uri).to_equal(
    "https://example.com/img/hero.png"
)

var inline = BrowserSession.new_without_runtime()
expect(inline.begin_network_navigation(
    "https://example.com/page/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val inline_document = inline.take_pending_request().unwrap()
expect(inline.commit_network_response(BrowserResponse.create(
    inline_document.id, "document", inline_document.url, 200, "",
    "<html><body><div style=\"background-image:url('hero.png')\"></div></body></html>",
    ""
)).is_ok()).to_be(true)
val inline_image = inline.take_pending_request().unwrap()
expect(inline_image.url).to_equal(
    "https://example.com/page/hero.png"
)
expect(inline.commit_network_response(BrowserResponse.create(
    inline_image.id, "image", inline_image.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFF654321u32), ""
)).is_ok()).to_be(true)
expect(inline.active_load).to_be_nil()
expect(inline.image_resources[0].image_uri).to_equal("hero.png")
```

</details>

#### applies img-src and broker HSTS policy to CSS background images

- var blocked = BrowserSession new
- "<style> hero{background-image:url
- var allowed = BrowserSession new
- "<style> hero{background-image:url
   - Expected: hsts_image.kind equals `image`
   - Expected: hsts_image.url equals `http://cdn.test/p.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blocked = BrowserSession.new()
blocked.broker_network_policy = true
expect(blocked.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val blocked_document = blocked.take_pending_request().unwrap()
expect(blocked.commit_network_response(BrowserResponse.create(
    blocked_document.id, "document", blocked_document.url, 200,
    "Content-Security-Policy: img-src 'none'",
    "<style>.hero{background-image:url(http://cdn.test/p.png)}</style>",
    ""
)).is_ok()).to_be(true)
expect(blocked.take_pending_request()).to_be_nil()
expect(blocked.warnings.join("|")).to_contain(
    "CSP blocked image: https://cdn.test/p.png"
)

var allowed = BrowserSession.new()
allowed.broker_network_policy = true
expect(allowed.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val allowed_document = allowed.take_pending_request().unwrap()
expect(allowed.commit_network_response(BrowserResponse.create(
    allowed_document.id, "document", allowed_document.url, 200,
    "Content-Security-Policy: img-src https:",
    "<style>.hero{background-image:url(http://cdn.test/p.png)}</style>",
    ""
)).is_ok()).to_be(true)
val hsts_image = allowed.take_pending_request().unwrap()
expect(hsts_image.kind).to_equal("image")
expect(hsts_image.url).to_equal("http://cdn.test/p.png")
```

</details>

#### loads a JavaScript-introduced background once without restarting animations

- var session = BrowserSession new
- session advance time
- "document getElementById
   - Expected: image.kind equals `image`
   - Expected: image.image_resource_key equals `dynamic.png`
-  browser image png hex
   - Expected: session.image_resources[0].image_uri equals `dynamic.png`
   - Expected: session.image_resources[0].pixels equals `[0xFF2468ACu32]`
   - Expected: session.animation_start_time_ms equals `animation_start`
- "document getElementById


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/page/index.html",
    "<html><body style='margin:0'><div id='stage' style='width:2px;height:2px'></div></body></html>"
).is_ok()).to_be(true)
session.advance_time(40)
val animation_start = session.animation_start_time_ms

expect(session.eval_script(
    "document.getElementById('stage').style.backgroundImage = \"url('dynamic.png')\""
).is_ok()).to_be(true)
val image = session.take_pending_request().unwrap()
expect(image.kind).to_equal("image")
expect(image.url).to_equal(
    "https://example.com/page/dynamic.png"
)
expect(image.image_resource_key).to_equal("dynamic.png")
val reconcile_epoch = session.css_animation_reconcile_epoch_ms
expect(session.commit_network_response(BrowserResponse.create(
    image.id, "image", image.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFF2468ACu32), ""
)).is_ok()).to_be(true)
expect(session.image_resources[0].image_uri).to_equal("dynamic.png")
expect(session.image_resources[0].pixels).to_equal([0xFF2468ACu32])
expect(session.render(4, 4).pixels).to_contain(0xFF2468ACu32)
expect(session.animation_start_time_ms).to_equal(animation_start)
expect(session.css_animation_reconcile_epoch_ms).to_equal(
    reconcile_epoch
)

expect(session.eval_script(
    "document.getElementById('stage').style.backgroundImage = \"url('dynamic.png')\""
).is_ok()).to_be(true)
expect(session.take_pending_request()).to_be_nil()
```

</details>

#### loads a Simple Script-introduced background after script execution

- var session = BrowserSession new
- "<html><body><script type='text/simple'>body html '<div style=\"background-image:url
   - Expected: image.kind equals `image`
   - Expected: image.image_resource_key equals `simple.png`
-  browser image png hex
   - Expected: session.image_resources[0].image_uri equals `simple.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/page/index.html",
    "<html><body><script type='text/simple'>body_html '<div style=\"background-image:url(simple.png)\"></div>'</script></body></html>"
).is_ok()).to_be(true)

val image = session.take_pending_request().unwrap()
expect(image.kind).to_equal("image")
expect(image.url).to_equal(
    "https://example.com/page/simple.png"
)
expect(image.image_resource_key).to_equal("simple.png")
expect(session.commit_network_response(BrowserResponse.create(
    image.id, "image", image.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFF13579Bu32), ""
)).is_ok()).to_be(true)
expect(session.image_resources[0].image_uri).to_equal("simple.png")
```

</details>

#### allows a failed dynamic image response to retry

- var session = BrowserSession new
- "document getElementById
   - Expected: session.admitted_image_sources.len() equals `0`
- "document getElementById
- "document getElementById
   - Expected: retry.image_resource_key equals `retry.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/index.html",
    "<html><body><div id='stage'></div></body></html>"
).is_ok()).to_be(true)
expect(session.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'url(retry.png)'"
).is_ok()).to_be(true)
val failed = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    failed.id, "image", failed.url, 503, "", "", ""
)).is_ok()).to_be(true)
expect(session.admitted_image_sources.len()).to_equal(0)

expect(session.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'none'"
).is_ok()).to_be(true)
expect(session.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'url(retry.png)'"
).is_ok()).to_be(true)
val retry = session.take_pending_request().unwrap()
expect(retry.image_resource_key).to_equal("retry.png")
```

</details>

#### reuses prefetched class backgrounds without a second request

- var session = BrowserSession new
- "<style> hot{background-image:url
-  browser image png hex
- session advance time
- "document getElementById
   - Expected: session.image_resources.len() equals `1`
   - Expected: session.animation_start_time_ms equals `animation_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/index.html",
    "<style>.hot{background-image:url(class.png)}</style><body><div id='stage'></div></body>"
).is_ok()).to_be(true)
val image = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    image.id, "image", image.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFF102030u32), ""
)).is_ok()).to_be(true)
session.advance_time(25)
val animation_start = session.animation_start_time_ms

expect(session.eval_script(
    "document.getElementById('stage').className = 'hot'"
).is_ok()).to_be(true)
expect(session.take_pending_request()).to_be_nil()
expect(session.image_resources.len()).to_equal(1)
expect(session.animation_start_time_ms).to_equal(animation_start)
```

</details>

#### blocks dynamic backgrounds with CSP and rejects their late stopped response

- var blocked = BrowserSession new
- "document getElementById
- var bounded = BrowserSession new
- "document getElementById
- "'url
- "document getElementById
- "'url
- var stopped = BrowserSession new
- "document getElementById
- stopped stop loading
-  browser image png hex
   - Expected: stopped.image_resources.len() equals `0`
   - Expected: stopped.admitted_image_sources.len() equals `0`
- "document getElementById
- "document getElementById
   - Expected: stopped_retry.image_resource_key equals `late.png`
- var navigated = BrowserSession new
- "document getElementById
-  browser image png hex
   - Expected: navigated.image_resources.len() equals `0`
   - Expected: navigated.admitted_image_sources.len() equals `0`
- "document getElementById
- "document getElementById
   - Expected: navigation_retry.image_resource_key equals `old.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 103 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blocked = BrowserSession.new()
expect(blocked.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val document = blocked.take_pending_request().unwrap()
expect(blocked.commit_network_response(BrowserResponse.create(
    document.id, "document", document.url, 200,
    "Content-Security-Policy: img-src 'none'",
    "<html><body><div id='stage'></div></body></html>", ""
)).is_ok()).to_be(true)
expect(blocked.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'url(blocked.png)'"
).is_ok()).to_be(true)
expect(blocked.take_pending_request()).to_be_nil()
expect(blocked.warnings.join("|")).to_contain(
    "CSP blocked image"
)

var bounded = BrowserSession.new()
expect(bounded.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val bounded_document = bounded.take_pending_request().unwrap()
expect(bounded.commit_network_response(BrowserResponse.create(
    bounded_document.id, "document", bounded_document.url, 200,
    "Content-Security-Policy: img-src 'self'",
    "<html><body><div id='stage'></div></body></html>", ""
)).is_ok()).to_be(true)
var denied_index = 0
while denied_index < 64:
    expect(bounded.eval_script(
        "document.getElementById('stage').style.backgroundImage = " +
        "'url(https://cdn{denied_index}.test/blocked.png)'"
    ).is_ok()).to_be(true)
    expect(bounded.take_pending_request()).to_be_nil()
    denied_index = denied_index + 1
expect(bounded.eval_script(
    "document.getElementById('stage').style.backgroundImage = " +
    "'url(allowed.png)'"
).is_ok()).to_be(true)
val allowed = bounded.take_pending_request().unwrap()
expect(allowed.url).to_equal(
    "https://example.com/allowed.png"
)

var stopped = BrowserSession.new()
expect(stopped.open_html(
    "https://example.com/index.html",
    "<html><body><div id='stage'></div></body></html>"
).is_ok()).to_be(true)
expect(stopped.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'url(late.png)'"
).is_ok()).to_be(true)
val late = stopped.take_pending_request().unwrap()
stopped.stop_loading()
expect(stopped.commit_network_response(BrowserResponse.create(
    late.id, "image", late.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFFFFFFFFu32), ""
)).is_err()).to_be(true)
expect(stopped.image_resources.len()).to_equal(0)
expect(stopped.admitted_image_sources.len()).to_equal(0)
expect(stopped.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'none'"
).is_ok()).to_be(true)
expect(stopped.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'url(late.png)'"
).is_ok()).to_be(true)
val stopped_retry = stopped.take_pending_request().unwrap()
expect(stopped_retry.image_resource_key).to_equal("late.png")

var navigated = BrowserSession.new()
expect(navigated.open_html(
    "https://example.com/index.html",
    "<html><body><div id='stage'></div></body></html>"
).is_ok()).to_be(true)
expect(navigated.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'url(old.png)'"
).is_ok()).to_be(true)
val old_image = navigated.take_pending_request().unwrap()
expect(navigated.begin_network_navigation(
    "https://example.com/next.html", "GET", "", "", ""
).is_ok()).to_be(true)
val replacement = navigated.take_pending_request().unwrap()
expect(navigated.commit_network_response(BrowserResponse.create(
    replacement.id, "document", replacement.url, 0,
    "", "", "offline"
)).is_err()).to_be(true)
expect(navigated.commit_network_response(BrowserResponse.create(
    old_image.id, "image", old_image.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFFFFFFFFu32), ""
)).is_err()).to_be(true)
expect(navigated.image_resources.len()).to_equal(0)
expect(navigated.admitted_image_sources.len()).to_equal(0)
expect(navigated.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'none'"
).is_ok()).to_be(true)
expect(navigated.eval_script(
    "document.getElementById('stage').style.backgroundImage = 'url(old.png)'"
).is_ok()).to_be(true)
val navigation_retry = navigated.take_pending_request().unwrap()
expect(navigation_retry.image_resource_key).to_equal("old.png")
```

</details>

#### blocks images with img-src and rejects non-PNG or noncanonical bodies

- var blocked = BrowserSession new
- var hsts blocked = BrowserSession new
- hsts blocked take pending request
- var hsts allowed = BrowserSession new
- hsts allowed take pending request
   - Expected: raw_hsts_request.kind equals `image`
   - Expected: raw_hsts_request.url equals `http://cdn.test/p.png`
- var invalid = BrowserSession new
-  browser image png hex
   - Expected: invalid.image_resources.len() equals `0`
- var noncanonical = BrowserSession new
-  browser image png hex
   - Expected: noncanonical.image_resources.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 96 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blocked = BrowserSession.new()
expect(blocked.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val blocked_document = blocked.take_pending_request().unwrap()
expect(blocked.commit_network_response(BrowserResponse.create(
    blocked_document.id, "document", blocked_document.url, 200,
    "Content-Security-Policy: img-src 'none'",
    "<html><body><img src='/blocked.png'></body></html>", ""
)).is_ok()).to_be(true)
expect(blocked.take_pending_request()).to_be_nil()
expect(blocked.warnings.join("|")).to_contain("CSP blocked image")

var hsts_blocked = BrowserSession.new()
hsts_blocked.broker_network_policy = true
expect(hsts_blocked.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val hsts_blocked_document = (
    hsts_blocked.take_pending_request().unwrap()
)
expect(hsts_blocked.commit_network_response(
    BrowserResponse.create(
        hsts_blocked_document.id, "document",
        hsts_blocked_document.url, 200,
        "Content-Security-Policy: img-src 'none'",
        "<html><body><img src='http://cdn.test/p.png'></body></html>",
        ""
    )
).is_ok()).to_be(true)
expect(hsts_blocked.take_pending_request()).to_be_nil()
expect(hsts_blocked.warnings.join("|")).to_contain(
    "CSP blocked image: https://cdn.test/p.png"
)

var hsts_allowed = BrowserSession.new()
hsts_allowed.broker_network_policy = true
expect(hsts_allowed.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val hsts_allowed_document = (
    hsts_allowed.take_pending_request().unwrap()
)
expect(hsts_allowed.commit_network_response(
    BrowserResponse.create(
        hsts_allowed_document.id, "document",
        hsts_allowed_document.url, 200,
        "Content-Security-Policy: img-src https:",
        "<html><body><img src='http://cdn.test/p.png'></body></html>",
        ""
    )
).is_ok()).to_be(true)
val raw_hsts_request = hsts_allowed.take_pending_request().unwrap()
expect(raw_hsts_request.kind).to_equal("image")
expect(raw_hsts_request.url).to_equal("http://cdn.test/p.png")

var invalid = BrowserSession.new()
expect(invalid.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val invalid_document = invalid.take_pending_request().unwrap()
expect(invalid.commit_network_response(BrowserResponse.create(
    invalid_document.id, "document", invalid_document.url, 200, "",
    "<html><body><img src='/bad.png'></body></html>", ""
)).is_ok()).to_be(true)
val wrong_mime = invalid.take_pending_request().unwrap()
expect(invalid.commit_network_response(BrowserResponse.create(
    wrong_mime.id, "image", wrong_mime.url, 200,
    "Content-Type: text/plain",
    _browser_image_png_hex(0xFF112233u32), ""
)).is_ok()).to_be(true)
expect(invalid.image_resources.len()).to_equal(0)
expect(invalid.warnings.join("|")).to_contain(
    "unsupported content type"
)

var noncanonical = BrowserSession.new()
expect(noncanonical.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val noncanonical_document = noncanonical.take_pending_request().unwrap()
expect(noncanonical.commit_network_response(BrowserResponse.create(
    noncanonical_document.id, "document",
    noncanonical_document.url, 200, "",
    "<html><body><img src='/bad.png'></body></html>", ""
)).is_ok()).to_be(true)
val bad_body = noncanonical.take_pending_request().unwrap()
expect(noncanonical.commit_network_response(BrowserResponse.create(
    bad_body.id, "image", bad_body.url, 200,
    "Content-Type: image/png",
    _browser_image_png_hex(0xFF112233u32).upper(), ""
)).is_ok()).to_be(true)
expect(noncanonical.image_resources.len()).to_equal(0)
expect(noncanonical.warnings.join("|")).to_contain(
    "invalid image payload"
)
```

</details>

#### deduplicates and caps discovered image sources

- var session = BrowserSession new
   - Expected: session.active_load.unwrap().image_sources.len() equals `64`
- session active load unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var html = "<html><body><img src='/same.png'>"
var image_index = 0
while image_index < 65:
    html = html + "<img src='/image-{image_index}.png'>"
    image_index = image_index + 1
html = html + "</body></html>"
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://example.com/index.html", "GET", "", "", ""
).is_ok()).to_be(true)
val document = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document.id, "document", document.url, 200, "", html, ""
)).is_ok()).to_be(true)
expect(session.active_load.unwrap().image_sources.len()).to_equal(64)
expect(
    session.active_load.unwrap().image_sources[0].resolved_url
).to_equal(
    "https://example.com/same.png"
)
expect(session.active_load.unwrap().warnings.join("|")).to_contain(
    "image resource limit reached"
)
```

</details>

#### keeps legacy image keys and rejects conflicting keyed sources

- "background-image:url
   - Expected: load.image_sources.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy = BrowserImageSource.create(
    "hero.png", "https://one.test/hero.png"
)
expect(legacy.resource_key).to_equal("hero.png")
var load = BrowserLoadState.create(
    "https://two.test/index.html", "", -1, false, [], [],
    [BrowserImageSource.create_keyed(
        "hero.png", "https://one.test/hero.png", "hero.png"
    )]
)

load._queue_background_image_sources(
    "background-image:url(hero.png)",
    "https://two.test/index.html", false
)

expect(load.image_sources.len()).to_equal(1)
expect(load.warnings.join("|")).to_contain(
    "image resource key conflict ignored: hero.png"
)
```

</details>

#### expands stylesheet imports before rendering

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/base.css", "@import '/theme.css'; body { color: red; }")
session.register_resource("https://example.com/theme.css", ".theme { background: blue; }")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><link rel='stylesheet' href='/base.css'></head><body class='theme'>styled</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_style_html).to_contain(".theme { background: blue; }")
        expect(session.current_style_html).to_contain("body { color: red; }")
    Err(e) =>
        fail("Expected stylesheet imports to expand before rendering: {e}")
```

</details>

#### commits imported background CSS before its parent remainder

- var session = BrowserSession new
- "@import '/theme css'; hero{background:url
- " hero{background:url
- Ok
- "<style> hero{background:url
- "<style> hero{background:url
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource(
    "https://example.com/base.css",
    "@import '/theme.css';.hero{background:url('parent.png') no-repeat}"
)
session.register_resource(
    "https://example.com/theme.css",
    ".hero{background:url('child.png') no-repeat}"
)
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><link rel='stylesheet' href='/base.css'></head><body><div class='hero'></div></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_style_html).to_start_with(
            "<style>.hero{background:url(\"https://example.com/child.png\") no-repeat}</style>"
        )
        expect(session.current_style_html).to_end_with(
            "<style>.hero{background:url(\"https://example.com/parent.png\") no-repeat}</style>"
        )
    Err(e) =>
        fail("Expected import background cascade to preserve source order: {e}")
```

</details>

#### loads external module graphs with named imports

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_title equals `ModuleLoaded`
   - Expected: session.current_body_html equals `dep`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const label = 'dep';")
session.register_resource("https://example.com/module.js", "import \{ label \} from '/dep.js'; document.title = 'ModuleLoaded'; document.body.textContent = label;")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><title>Before</title><script type='module' src='/module.js' defer></script></head><body>start</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("ModuleLoaded")
        expect(session.current_body_html).to_equal("dep")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected external module graph with named imports to load: {e}")
```

</details>

#### supports inline module default and namespace imports

- var session = BrowserSession new
- session register resource
- "<html><body><script type='module'>import greet, * as lib from '/lib js'; document body textContent = greet
- Ok
   - Expected: session.current_body_html equals `hi browser!`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/lib.js", "export default function greet(name) { return 'hi ' + name; } export const suffix = '!';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import greet, * as lib from '/lib.js'; document.body.textContent = greet('browser') + lib.suffix;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("hi browser!")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected inline module default and namespace imports to load: {e}")
```

</details>

#### supports module default class exports and named re-exports

- var session = BrowserSession new
- session register resource
- session register resource
- "<html><body><script type='module'>import Bridge, \{ bridged \} from '/bridge js'; document body textContent =
- Ok
   - Expected: session.current_body_html equals `Bridge:v`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const value = 'v';")
session.register_resource("https://example.com/bridge.js", "export \{ value as bridged \} from '/dep.js'; export default class Bridge { constructor() { this.kind = 'Bridge'; } }")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import Bridge, \{ bridged \} from '/bridge.js'; document.body.textContent = (new Bridge()).kind + ':' + bridged;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("Bridge:v")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected module default class export and named re-export to load: {e}")
```

</details>

#### supports anonymous default function and class exports

- var session = BrowserSession new
- session register resource
- session register resource
- "<html><body><script type='module'>import anonFn from '/anon-fn js'; import AnonClass from '/anon-class js'; document body textContent = anonFn
- Ok
   - Expected: session.current_body_html equals `anon module:Anon`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/anon-fn.js", "export default function(name) { return 'anon ' + name; }")
session.register_resource("https://example.com/anon-class.js", "export default class { constructor() { this.kind = 'Anon'; } }")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import anonFn from '/anon-fn.js'; import AnonClass from '/anon-class.js'; document.body.textContent = anonFn('module') + ':' + (new AnonClass()).kind;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("anon module:Anon")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected anonymous default function and class exports to load: {e}")
```

</details>

#### supports export star re-exports

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_body_html equals `A:B`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const a = 'A'; export const b = 'B';")
session.register_resource("https://example.com/bridge.js", "export * from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import { a, b } from '/bridge.js'; document.body.textContent = a + ':' + b;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("A:B")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected export star re-exports to load: {e}")
```

</details>

#### does not forward default through export star re-exports

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_body_html equals `N`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export * from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ named \} from '/bridge.js'; document.body.textContent = named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected export star re-export to omit default forwarding: {e}")
```

</details>

#### keeps explicit local exports ahead of export star re-exports

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_body_html equals `bridge`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const value = 'dep';")
session.register_resource("https://example.com/bridge.js", "export const value = 'bridge'; export * from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ value \} from '/bridge.js'; document.body.textContent = value;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("bridge")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected explicit local exports to take precedence over export star: {e}")
```

</details>

#### supports export star as namespace re-exports

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_body_html equals `dep:x`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const value = 'dep'; export const other = 'x';")
session.register_resource("https://example.com/bridge.js", "export * as ns from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import { ns } from '/bridge.js'; document.body.textContent = ns.value + ':' + ns.other;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("dep:x")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected export star namespace re-export to load: {e}")
```

</details>

#### supports multi-declarator variable exports from a single module statement

- var session = BrowserSession new
- session register resource
- Ok
   - Expected: session.current_body_html equals `A:B:C:D`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export const a = 'A', b = 'B'; export let c = 'C', d = 'D';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import { a, b, c, d } from '/dep.js'; document.body.textContent = a + ':' + b + ':' + c + ':' + d;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("A:B:C:D")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected multi-declarator variable exports to load: {e}")
```

</details>

#### keeps default on export star as namespace re-exports

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_body_html equals `D:N`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export * as ns from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ ns \} from '/bridge.js'; document.body.textContent = ns.default + ':' + ns.named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("D:N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected export star namespace re-export to keep default: {e}")
```

</details>

#### supports default re-export aliases from dependency modules

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_body_html equals `D:N`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export \{ default as depDefault, named \} from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ depDefault, named \} from '/bridge.js'; document.body.textContent = depDefault + ':' + named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("D:N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected default re-export aliases from dependency modules to load: {e}")
```

</details>

#### keeps default on export star as namespace re-exports

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_body_html equals `D:N`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export * as ns from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ ns \} from '/bridge.js'; document.body.textContent = ns.default + ':' + ns.named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("D:N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected repeated export star namespace re-export to keep default: {e}")
```

</details>

#### supports default re-export aliases from dependency modules

- var session = BrowserSession new
- session register resource
- session register resource
- Ok
   - Expected: session.current_body_html equals `D:N`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/dep.js", "export default 'D'; export const named = 'N';")
session.register_resource("https://example.com/bridge.js", "export \{ default as depDefault, named \} from '/dep.js';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><body><script type='module'>import \{ depDefault, named \} from '/bridge.js'; document.body.textContent = depDefault + ':' + named;</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_body_html).to_equal("D:N")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected repeated default re-export alias case to load: {e}")
```

</details>

#### runs async classic scripts after parser-blocking inline scripts

- var session = BrowserSession new
- session register resource
- Ok
   - Expected: session.current_title equals `Start:inline:async`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/async.js", "document.title = document.title + ':async';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><title>Start</title></head><body><script async src='/async.js'></script><script>document.title = document.title + ':inline';</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("Start:inline:async")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected async classic script to run after parser-blocking inline script: {e}")
```

</details>

#### runs defer classic scripts after parser-blocking inline scripts

- var session = BrowserSession new
- session register resource
- Ok
   - Expected: session.current_title equals `Start:inline:defer`
   - Expected: session.warnings.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/defer.js", "document.title = document.title + ':defer';")
val result = session.open_html(
    "https://example.com/index.html",
    "<html><head><title>Start</title><script defer src='/defer.js'></script></head><body><script>document.title = document.title + ':inline';</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_title).to_equal("Start:inline:defer")
        expect(session.warnings.len()).to_equal(0)
    Err(e) =>
        fail("Expected defer classic script to run after parser-blocking inline script: {e}")
```

</details>

#### supports deterministic document loading without the js runtime

- var session = BrowserSession new without runtime
- Ok
   - Expected: session.current_url equals `about:deterministic`
   - Expected: session.current_title equals `Deterministic`
   - Expected: session.warnings.len() equals `1`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new_without_runtime()
val result = session.open_html(
    "about:deterministic",
    "<html><head><title>Deterministic</title></head><body><p>Stable</p><script>document.title = 'Ignored';</script></body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:deterministic")
        expect(session.current_title).to_equal("Deterministic")
        expect(session.current_body_html).to_contain("<p>Stable</p>")
        expect(session.runtime_state).to_be_nil()
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("runtime is disabled")
    Err(e) =>
        fail("Expected deterministic no-runtime document loading to succeed: {e}")
```

</details>

### BrowserSession script bridge

#### exposes browser like globals

- var session = BrowserSession new
- session open html
- Ok
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `about:globals`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `true`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `true`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `complete`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `about:globals`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `about:globals`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `expected_platform`
- Err
- fail
- Ok
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 67 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:globals", "<html><body><p>Hi</p></body></html>")

val ua_result = session.eval_script("navigator.userAgent")
match ua_result:
    Ok(value) =>
        expect(_display_js(value)).to_contain("Chrome/")
    Err(e) =>
        fail("Expected navigator.userAgent to evaluate: {e}")

val href_result = session.eval_script("window.location.href")
match href_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("about:globals")
    Err(e) =>
        fail("Expected window.location.href to evaluate: {e}")

val self_result = session.eval_script("window.self === window")
match self_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true")
    Err(e) =>
        fail("Expected window.self identity check to evaluate: {e}")

val body_result = session.eval_script("document.body !== null")
match body_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true")
    Err(e) =>
        fail("Expected document.body presence check to evaluate: {e}")

val ready_result = session.eval_script("document.readyState")
match ready_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("complete")
    Err(e) =>
        fail("Expected document.readyState to evaluate: {e}")

val path_result = session.eval_script("window.location.pathname")
match path_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("about:globals")
    Err(e) =>
        fail("Expected window.location.pathname to evaluate: {e}")

val url_result = session.eval_script("document.URL")
match url_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("about:globals")
    Err(e) =>
        fail("Expected document.URL to evaluate: {e}")

val platform_result = session.eval_script("navigator.platform")
val expected_platform = _expected_navigator_platform()
match platform_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal(expected_platform)
    Err(e) =>
        fail("Expected navigator.platform to evaluate: {e}")

val platform_ua_token = _expected_user_agent_token()
if platform_ua_token.len() > 0:
    match ua_result:
        Ok(value) =>
            expect(_display_js(value)).to_contain(platform_ua_token)
        Err(e) =>
            fail("Expected navigator.userAgent platform token check to reuse evaluated user agent: {e}")
```

</details>

#### exposes complete location URL parts

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `https:|example.com:8443|https://example.com:8443|/path/page|?q=1|#top`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com:8443/path/page?q=1#top", "<html><body>URL</body></html>")

val result = session.eval_script("location.protocol + '|' + location.host + '|' + location.origin + '|' + location.pathname + '|' + location.search + '|' + location.hash")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https:|example.com:8443|https://example.com:8443|/path/page|?q=1|#top")
    Err(e) =>
        fail("Expected complete location URL parts to evaluate: {e}")
```

</details>

#### keeps location parts coherent after href mutation

- var session = BrowserSession new
- session open html
- Ok
   - Expected: session.current_url equals `https://other.test/next?q=2#done`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `/next|?q=2|#done|other.test`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>URL</body></html>")

val assign_result = session.eval_script("location.href = 'https://other.test/next?q=2#done'")
match assign_result:
    Ok(value) =>
        expect(session.current_url).to_equal("https://other.test/next?q=2#done")
    Err(e) =>
        fail("Expected location.href mutation to evaluate: {e}")

val parts_result = session.eval_script("location.pathname + '|' + location.search + '|' + location.hash + '|' + location.host")
match parts_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("/next|?q=2|#done|other.test")
    Err(e) =>
        fail("Expected location parts after href mutation to evaluate: {e}")
```

</details>

#### supports location assign as a history push

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `https://example.com/next?q=1#top`
   - Expected: session.current_url equals `https://example.com/next?q=1#top`
   - Expected: session.history.len() equals `2`
   - Expected: session.current_index equals `1`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `/next|?q=1|#top`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>URL</body></html>")

val result = session.eval_script("location.assign('https://example.com/next?q=1#top')")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https://example.com/next?q=1#top")
        expect(session.current_url).to_equal("https://example.com/next?q=1#top")
        expect(session.history.len()).to_equal(2)
        expect(session.current_index).to_equal(1)
    Err(e) =>
        fail("Expected location.assign history push to evaluate: {e}")

val parts_result = session.eval_script("location.pathname + '|' + location.search + '|' + location.hash")
match parts_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("/next|?q=1|#top")
    Err(e) =>
        fail("Expected location parts after assign to evaluate: {e}")
```

</details>

#### supports location replace without appending history

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `https://example.com/replaced`
   - Expected: session.current_url equals `https://example.com/replaced`
   - Expected: session.history.len() equals `1`
   - Expected: session.current_index equals `0`
- Err
- fail
- Some
   - Expected: value.url equals `https://example.com/replaced`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>URL</body></html>")

val result = session.eval_script("location.replace('https://example.com/replaced')")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https://example.com/replaced")
        expect(session.current_url).to_equal("https://example.com/replaced")
        expect(session.history.len()).to_equal(1)
        expect(session.current_index).to_equal(0)
    Err(e) =>
        fail("Expected location.replace to evaluate without appending history: {e}")

val entry = session.current_entry()
match entry:
    Some(value) =>
        expect(value.url).to_equal("https://example.com/replaced")
    nil =>
        fail("Expected current history entry after location.replace")
```

</details>

#### supports history pushState as a location synced history push

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `https://example.com/next?q=1#top`
   - Expected: session.current_url equals `https://example.com/next?q=1#top`
   - Expected: session.history.len() equals `2`
   - Expected: session.current_index equals `1`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `/next|?q=1|#top`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start/index.html", "<html><body>URL</body></html>")

val result = session.eval_script("history.pushState(2, '', 'https://example.com/next?q=1#top')")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https://example.com/next?q=1#top")
        expect(session.current_url).to_equal("https://example.com/next?q=1#top")
        expect(session.history.len()).to_equal(2)
        expect(session.current_index).to_equal(1)
    Err(e) =>
        fail("Expected history.pushState to sync location and append history: {e}")

val parts_result = session.eval_script("location.pathname + '|' + location.search + '|' + location.hash")
match parts_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("/next|?q=1|#top")
    Err(e) =>
        fail("Expected location parts after history.pushState to evaluate: {e}")
```

</details>

#### supports history replaceState without appending history

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `https://example.com/replaced?ok=1`
   - Expected: session.current_url equals `https://example.com/replaced?ok=1`
   - Expected: session.history.len() equals `1`
   - Expected: session.current_index equals `0`
- Err
- fail
- Some
   - Expected: value.url equals `https://example.com/replaced?ok=1`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>URL</body></html>")

val result = session.eval_script("history.replaceState(3, '', 'https://example.com/replaced?ok=1')")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("https://example.com/replaced?ok=1")
        expect(session.current_url).to_equal("https://example.com/replaced?ok=1")
        expect(session.history.len()).to_equal(1)
        expect(session.current_index).to_equal(0)
    Err(e) =>
        fail("Expected history.replaceState to sync location without appending history: {e}")

val entry = session.current_entry()
match entry:
    Some(value) =>
        expect(value.url).to_equal("https://example.com/replaced?ok=1")
    nil =>
        fail("Expected current history entry after history.replaceState")
```

</details>

#### keeps push and replace neighbors stable through traversal

- var session = BrowserSession new
- "history pushState
- "history pushState
- "history replaceState
   - Expected: session.history.len() equals `3`
   - Expected: session.history[0].url equals `https://example.com/start`
   - Expected: session.history[1].url equals `https://example.com/one`
   - Expected: session.current_index equals `2`
   - Expected: session.history_back_url() equals `https://example.com/one`
   - Expected: session.history_forward_url() equals ``
   - Expected: session.current_url equals `https://example.com/one`
   - Expected: session.current_url equals `https://example.com/start`
   - Expected: session.current_url equals `https://example.com/one`
   - Expected: session.current_url equals `https://example.com/two-final`
   - Expected: session.history.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/start", "<html><body>URL</body></html>"
).is_ok()).to_be(true)
expect(session.eval_script(
    "history.pushState(1, '', '/one')"
).is_ok()).to_be(true)
expect(session.eval_script(
    "history.pushState(2, '', '/two')"
).is_ok()).to_be(true)
expect(session.eval_script(
    "history.replaceState(3, '', '/two-final')"
).is_ok()).to_be(true)

expect(session.history.len()).to_equal(3)

expect(session.history[0].url).to_equal("https://example.com/start")
expect(session.history[1].url).to_equal("https://example.com/one")
expect(session.history[2].url).to_equal(
    "https://example.com/two-final"
)
expect(session.current_index).to_equal(2)
expect(session.history_back_url()).to_equal("https://example.com/one")
expect(session.history_forward_url()).to_equal("")

expect(session.go_back().is_ok()).to_be(true)
expect(session.current_url).to_equal("https://example.com/one")
expect(session.history_back_url()).to_equal(
    "https://example.com/start"
)
expect(session.history_forward_url()).to_equal(
    "https://example.com/two-final"
)
expect(session.go_back().is_ok()).to_be(true)
expect(session.current_url).to_equal("https://example.com/start")
expect(session.go_forward().is_ok()).to_be(true)
expect(session.current_url).to_equal("https://example.com/one")
expect(session.go_forward().is_ok()).to_be(true)
expect(session.current_url).to_equal("https://example.com/two-final")
expect(session.history.len()).to_equal(3)
```

</details>

#### rejects oversized same-origin History API URLs

- var session = BrowserSession new
- "history pushState
   - Expected: session.current_url equals `https://example.com/start`
   - Expected: session.history.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/start", "<html><body>URL</body></html>"
).is_ok()).to_be(true)
val oversized = ["x"; 8193].join("")
expect(session.eval_script(
    "history.pushState(1, '', '/" + oversized + "')"
).is_ok()).to_be(true)
expect(session.current_url).to_equal("https://example.com/start")
expect(session.history.len()).to_equal(1)
```

</details>

#### supports URLSearchParams in inline browser scripts

- var session = BrowserSession new
- "<html><body><script>var params = new URLSearchParams
   - Expected: session.current_body_html equals `function:function:1:true:null:q=2&amp;empty=&amp;tag=a+b&amp;added=hello+worl... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/search?q=1&empty=&tag=a+b",
    "<html><body><script>var params = new URLSearchParams(location.search); var before = typeof URLSearchParams + ':' + typeof window.URLSearchParams + ':' + params.get('q') + ':' + params.has('empty') + ':' + params.get('missing'); params.set('q', '2'); params.append('added', 'hello world'); params.append('q', '3'); document.body.textContent = before + ':' + params.toString();</script></body></html>"
)

expect(session.current_body_html).to_equal("function:function:1:true:null:q=2&amp;empty=&amp;tag=a+b&amp;added=hello+world&amp;q=3")
```

</details>

#### exposes secure WebGPU globals

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `object`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `true:true`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `true:available`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `bgra8unorm`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `function`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals ``
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `Simple WebGPU Software Adapter:available:true`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu.html", "<html><body>GPU</body></html>")

val type_result = session.eval_script("typeof navigator.gpu")
match type_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("object")
    Err(e) =>
        fail("Expected secure navigator.gpu type check to evaluate: {e}")

val secure_result = session.eval_script("window.isSecureContext + ':' + navigator.gpu.secureContext")
match secure_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true:true")
    Err(e) =>
        fail("Expected secure WebGPU context flags to evaluate: {e}")

val adapter_result = session.eval_script("navigator.gpu.adapterAvailable + ':' + navigator.gpu.requestAdapterStatus")
match adapter_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true:available")
    Err(e) =>
        fail("Expected WebGPU adapter availability metadata to evaluate: {e}")

val format_result = session.eval_script("navigator.gpu.preferredCanvasFormat")
match format_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("bgra8unorm")
    Err(e) =>
        fail("Expected WebGPU preferred canvas format to evaluate: {e}")

val method_result = session.eval_script("typeof navigator.gpu.requestAdapter")
match method_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function")
    Err(e) =>
        fail("Expected WebGPU requestAdapter method type to evaluate: {e}")

val adapter_request_result = session.eval_script("var adapterName = ''; navigator.gpu.requestAdapter().then(function(adapter) { adapterName = adapter.name + ':' + adapter.requestAdapterStatus + ':' + adapter.isFallbackAdapter; }); adapterName")
match adapter_request_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("")
    Err(e) =>
        fail("Expected WebGPU requestAdapter promise setup to evaluate: {e}")

val adapter_name_result = session.eval_script("adapterName")
match adapter_name_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("Simple WebGPU Software Adapter:available:true")
    Err(e) =>
        fail("Expected WebGPU requestAdapter promise callback result to evaluate: {e}")
```

</details>

#### hides WebGPU globals from insecure pages

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `false`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `undefined`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("http://example.com/webgpu.html", "<html><body>GPU</body></html>")

val secure_result = session.eval_script("window.isSecureContext")
match secure_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("false")
    Err(e) =>
        fail("Expected insecure window.isSecureContext check to evaluate: {e}")

val type_result = session.eval_script("typeof navigator.gpu")
match type_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("undefined")
    Err(e) =>
        fail("Expected insecure navigator.gpu type check to evaluate: {e}")
```

</details>

#### syncs eval script changes back into session state

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `B`
   - Expected: session.current_title equals `B`
   - Expected: session.current_body_html equals `Plain`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:eval", "<html><head><title>A</title></head><body><p>Hi</p></body></html>")

val result = session.eval_script("document.title = 'B'; document.body.textContent = 'Plain'; document.title")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("B")
        expect(session.current_title).to_equal("B")
        expect(session.current_body_html).to_equal("Plain")
    Err(e) =>
        fail("Expected eval script document mutations to sync back to session state: {e}")
```

</details>

#### dispatches retained JavaScript listeners synchronously for host events

- var session = BrowserSession new
- "function note
- "var outer=document getElementById
- "var run=document getElementById
- "var blocked=document getElementById
- "var halt=document getElementById
- "var probe=document getElementById
- "var mutate=document getElementById
- "window addEventListener
- "document addEventListener
- "outer addEventListener
- "run addEventListener
- "run addEventListener
- "outer addEventListener
- "document addEventListener
- "window addEventListener
- "var removed=note
- "while
- "blocked removeEventListener
- "blocked addEventListener
- "event preventDefault
- "halt addEventListener
- "event stopImmediatePropagation
- "halt addEventListener
- "probe addEventListener
- "semantic=
- "
- "lastEvent=event;event preventDefault
- "var late=function
- "var added=function
- "mutate addEventListener
- "mutate removeEventListener
- "mutate addEventListener
- "mutate addEventListener
- "requestAnimationFrame
   - Expected: ordered.actions.len() equals `9`
- Ok
   - Expected: _display_js(value) equals `true:true:2`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `true`
- Err
- fail
   - Expected: mutation_first.actions.len() equals `2`
   - Expected: mutation_second.actions.len() equals `2`
   - Expected: session.advance_time(16) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 114 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/events",
    "<html><body><div id='outer'><button id='run' " +
    "onclick=\"document.title=document.title+'inline,'\">" +
    "Run</button></div><a id='blocked' href='/escaped'>Blocked</a>" +
    "<button id='halt'>Halt</button><button id='probe'>Probe</button>" +
    "<button id='mutate'>Mutate</button></body></html>"
).is_ok()).to_be(true)
expect(session.eval_script(
    "document.title='';" +
    "function note(label){return function(event){" +
    "document.title=document.title+label+',';};}" +
    "var outer=document.getElementById('outer');" +
    "var run=document.getElementById('run');" +
    "var blocked=document.getElementById('blocked');" +
    "var halt=document.getElementById('halt');" +
    "var probe=document.getElementById('probe');" +
    "var mutate=document.getElementById('mutate');" +
    "window.addEventListener('click',note('window-capture'),true);" +
    "document.addEventListener('click',note('document-capture'),true);" +
    "outer.addEventListener('click',note('outer-capture'),true);" +
    "run.addEventListener('click',note('target-capture'),true);" +
    "run.addEventListener('click',note('target-bubble'));" +
    "outer.addEventListener('click',note('outer-bubble'));" +
    "document.addEventListener('click',note('document-bubble'));" +
    "window.addEventListener('click',note('window-bubble'));" +
    "var removed=note('removed');var churn=0;" +
    "while(churn<300){blocked.addEventListener('click',removed);" +
    "blocked.removeEventListener('click',removed);churn=churn+1;}" +
    "blocked.addEventListener('click',function(event){" +
    "document.title=document.title+'cancel,';" +
    "event.preventDefault();});" +
    "halt.addEventListener('click',function(event){" +
    "document.title=document.title+'halt-first,';" +
    "event.stopImmediatePropagation();});" +
    "halt.addEventListener('click',note('halt-after'));" +
    "var lastEvent=null;var semantic='';" +
    "probe.addEventListener('probe',function(event){" +
    "semantic=(this===probe)+':'+" +
    "(event.currentTarget===probe)+':'+event.eventPhase;" +
    "lastEvent=event;event.preventDefault();});" +
    "var late=function(event){document.title=document.title+'late,';};" +
    "var added=function(event){document.title=document.title+'added,';};" +
    "mutate.addEventListener('mutate',function(event){" +
    "mutate.removeEventListener('mutate',late);" +
    "mutate.addEventListener('mutate',added);" +
    "document.title=document.title+'mutate,';});" +
    "mutate.addEventListener('mutate',late);" +
    "requestAnimationFrame(function(){" +
    "document.title=document.title+'raf,';});"
).is_ok()).to_be(true)

val ordered = session.dispatch_dom_event(
    "run", "click", true, true
)
expect(ordered.actions.len()).to_equal(9)
expect(session.current_title).to_equal(
    "window-capture,document-capture,outer-capture," +
    "target-capture,inline,target-bubble,outer-bubble," +
    "document-bubble,window-bubble,"
)

val canceled = session.dispatch_dom_event(
    "blocked", "click", true, true
)
expect(canceled.event.default_prevented).to_be(true)
expect(canceled.default_action_allowed).to_be(false)
expect(session.take_pending_request()).to_be_nil()
expect(session.current_title).to_end_with(
    "window-capture,document-capture,cancel," +
    "document-bubble,window-bubble,"
)

val halted = session.dispatch_dom_event(
    "halt", "click", true, true
)
expect(halted.event.immediate_propagation_stopped).to_be(true)
expect(session.current_title).to_end_with(
    "window-capture,document-capture,halt-first,"
)

val semantic = session.dispatch_dom_event(
    "probe", "probe", false, false
)
expect(semantic.event.default_prevented).to_be(false)
match session.eval_script("semantic"):
    Ok(value):
        expect(_display_js(value)).to_equal("true:true:2")
    Err(e):
        fail("Expected listener receiver semantics: {e}")
match session.eval_script(
    "lastEvent.currentTarget===null&&lastEvent.eventPhase===0"
):
    Ok(value):
        expect(_display_js(value)).to_equal("true")
    Err(e):
        fail("Expected post-dispatch Event reset: {e}")

val mutation_first = session.dispatch_dom_event(
    "mutate", "mutate", false, true
)
expect(mutation_first.actions.len()).to_equal(2)
expect(session.current_title).to_end_with("mutate,")
val mutation_second = session.dispatch_dom_event(
    "mutate", "mutate", false, true
)
expect(mutation_second.actions.len()).to_equal(2)
expect(session.current_title).to_end_with("mutate,mutate,added,")

expect(session.advance_time(16)).to_equal(1)
expect(session.current_title).to_end_with(
    "mutate,mutate,added,raf,"
)
```

</details>

#### fails closed for synchronous JavaScript-originated dispatchEvent

- var session = BrowserSession new
- "window addEventListener
- "window dispatchEvent
- Ok
   - Expected: _display_js(value) equals `false`
- Err
- fail
   - Expected: session.current_title equals `unchanged`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/script-dispatch",
    "<html><body><button id='run'>Run</button></body></html>"
).is_ok()).to_be(true)
val result = session.eval_script(
    "document.title='unchanged';" +
    "window.addEventListener('probe',function(event){" +
    "document.title='unexpected';});" +
    "window.dispatchEvent({type:'probe',bubbles:true,cancelable:true})"
)
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("false")
    Err(e):
        fail("Expected dispatchEvent to fail closed: {e}")
expect(session.current_title).to_equal("unchanged")
expect(session.warnings.join("|")).to_contain(
    "synchronous script dispatchEvent is unsupported"
)
```

</details>

#### persists storage objects and cookie jar state

- var session = BrowserSession new
- Ok
   - Expected: session.local_storage_item("theme") ?? "" equals `dark`
   - Expected: session.session_storage_item("tab") ?? "" equals `welcome`
- Err
- fail
- Ok
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val open_result = session.open_html(
    "https://example.com/app",
    "<html><body><script>localStorage.theme = 'dark'; sessionStorage.tab = 'welcome'; document.cookie = 'sid=abc123; Path=/';</script></body></html>"
)
match open_result:
    Ok(_) =>
        expect(session.local_storage_item("theme") ?? "").to_equal("dark")
        expect(session.session_storage_item("tab") ?? "").to_equal("welcome")
        expect(session.document_cookie()).to_contain("sid=abc123")
    Err(e) =>
        fail("Expected storage and cookie writes during page load to persist: {e}")

val reload_result = session.open_html(
    "https://example.com/dashboard",
    "<html><body><script>document.body.textContent = localStorage.theme + ':' + sessionStorage.tab + ':' + document.cookie;</script></body></html>"
)
match reload_result:
    Ok(_) =>
        expect(session.current_body_html).to_contain("dark:welcome:sid=abc123")
    Err(e) =>
        fail("Expected storage and cookie state to persist across page loads: {e}")
```

</details>

#### does not treat cookie attributes as standalone cookies

- var session = BrowserSession new
- Ok
   - Expected: session.document_cookie() equals `sid=abc123`
   - Expected: session.cookie_header_for_request("https://example.com/app/next") equals `sid=abc123`
   - Expected: session.cookie_header_for_request("https://example.com/other") equals ``
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val open_result = session.open_html(
    "https://example.com/app",
    "<html><body><script>document.cookie = 'sid=abc123; Path=/app';</script></body></html>"
)
match open_result:
    Ok(_) =>
        expect(session.document_cookie()).to_equal("sid=abc123")
        expect(session.cookie_header_for_request("https://example.com/app/next")).to_equal("sid=abc123")
        expect(session.cookie_header_for_request("https://example.com/other")).to_equal("")
    Err(e) =>
        fail("Expected cookie attribute parsing to ignore standalone attributes: {e}")
```

</details>

#### removes cookies when Max-Age=0 is assigned

- var session = BrowserSession new
- Ok
   - Expected: session.document_cookie() equals ``
   - Expected: session.cookie_header_for_request("https://example.com/app/next") equals ``
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val open_result = session.open_html(
    "https://example.com/app",
    "<html><body><script>document.cookie = 'sid=abc123; Path=/app'; document.cookie = 'sid=gone; Path=/app; Max-Age=0';</script></body></html>"
)
match open_result:
    Ok(_) =>
        expect(session.document_cookie()).to_equal("")
        expect(session.cookie_header_for_request("https://example.com/app/next")).to_equal("")
    Err(e) =>
        fail("Expected Max-Age=0 document.cookie assignment to remove cookie: {e}")
```

</details>

#### exposes cookie jar update points for future network integration

- var session = BrowserSession new
- session open html
- session apply set cookie header
- session apply set cookie header
   - Expected: session.cookie_header_for_request("https://example.com/other") equals `global=yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/path/page", "<html><body>Cookies</body></html>")
session.apply_set_cookie_header("theme=light; Path=/path")
session.apply_set_cookie_header("global=yes; Domain=example.com; Path=/")

expect(session.document_cookie()).to_contain("theme=light")
expect(session.document_cookie()).to_contain("global=yes")
expect(session.cookie_header_for_request("https://example.com/path/next")).to_contain("theme=light")
expect(session.cookie_header_for_request("https://example.com/other")).to_equal("global=yes")
```

</details>

#### removes cookies from Set-Cookie updates when Max-Age=0

- var session = BrowserSession new
- session open html
- session apply set cookie header
   - Expected: session.document_cookie() equals `theme=light`
- session apply set cookie header
   - Expected: session.document_cookie() equals ``
   - Expected: session.cookie_header_for_request("https://example.com/path/next") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/path/page", "<html><body>Cookies</body></html>")
session.apply_set_cookie_header("theme=light; Path=/path")
expect(session.document_cookie()).to_equal("theme=light")

session.apply_set_cookie_header("theme=gone; Path=/path; Max-Age=0")
expect(session.document_cookie()).to_equal("")
expect(session.cookie_header_for_request("https://example.com/path/next")).to_equal("")
```

</details>

#### removes cookies from Set-Cookie updates when Expires is in the past

- var session = BrowserSession new
- session open html
- session apply set cookie header
   - Expected: session.document_cookie() equals `theme=light`
- session apply set cookie header
   - Expected: session.document_cookie() equals ``
   - Expected: session.cookie_header_for_request("https://example.com/path/next") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/path/page", "<html><body>Cookies</body></html>")
session.apply_set_cookie_header("theme=light; Path=/path")
expect(session.document_cookie()).to_equal("theme=light")

session.apply_set_cookie_header("theme=gone; Path=/path; Expires=Thu, 01 Jan 1970 00:00:00 GMT")
expect(session.document_cookie()).to_equal("")
expect(session.cookie_header_for_request("https://example.com/path/next")).to_equal("")
```

</details>

#### matches Set-Cookie domain attributes that include a leading dot

- var session = BrowserSession new
- session open html
- session apply set cookie header
   - Expected: session.document_cookie() equals `theme=light`
   - Expected: session.cookie_header_for_request("https://example.com/path/next") equals `theme=light`
   - Expected: session.cookie_header_for_request("https://sub.example.com/path/next") equals `theme=light`
   - Expected: session.cookie_header_for_request("https://other.com/path/next") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/path/page", "<html><body>Cookies</body></html>")
session.apply_set_cookie_header("theme=light; Domain=.example.com; Path=/")

expect(session.document_cookie()).to_equal("theme=light")
expect(session.cookie_header_for_request("https://example.com/path/next")).to_equal("theme=light")
expect(session.cookie_header_for_request("https://sub.example.com/path/next")).to_equal("theme=light")
expect(session.cookie_header_for_request("https://other.com/path/next")).to_equal("")
```

</details>

#### installs promise globals and settles async fetch after response commit

- var session = BrowserSession new
- "<html><body><script>var out = ''; window fetch
- Ok
- Ok
   - Expected: _display_js(value) equals `function:function`
- Err
- fail
- Err
- fail
- Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/data.txt`
- Ok
- Ok
- Err
- fail
- Err
- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val open_result = session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = ''; window.fetch('/data.txt').then(function(r) { return r.text(); }).then(function(t) { out = t; document.body.textContent = t; });</script></body></html>"
)
match open_result:
    Ok(_) =>
        val promise_result = session.eval_script("typeof Promise.resolve + ':' + typeof Promise.prototype.then")
        match promise_result:
            Ok(value) =>
                expect(_display_js(value)).to_equal("function:function")
            Err(e) =>
                fail("Expected Promise globals to evaluate after fetch setup: {e}")
    Err(e) =>
        fail("Expected async fetch setup page to load: {e}")

match session.take_pending_request():
    Some(request) =>
        expect(request.kind).to_equal("fetch")
        expect(request.url).to_equal("https://example.com/data.txt")
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Set-Cookie: token=abc; Path=/\n",
            body: "alpha",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val out_result = session.eval_script("out + ':' + document.body.textContent + ':' + document.cookie")
                match out_result:
                    Ok(value) =>
                        expect(_display_js(value)).to_contain("alpha:alpha")
                        expect(_display_js(value)).to_contain("token=abc")
                    Err(e) =>
                        fail("Expected settled fetch output and cookie to evaluate: {e}")
            Err(e) =>
                fail("Expected network response commit for fetch to succeed: {e}")
    nil:
        fail("Expected pending fetch request after page load")
```

</details>

#### supports fetch then chaining through the browser promise path

- var session = BrowserSession new
- "<html><body><script>var out = ''; window fetch
- Some
- Ok
- Ok
   - Expected: _display_js(value) equals `alpha`
- Err
- fail
- Err
- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = ''; window.fetch('/data.txt').then(function(r) { return r.text(); }).then(function(t) { out = t; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "",
            body: "alpha",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("out")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("alpha")
                    Err(e) =>
                        fail("Expected fetch then-chain output to evaluate: {e}")
            Err(e) =>
                fail("Expected fetch then-chain network response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for then-chain")
```

</details>

#### supports fetch response blob metadata and text

- var session = BrowserSession new
- "<html><body><script>var out = ''; window fetch
- Some
- Ok
- Ok
   - Expected: _display_js(value) equals `5:text/plain:alpha`
- Err
- fail
- Err
- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = ''; window.fetch('/data.bin').then(function(r) { return r.blob(); }).then(function(b) { out = b.size + ':' + b.type; return b.text(); }).then(function(t) { out = out + ':' + t; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: text/plain\n",
            body: "alpha",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("out")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("5:text/plain:alpha")
                    Err(e) =>
                        fail("Expected fetch response blob metadata/text output to evaluate: {e}")
            Err(e) =>
                fail("Expected fetch blob response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for blob response")
```

</details>

#### supports fetch promise rejection on transport error

- var session = BrowserSession new
- "<html><body><script>var out = 'start'; window fetch
- Some
- Err
   - Expected: e equals `network down`
- Ok
   - Expected: _display_js(value) equals `network down`
- Err
- fail
- Ok
- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = 'start'; window.fetch('/data.txt').catch(function(err) { out = err; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 0,
            headers: "",
            body: "",
            error: "network down"
        ))
        match commit_result:
            Err(e) =>
                expect(e).to_equal("network down")
                val result = session.eval_script("out")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("network down")
                    Err(err) =>
                        fail("Expected fetch rejection handler output to evaluate: {err}")
            Ok(_) =>
                fail("Expected transport-error response commit to reject")
    nil:
        fail("Expected pending fetch request for transport-error path")
```

</details>

#### follows location changes through session owned navigation

- var session = BrowserSession new
- session register resource
- Ok
   - Expected: session.current_url equals `https://example.com/next`
   - Expected: session.current_title equals `Next`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/next", "<html><head><title>Next</title></head><body>After</body></html>")
val result = session.open_html(
    "https://example.com/start",
    "<html><body><script>location.href = 'https://example.com/next';</script>Start</body></html>"
)
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("https://example.com/next")
        expect(session.current_title).to_equal("Next")
        expect(session.current_body_html).to_contain("After")
    Err(e) =>
        fail("Expected script-owned location change to navigate through session resource: {e}")
```

</details>

#### implements storage method surface while keeping property access compatible

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `function:function:function:function:function`
- Err
- fail
- "sessionStorage setItem
- Ok
   - Expected: _display_js(value) equals `7:2:tab:mode`
   - Expected: session.session_storage_item("tab") ?? "" equals `7`
   - Expected: session.session_storage_item("mode") ?? "" equals `reader`
- Err
- fail
- "sessionStorage removeItem
- Ok
   - Expected: _display_js(value) equals `true:1:mode`
- Err
- fail
- "localStorage theme = 'dark'; localStorage getItem
- Ok
   - Expected: _display_js(value) equals `dark:0`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `1:theme`
   - Expected: session.local_storage_item("theme") ?? "" equals `dark`
- Err
- fail
- "localStorage clear
- Ok
   - Expected: _display_js(value) equals `0:0:true`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:storage", "<html><body>Storage</body></html>")

val method_result = session.eval_script(
    "typeof sessionStorage.getItem + ':' + typeof sessionStorage.setItem + ':' + typeof sessionStorage.removeItem + ':' + typeof sessionStorage.clear + ':' + typeof sessionStorage.key"
)
match method_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function:function:function:function:function")
    Err(e) =>
        fail("Expected storage method surface type check to evaluate: {e}")

val set_result = session.eval_script(
    "sessionStorage.setItem('tab', 7); sessionStorage.setItem('mode', 'reader'); sessionStorage.getItem('tab') + ':' + sessionStorage.length + ':' + sessionStorage.key(0) + ':' + sessionStorage.key(1)"
)
match set_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("7:2:tab:mode")
        expect(session.session_storage_item("tab") ?? "").to_equal("7")
        expect(session.session_storage_item("mode") ?? "").to_equal("reader")
    Err(e) =>
        fail("Expected sessionStorage setItem/getItem/key flow to evaluate: {e}")

val remove_result = session.eval_script(
    "sessionStorage.removeItem('tab'); (sessionStorage.getItem('tab') === null) + ':' + sessionStorage.length + ':' + sessionStorage.key(0)"
)
match remove_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("true:1:mode")
        expect(session.session_storage_item("tab")).to_be_nil()
    Err(e) =>
        fail("Expected sessionStorage removeItem flow to evaluate: {e}")

val property_result = session.eval_script(
    "localStorage.theme = 'dark'; localStorage.getItem('theme') + ':' + localStorage.length"
)
match property_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("dark:0")
    Err(e) =>
        fail("Expected localStorage property assignment compatibility flow to evaluate: {e}")

val synced_length_result = session.eval_script("localStorage.length + ':' + localStorage.key(0)")
match synced_length_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("1:theme")
        expect(session.local_storage_item("theme") ?? "").to_equal("dark")
    Err(e) =>
        fail("Expected localStorage synced length/key flow to evaluate: {e}")

val clear_result = session.eval_script(
    "localStorage.clear(); sessionStorage.clear(); localStorage.length + ':' + sessionStorage.length + ':' + (localStorage.getItem('theme') === null)"
)
match clear_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("0:0:true")
        expect(session.local_storage_item("theme")).to_be_nil()
        expect(session.session_storage_item("mode")).to_be_nil()
    Err(e) =>
        fail("Expected storage clear flow to evaluate: {e}")
```

</details>

### BrowserSession history and rendering

#### supports back forward and reload

- var session = BrowserSession new
- session open html
- session open html
   - Expected: session.can_go_back() is true
   - Expected: session.can_go_forward() is false
- Ok
   - Expected: session.current_url equals `about:one`
   - Expected: session.current_title equals `One`
- Err
- fail
- Ok
   - Expected: session.current_url equals `about:two`
   - Expected: session.current_title equals `Two`
- Err
- fail
- Ok
   - Expected: session.current_url equals `about:two`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:one", "<html><head><title>One</title></head><body>One</body></html>")
session.open_html("about:two", "<html><head><title>Two</title></head><body>Two</body></html>")

expect(session.can_go_back()).to_equal(true)
expect(session.can_go_forward()).to_equal(false)

val back_result = session.go_back()
match back_result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:one")
        expect(session.current_title).to_equal("One")
    Err(e) =>
        fail("Expected browser session go_back to succeed: {e}")

val forward_result = session.go_forward()
match forward_result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:two")
        expect(session.current_title).to_equal("Two")
    Err(e) =>
        fail("Expected browser session go_forward to succeed: {e}")

val reload_result = session.reload()
match reload_result:
    Ok(_) =>
        expect(session.current_url).to_equal("about:two")
        expect(session.current_body_html).to_contain("Two")
    Err(e) =>
        fail("Expected browser session reload to succeed: {e}")
```

</details>

#### rejects a stale target-bound history traversal

- var session = BrowserSession new
- Ok
- Err
   - Expected: reason equals `navigation-target-mismatch`
   - Expected: session.current_url equals `about:three`
   - Expected: session.current_index equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html("about:one", "<p>One</p>").is_ok()).to_be(true)
expect(session.open_html("about:two", "<p>Two</p>").is_ok()).to_be(true)
val stale_target = session.history_back_url()
expect(session.open_html("about:three", "<p>Three</p>").is_ok()).to_be(true)
match session.go_back_to(stale_target):
    Ok(_): fail("Expected stale history target rejection")
    Err(reason):
        expect(reason).to_equal("navigation-target-mismatch")
expect(session.current_url).to_equal("about:three")
expect(session.current_index).to_equal(2)
```

</details>

#### reloads network documents without appending history

- var session = BrowserSession new
- fail
- Some
   - Expected: request.kind equals `document`
   - Expected: request.method equals `GET`
   - Expected: session.history.len() equals `1`
   - Expected: session.current_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/page",
    "<html><body>old</body></html>"
).is_ok()).to_be(true)
expect(session.reload().is_ok()).to_be(true)
expect(session.is_loading).to_be(true)
match session.take_pending_request():
    nil:
        fail("Expected reload document request")
    Some(request):
        expect(request.kind).to_equal("document")
        expect(request.method).to_equal("GET")
        expect(session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "",
                body: "<html><body>fresh</body></html>",
                error: ""
            )
        ).is_ok()).to_be(true)
expect(session.current_body_html).to_contain("fresh")
expect(session.history.len()).to_equal(1)
expect(session.current_index).to_equal(0)
```

</details>

#### renders current body through browser renderer

- var session = BrowserSession new
   - Expected: render.width equals `320`
   - Expected: render.height equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:render",
    "<html><body><div style='background-color: #ff0000'><span>Hello</span></div></body></html>"
)
val render = session.render(320, 200)
expect(render.width).to_equal(320)
expect(render.height).to_equal(200)
expect(render.node_count).to_be_greater_than(0)
```

</details>

#### deletes one UTF-8 scalar from focused text input

- var session = BrowserSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:input",
    "<html><body><input id='name' value='café' data-focused></body></html>"
)
expect(session.dispatch_dom_keyboard_event(
    "name", "Backspace", true
).is_ok()).to_be(true)
expect(session.current_body_html).to_contain("value=\"caf\"")
```

</details>

#### edits UTF-8 text at the caret and replaces selections

- var session = BrowserSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:selection",
    "<html><body><input id='name' value='aéz' data-focused></body></html>"
)
expect(session.dispatch_dom_keyboard_event_with_shift(
    "name", "37", true, false
).is_ok()).to_be(true)
expect(session.append_dom_text_input("name", "X").is_ok()).to_be(true)
expect(session.current_body_html).to_contain("value=\"aéXz\"")

expect(session.dispatch_dom_keyboard_event_with_shift(
    "name", "37", true, true
).is_ok()).to_be(true)
expect(session.append_dom_text_input("name", "Y").is_ok()).to_be(true)
expect(session.current_body_html).to_contain("value=\"aéYz\"")

expect(session.dispatch_dom_keyboard_event_with_shift(
    "name", "127", true, false
).is_ok()).to_be(true)
expect(session.dispatch_dom_keyboard_event_with_shift(
    "name", "8", true, false
).is_ok()).to_be(true)
expect(session.current_body_html).to_contain("value=\"aé\"")
```

</details>

#### activates Space on keyup and honors canceled keydown

- var session = BrowserSession new
- var canceled = BrowserSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:buttons",
    "<html><body><button id='go' onclick='set-attr:data-clicked=true'>Go</button><button id='blocked' onkeydown='prevent-default' onclick='set-attr:data-clicked=true'>Blocked</button></body></html>"
)
expect(session.dispatch_dom_keyboard_event(
    "go", " ", true
).is_ok()).to_be(true)
expect(session.current_body_html).not.to_contain("data-clicked=\"true\"")
expect(session.dispatch_dom_keyboard_event(
    "go", " ", false
).is_ok()).to_be(true)
expect(session.current_body_html).to_contain("data-clicked=\"true\"")

var canceled = BrowserSession.new()
canceled.open_html(
    "about:canceled-button",
    "<html><body><button id='blocked' onkeydown='prevent-default' onclick='set-attr:data-clicked=true'>Blocked</button></body></html>"
)
expect(canceled.dispatch_dom_keyboard_event(
    "blocked", " ", true
).is_ok()).to_be(true)
expect(canceled.dispatch_dom_keyboard_event(
    "blocked", " ", false
).is_ok()).to_be(true)
expect(canceled.current_body_html).not.to_contain("data-clicked=\"true\"")
```

</details>

#### disarms Space activation when navigation starts or stops

- var session = BrowserSession new
   - Expected: session.pending_space_activation_target equals `go`
   - Expected: session.pending_space_activation_target equals ``
   - Expected: session.pending_space_activation_target equals `go`
- session stop loading
   - Expected: session.pending_space_activation_target equals ``
   - Expected: session.current_url equals `https://example.test/old`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/old",
    "<html><body><button id='go' onclick='set-attr:data-clicked=true'>Go</button></body></html>"
)
expect(session.dispatch_dom_keyboard_event(
    "go", " ", true
).is_ok()).to_be(true)
expect(session.pending_space_activation_target).to_equal("go")

expect(session.begin_network_navigation(
    "https://example.test/new", "GET", "", "", ""
).is_ok()).to_be(true)
expect(session.pending_space_activation_target).to_equal("")
expect(session.dispatch_dom_keyboard_event(
    "go", " ", true
).is_ok()).to_be(true)
expect(session.pending_space_activation_target).to_equal("go")
session.stop_loading()
expect(session.pending_space_activation_target).to_equal("")
expect(session.dispatch_dom_keyboard_event(
    "go", " ", false
).is_ok()).to_be(true)
expect(session.current_url).to_equal("https://example.test/old")
expect(session.current_body_html).not.to_contain("data-clicked=\"true\"")
```

</details>

#### activates the form submitter from Enter in a text input

- var session = BrowserSession new
- fail
- Some
   - Expected: request.method equals `GET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/start",
    "<html><body><form action='/find'><input id='query' name='q' value='simple'><button id='go' onclick='set-attr:data-clicked=true'>Search</button></form></body></html>"
)
expect(session.dispatch_dom_keyboard_event(
    "query", "Enter", true
).is_ok()).to_be(true)
expect(session.current_body_html).to_contain("data-clicked=\"true\"")
match session.take_pending_request():
    nil:
        fail("Expected implicit form navigation request")
    Some(request):
        expect(request.method).to_equal("GET")
        expect(request.url).to_equal(
            "https://example.test/find?q=simple"
        )
```

</details>

#### submits a buttonless form only with one blocking field

- var single = BrowserSession new
- fail
- Some
- var multiple = BrowserSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var single = BrowserSession.new()
single.open_html(
    "https://example.test/start",
    "<html><body><form action='/find'><input id='query' name='q' value='simple'></form></body></html>"
)
expect(single.dispatch_dom_keyboard_event(
    "query", "Enter", true
).is_ok()).to_be(true)
match single.take_pending_request():
    nil:
        fail("Expected direct implicit form request")
    Some(request):
        expect(request.url).to_equal(
            "https://example.test/find?q=simple"
        )

var multiple = BrowserSession.new()
multiple.open_html(
    "https://example.test/start",
    "<html><body><form action='/find'><input id='first' name='a'><input name='b'></form></body></html>"
)
expect(multiple.dispatch_dom_keyboard_event(
    "first", "Enter", true
).is_ok()).to_be(true)
expect(multiple.take_pending_request()).to_be_nil()
```

</details>

#### traverses focus by tabindex in both directions

- var session = BrowserSession new
   - Expected: be_dom_focused_id(session.dom_root()) equals `first`
   - Expected: be_dom_focused_id(session.dom_root()) equals `second`
   - Expected: be_dom_focused_id(session.dom_root()) equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:focus",
    "<html><body><input id='regular'><button id='second' tabindex='2'>Second</button><button id='first' tabindex='1'>First</button><button id='disabled' disabled>Disabled</button><div id='last' tabindex='0'>Last</div></body></html>"
)
expect(session.dispatch_dom_keyboard_event_with_shift(
    "", "Tab", true, false
).is_ok()).to_be(true)
expect(be_dom_focused_id(session.dom_root())).to_equal("first")

expect(session.dispatch_dom_keyboard_event_with_shift(
    "first", "Tab", true, false
).is_ok()).to_be(true)
expect(be_dom_focused_id(session.dom_root())).to_equal("second")

expect(session.dispatch_dom_keyboard_event_with_shift(
    "second", "Tab", true, true
).is_ok()).to_be(true)
expect(be_dom_focused_id(session.dom_root())).to_equal("first")
```

</details>

#### does not move focus when Tab keydown is canceled

- var session = BrowserSession new
   - Expected: be_dom_focused_id(session.dom_root()) equals `stay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:focus-cancel",
    "<html><body><button id='stay' data-focused onkeydown='prevent-default'>Stay</button><button id='next'>Next</button></body></html>"
)
expect(session.dispatch_dom_keyboard_event_with_shift(
    "stay", "Tab", true, false
).is_ok()).to_be(true)
expect(be_dom_focused_id(session.dom_root())).to_equal("stay")
```

</details>

#### exposes canonical raw keyboard payload without retaining key state

- var session = BrowserSession new
- "var stay=document getElementById
- "stay addEventListener
- "if
- "stay addEventListener
- Ok
   - Expected: dispatch.event.key equals `A`
   - Expected: dispatch.event.code equals `KeyA`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `ArrowLeft`
   - Expected: dispatch.event.code equals `ArrowLeft`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `ArrowLeft`
   - Expected: dispatch.event.code equals `ArrowLeft`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `!`
   - Expected: dispatch.event.code equals `Digit1`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `F1`
   - Expected: dispatch.event.code equals `F1`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `Shift`
   - Expected: dispatch.event.code equals `ShiftLeft`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `Control`
   - Expected: dispatch.event.code equals `ControlLeft`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `Alt`
   - Expected: dispatch.event.code equals `AltLeft`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `Meta`
   - Expected: dispatch.event.code equals `MetaLeft`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `Unidentified`
   - Expected: dispatch.event.code equals `Unidentified`
- Err
- fail
- Ok
   - Expected: dispatch.event.key equals `Tab`
   - Expected: dispatch.event.code equals `Tab`
- Err
- fail
   - Expected: be_dom_focused_id(session.dom_root()) equals `stay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 132 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:keyboard-payload",
    "<html><body><button id='stay' data-focused>Stay</button>" +
    "<button id='next'>Next</button></body></html>"
)
expect(session.eval_script(
    "var stay=document.getElementById('stay');" +
    "stay.addEventListener('keydown',function(event){" +
    "document.title=event.type+'|'+event.key+'|'+event.code+'|'+" +
    "event.shiftKey+'|'+event.altKey+'|'+event.ctrlKey+'|'+" +
    "event.metaKey+'|'+event.repeat;" +
    "if(event.key==='Tab'&&event.shiftKey){event.preventDefault();}});" +
    "stay.addEventListener('keyup',function(event){" +
    "document.title=event.type+'|'+event.key+'|'+event.code+'|'+" +
    "event.shiftKey+'|'+event.repeat;});"
).is_ok()).to_be(true)

match session.dispatch_dom_keyboard_code_event(
    "stay", 65, true, true
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("A")
        expect(dispatch.event.code).to_equal("KeyA")
        expect(dispatch.event.shift_key).to_be(true)
        expect(dispatch.event.alt_key).to_be(false)
        expect(dispatch.event.ctrl_key).to_be(false)
        expect(dispatch.event.meta_key).to_be(false)
        expect(dispatch.event.repeat).to_be(false)
    Err(reason):
        fail(reason)
expect(session.current_title).to_equal(
    "keydown|A|KeyA|true|false|false|false|false"
)

match session.dispatch_dom_keyboard_code_event(
    "stay", 37, true, false
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("ArrowLeft")
        expect(dispatch.event.code).to_equal("ArrowLeft")
        expect(dispatch.event.shift_key).to_be(false)
        expect(dispatch.event.repeat).to_be(false)
    Err(reason):
        fail(reason)
expect(session.current_title).to_equal(
    "keydown|ArrowLeft|ArrowLeft|false|false|false|false|false"
)

match session.dispatch_dom_keyboard_code_event(
    "stay", 37, false, false
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("ArrowLeft")
        expect(dispatch.event.code).to_equal("ArrowLeft")
        expect(dispatch.event.shift_key).to_be(false)
        expect(dispatch.event.repeat).to_be(false)
    Err(reason):
        fail(reason)
expect(session.current_title).to_equal(
    "keyup|ArrowLeft|ArrowLeft|false|false"
)

match session.dispatch_dom_keyboard_code_event(
    "stay", 49, true, true
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("!")
        expect(dispatch.event.code).to_equal("Digit1")
    Err(reason):
        fail(reason)
match session.dispatch_dom_keyboard_code_event(
    "stay", 112, true, false
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("F1")
        expect(dispatch.event.code).to_equal("F1")
        expect(dispatch.event.shift_key).to_be(false)
    Err(reason):
        fail(reason)

match session.dispatch_dom_keyboard_code_event(
    "stay", 16, true, true
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("Shift")
        expect(dispatch.event.code).to_equal("ShiftLeft")
    Err(reason):
        fail(reason)
match session.dispatch_dom_keyboard_code_event(
    "stay", 17, true, false
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("Control")
        expect(dispatch.event.code).to_equal("ControlLeft")
    Err(reason):
        fail(reason)
match session.dispatch_dom_keyboard_code_event(
    "stay", 18, true, false
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("Alt")
        expect(dispatch.event.code).to_equal("AltLeft")
    Err(reason):
        fail(reason)
match session.dispatch_dom_keyboard_code_event(
    "stay", 91, true, false
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("Meta")
        expect(dispatch.event.code).to_equal("MetaLeft")
    Err(reason):
        fail(reason)
match session.dispatch_dom_keyboard_code_event(
    "stay", 999, true, false
):
    Ok(dispatch):
        expect(dispatch.event.key).to_equal("Unidentified")
        expect(dispatch.event.code).to_equal("Unidentified")
    Err(reason):
        fail(reason)

match session.dispatch_dom_keyboard_code_event(
    "stay", 9, true, true
):
    Ok(dispatch):
        expect(dispatch.event.default_prevented).to_be(true)
        expect(dispatch.event.key).to_equal("Tab")
        expect(dispatch.event.code).to_equal("Tab")
    Err(reason):
        fail(reason)
expect(be_dom_focused_id(session.dom_root())).to_equal("stay")
```

</details>

#### emits focus lifecycle events when pointer focus changes

- var session = BrowserSession new
   - Expected: dispatch.default_action equals `focus-element`
   - Expected: be_dom_focused_id(session.dom_root()) equals `next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "about:pointer-focus",
    "<html><body><button id='old' data-focused onblur='set-attr:data-blurred=true' onfocusout='set-attr:data-focusout=true'>Old</button><button id='next' onfocus='set-attr:data-focused-event=true' onfocusin='set-attr:data-focusin=true'>Next</button></body></html>"
)
val dispatch = session.dispatch_dom_event(
    "next", "mousedown", true, true
)
expect(dispatch.default_action).to_equal("focus-element")
expect(be_dom_focused_id(session.dom_root())).to_equal("next")
expect(session.current_body_html).to_contain("data-blurred=\"true\"")
expect(session.current_body_html).to_contain("data-focusout=\"true\"")
expect(session.current_body_html).to_contain(
    "data-focused-event=\"true\""
)
expect(session.current_body_html).to_contain("data-focusin=\"true\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession lifecycle, BrowserSession page loading, BrowserSession script bridge, BrowserSession history and rendering.
- BrowserSession lifecycle
- BrowserSession page loading
- BrowserSession script bridge
- BrowserSession history and rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 86 |
| Active scenarios | 86 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
