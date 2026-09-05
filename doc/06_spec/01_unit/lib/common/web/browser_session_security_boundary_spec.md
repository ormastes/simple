# Browser Session Security Boundary Specification

> Tests covering BrowserSession production security boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Security Boundary Specification

## Scenarios

### BrowserSession production security boundary

#### bounds hostile do-while script execution

- Run a nonterminating do-while script in a browser session
- var session = BrowserSession new
- "var iterations = 0; do { iterations = iterations + 1; } while
- Ok
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a nonterminating do-while script in a browser session")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://safe.test/app", "<html><body>safe</body></html>"
)
expect(opened.is_ok()).to_be(true)

val exhausted = session.eval_script(
    "var iterations = 0; do { iterations = iterations + 1; } while (true);"
)
expect(exhausted.is_ok()).to_be(true)
match session.eval_script("iterations"):
    Ok(JsValue.Number(iterations)):
        expect(iterations).to_be_greater_than(0.0)
        expect(iterations).to_be_less_than(100000.0)
    _:
        fail("Expected the do-while execution limit to terminate the script")
```

</details>

#### bounds hostile recursive script execution

- Run an unbounded recursive script in a browser session
- var session = BrowserSession new
- "var depth = 0; function recurse
- Ok
   - Expected: depth equals `256.0`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run an unbounded recursive script in a browser session")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://safe.test/app", "<html><body>safe</body></html>"
)
expect(opened.is_ok()).to_be(true)

match session.eval_script(
    "var depth = 0; function recurse() { depth = depth + 1; recurse(); } recurse(); depth"
):
    Ok(JsValue.Number(depth)):
        expect(depth).to_equal(256.0)
    _:
        fail("Expected the recursion limit to terminate the script")
```

</details>

<details>
<summary>Advanced: shares one execution budget across nested script loops</summary>

#### shares one execution budget across nested script loops

- Run nested loops and then advance the queued timer task
- var session = BrowserSession new
- "var timerRan = 0; setTimeout
   - Expected: session.advance_time(0) equals `1`
- Ok
   - Expected: timer_ran equals `1.0`
- fail
- Ok
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run nested loops and then advance the queued timer task")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://safe.test/app", "<html><body>safe</body></html>"
)
expect(opened.is_ok()).to_be(true)

val exhausted = session.eval_script(
    "var timerRan = 0; setTimeout(function() { timerRan = 1; }, 0); var iterations = 0; for (var outer = 0; outer < 100000; outer = outer + 1) { for (var inner = 0; inner < 100000; inner = inner + 1) { iterations = iterations + 1; } }"
)
expect(exhausted.is_ok()).to_be(true)
expect(session.advance_time(0)).to_equal(1)
match session.eval_script("timerRan"):
    Ok(JsValue.Number(timer_ran)):
        expect(timer_ran).to_equal(1.0)
    _:
        fail("Expected timer execution to receive a fresh task budget")
match session.eval_script("iterations"):
    Ok(JsValue.Number(iterations)):
        expect(iterations).to_be_greater_than(0.0)
        expect(iterations).to_be_less_than(100000.0)
    _:
        fail("Expected the shared execution budget to preserve runtime state")
```

</details>


</details>

#### rejects direct file navigation before reading the host filesystem

- Navigate directly to a local file URL
- var session = BrowserSession new
   - Expected: result.is_err() is true
   - Expected: session.current_url equals `about:blank`
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Navigate directly to a local file URL")
var session = BrowserSession.new()
val result = session.begin_network_navigation("file:///etc/passwd", "GET", "", "", "")
expect(result.is_err()).to_equal(true)
expect(session.current_url).to_equal("about:blank")
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### rejects request-line injection in the central subresource pump

- Queue a subresource URL containing an injected request line
- var session = BrowserSession new
   - Expected: session.take_pending_request().is_none() is true
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Queue a subresource URL containing an injected request line")
var session = BrowserSession.new()
session.open_html(
    "https://safe.test/app", "<html><body>safe</body></html>"
)
session.pending_requests.push(BrowserRequest.create(
    "script-injection", "script",
    "https://safe.test/app.js\r\nX-Injected: yes",
    "GET", "", "", ""
))

expect(session.take_pending_request().is_none()).to_equal(true)
expect(session.has_pending_requests()).to_equal(false)
expect(session.warnings).to_contain(
    "blocked invalid browser request"
)
```

</details>

#### rejects direct file open and file home navigation

- Open and assign a local file URL through browser navigation APIs
- var session = BrowserSession new
   - Expected: session.open_url("file:///etc/hosts").is_err() is true
   - Expected: session.try_set_home_url("file:///etc/hosts") is false
   - Expected: session.home_url equals `about:blank`
   - Expected: session.current_url equals `about:blank`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open and assign a local file URL through browser navigation APIs")
var session = BrowserSession.new()
expect(session.open_url("file:///etc/hosts").is_err()).to_equal(true)
expect(session.try_set_home_url("file:///etc/hosts")).to_equal(false)
expect(session.home_url).to_equal("about:blank")
expect(session.current_url).to_equal("about:blank")
```

</details>

#### rejects executable and unknown top-level navigation schemes

- Navigate to executable and inline-data URL schemes
- var session = BrowserSession new
   - Expected: session.begin_network_navigation("javascript:alert(1)", "GET", "", "", "").is_err() is true
   - Expected: session.begin_network_navigation("data:text/html,<script>alert(1)</script>", "GET", "", "", "").is_err() is true
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Navigate to executable and inline-data URL schemes")
var session = BrowserSession.new()
expect(session.begin_network_navigation("javascript:alert(1)", "GET", "", "", "").is_err()).to_equal(true)
expect(session.begin_network_navigation("data:text/html,<script>alert(1)</script>", "GET", "", "", "").is_err()).to_equal(true)
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### keeps storage and cookies bound to the active document after a cross-origin location write

- Write cross-origin location, storage, and cookie state from the active document
- var session = BrowserSession new
   - Expected: session.current_url equals `https://evil.test/landing`
   - Expected: session.document_url equals `https://bank.test/app`
   - Expected: session.document_cookie() equals ``
   - Expected: session.local_storage_item("bank") ?? "" equals `secret`
   - Expected: session.local_storage_item("planted") ?? "" equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write cross-origin location, storage, and cookie state from the active document")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://bank.test/app",
    "<html><body><script>localStorage.bank = 'secret'; document.cookie = 'bank=yes; Path=/';</script></body></html>"
)
expect(opened.is_ok()).to_be(true)

val attacked = session.eval_script(
    "location.href = 'https://evil.test/landing'; localStorage.planted = 'yes'; document.cookie = 'planted=yes; Path=/';"
)
expect(attacked.is_ok()).to_be(true)
expect(session.current_url).to_equal("https://evil.test/landing")
expect(session.document_url).to_equal("https://bank.test/app")

val evil = session.open_html(
    "https://evil.test/landing", "<html><body>evil</body></html>"
)
expect(evil.is_ok()).to_be(true)
expect(session.local_storage_item("planted")).to_be_nil()
expect(session.document_cookie()).to_equal("")

val bank = session.open_html(
    "https://bank.test/again", "<html><body>bank</body></html>"
)
expect(bank.is_ok()).to_be(true)
expect(session.local_storage_item("bank") ?? "").to_equal("secret")
expect(session.local_storage_item("planted") ?? "").to_equal("yes")
expect(session.document_cookie()).to_contain("planted=yes")
```

</details>

#### rejects cross-origin history state URLs without changing the document principal

- Push a cross-origin URL into same-document history
- var session = BrowserSession new
- "history pushState
   - Expected: session.current_url equals `https://bank.test/app`
   - Expected: session.document_url equals `https://bank.test/app`
   - Expected: session.history.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Push a cross-origin URL into same-document history")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://bank.test/app", "<html><body>bank</body></html>"
)
expect(opened.is_ok()).to_be(true)

val attacked = session.eval_script(
    "history.pushState(1, '', 'https://evil.test/planted')"
)
expect(attacked.is_ok()).to_be(true)
expect(session.current_url).to_equal("https://bank.test/app")
expect(session.document_url).to_equal("https://bank.test/app")
expect(session.history.len()).to_equal(1)
expect(session.warnings).to_contain(
    "cross-origin history URL blocked: https://evil.test/planted"
)
```

</details>

#### blocks mixed-content and unvalidated cross-origin executable resources

- Open an HTTPS page containing mixed and cross-origin executable resources
- var session = BrowserSession new
   - Expected: opened.is_ok() is true
   - Expected: session.take_pending_request().is_none() is true
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open an HTTPS page containing mixed and cross-origin executable resources")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://safe.test/app",
    "<html><head><link rel='stylesheet' href='http://cdn.test/theme.css'></head><body><script src='http://cdn.test/app.js'></script><script type='module' src='https://other.test/module.js'></script></body></html>"
)
expect(opened.is_ok()).to_equal(true)
expect(session.take_pending_request().is_none()).to_equal(true)
expect(session.has_pending_requests()).to_equal(false)
val warnings = session.warnings.join("|")
expect(warnings).to_contain("stylesheet load error: mixed-content:")
expect(warnings).to_contain("external script error: mixed-content:")
expect(warnings).to_contain("module load error: cross-origin:")
```

</details>

#### allows registered HTTPS resources without host filesystem access

- Register and navigate to an in-memory HTTPS resource
- var session = BrowserSession new
- session register resource
   - Expected: result.is_ok() is true
   - Expected: session.current_url equals `https://example.test/page`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Register and navigate to an in-memory HTTPS resource")
var session = BrowserSession.new()
session.register_resource("https://example.test/page", "<html><body>safe</body></html>")
val result = session.begin_network_navigation("https://example.test/page", "GET", "", "", "")
expect(result.is_ok()).to_equal(true)
expect(session.current_url).to_equal("https://example.test/page")
```

</details>

#### escapes page-controlled title text before rebuilding render HTML

- Render a document after assigning markup-shaped title text
- var session = BrowserSession new
   - Expected: rendered does not contain `</title><style>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a document after assigning markup-shaped title text")
var session = BrowserSession.new()
session.open_html(
    "https://safe.test/app", "<html><head><title>Safe</title></head><body>Body</body></html>"
)
session.current_title = "</title><style>body{display:none}</style>"

val rendered = session.render_html_document()

expect(rendered.contains("</title><style>")).to_equal(false)
expect(rendered).to_contain("&lt;/title&gt;&lt;style&gt;body{display:none}&lt;/style&gt;")
```

</details>

#### rejects a response whose URL differs from its inflight request

- Commit a network response from a URL different from its request
- var session = BrowserSession new
   - Expected: started.is_ok() is true
- Some
- Ok
   - Expected: session.current_url equals `about:blank`
   - Expected: session.cookies.count() equals `0`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Commit a network response from a URL different from its request")
var session = BrowserSession.new()
val started = session.begin_network_navigation("https://example.test/page", "GET", "", "", "")
expect(started.is_ok()).to_equal(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: request.kind,
            url: "https://attacker.test/page",
            status: 200,
            headers: "Set-Cookie: stolen=yes; Secure; HttpOnly",
            body: "<html><body>attacker</body></html>",
            error: ""
        ))
        match committed:
            Ok(_): fail("Expected mismatched response URL to be rejected")
            Err(e): expect(e).to_contain("response URL mismatch")
        expect(session.current_url).to_equal("about:blank")
        expect(session.cookies.count()).to_equal(0)
        val retry = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "",
                body: "<html><body>safe</body></html>",
                error: ""
            )
        )
        expect(retry.is_ok()).to_be(true)
        expect(session.current_body_html).to_contain("safe")
    nil:
        fail("Expected pending HTTPS document request")
```

</details>

#### blocks cross-origin page fetches before they reach the host network

- Issue repeated cross-origin fetches from page script
- var session = BrowserSession new
- "<html><body><script>var outcome = 'pending'; fetch
   - Expected: session.take_pending_request().is_none() is true
- "fetch
   - Expected: session.warnings.len() equals `1`
- Ok
- JsValue String
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Issue repeated cross-origin fetches from page script")
var session = BrowserSession.new()
session.open_html(
    "https://safe.test/app",
    "<html><body><script>var outcome = 'pending'; fetch('https://evil.test/private').catch(function(e) { outcome = e; })</script></body></html>"
)

expect(session.take_pending_request().is_none()).to_equal(true)
expect(session.warnings).to_contain("cross-origin fetch blocked: https://evil.test/private")
var repeat = 0
while repeat < 32:
    val _ = session.eval_script(
        "fetch('https://evil.test/private')"
    )
    repeat = repeat + 1
expect(session.warnings.len()).to_equal(1)
match session.eval_script("outcome"):
    Ok(value):
        match value:
            JsValue.String(message):
                expect(message).to_contain("cross-origin:https://evil.test/private")
            _:
                fail("Expected blocked fetch rejection text")
    Err(e):
        fail("Expected blocked cross-origin fetch to reject: {e}")
```

</details>

#### bounds and deduplicates retained browser warnings

- Append duplicate, excessive, and oversized browser warnings
- var session = BrowserSession new
- session  append warning
- session  append warning
   - Expected: session.warnings.len() equals `1`
- session  append warning
   - Expected: session.warnings.len() equals `128`
- var oversized = BrowserSession new
- oversized  append warning
   - Expected: oversized.warnings[0].len() equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Append duplicate, excessive, and oversized browser warnings")
var session = BrowserSession.new()
session._append_warning("duplicate")
session._append_warning("duplicate")
expect(session.warnings.len()).to_equal(1)
var index = 0
while index < 256:
    session._append_warning("blocked warning {index}")
    index = index + 1
expect(session.warnings.len()).to_equal(128)

var oversized_text = ""
index = 0
while index < 129:
    oversized_text = oversized_text +
        "abcdefghijklmnopqrstuvwxyz012345"
    index = index + 1
var oversized = BrowserSession.new()
oversized._append_warning(oversized_text)
expect(oversized.warnings[0].len()).to_equal(4096)
```

</details>

#### bounds active-load warnings before finalization

- Fail enough active subresource loads to exceed warning limits
- var session = BrowserSession new
- Some
- fail
- Some
   - Expected: load.warnings.len() equals `128`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail enough active subresource loads to exceed warning limits")
var html = "<html><body>"
var index = 0
while index < 130:
    html = html + "<script src='/bad-{index}.js'></script>"
    index = index + 1
html = html + "</body></html>"

var session = BrowserSession.new()
expect(session.open_html(
    "https://safe.test/app", html
).is_ok()).to_be(true)
index = 0
while index < 129:
    match session.take_pending_request():
        Some(request):
            val error = "error-{index}-" + "x".repeat(5000)
            expect(session.commit_network_response(
                BrowserResponse.create(
                    request_id: request.id,
                    kind: request.kind,
                    url: request.url,
                    status: 0,
                    headers: "",
                    body: "",
                    error: error
                )
            ).is_ok()).to_be(true)
        nil:
            fail("Expected hostile script request {index}")
    index = index + 1

match session.active_load:
    Some(load):
        expect(load.warnings.len()).to_equal(128)
        for warning in load.warnings:
            expect(warning.len()).to_be_less_than(4097)
    nil:
        fail("Expected the final script request to keep loading active")
```

</details>

#### still exports same-origin page fetches

- Issue a relative same-origin fetch from page script
- var session = BrowserSession new
- "<html><body><script>fetch
- Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://safe.test/ok`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Issue a relative same-origin fetch from page script")
var session = BrowserSession.new()
session.open_html(
    "https://safe.test/app",
    "<html><body><script>fetch('/ok')</script></body></html>"
)

match session.take_pending_request():
    Some(request):
        expect(request.kind).to_equal("fetch")
        expect(request.url).to_equal("https://safe.test/ok")
    nil:
        fail("Expected same-origin fetch request")
```

</details>

#### enforces document CSP before style script and fetch dispatch

- Load a document whose CSP blocks style, script, and fetch dispatch
- var session = BrowserSession new
   - Expected: started.is_ok() is true
- Some
- body: "<html><head><style>body{background:#f00}</style><link rel='stylesheet' href='/theme css'></head><body><script>document title='inline allowed'; fetch
   - Expected: committed.is_ok() is true
- fail
   - Expected: session.take_pending_request().is_none() is true
   - Expected: session.current_title equals `inline allowed`
   - Expected: session.current_style_html equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load a document whose CSP blocks style, script, and fetch dispatch")
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "https://safe.test/app", "GET", "", "", ""
)
expect(started.is_ok()).to_equal(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "Content-Security-Policy: style-src 'none'; style-src *; script-src 'unsafe-inline'; connect-src *\nContent-Security-Policy: connect-src 'none'",
                body: "<html><head><style>body{background:#f00}</style><link rel='stylesheet' href='/theme.css'></head><body><script>document.title='inline allowed'; fetch('/private')</script><script src='/app.js'></script></body></html>",
                error: ""
            )
        )
        expect(committed.is_ok()).to_equal(true)
    nil:
        fail("Expected CSP document request")

expect(session.take_pending_request().is_none()).to_equal(true)
expect(session.current_title).to_equal("inline allowed")
expect(session.current_style_html).to_equal("")
val warnings = session.warnings.join("|")
expect(warnings).to_contain("CSP blocked inline style")
expect(warnings).to_contain("CSP blocked style: https://safe.test/theme.css")
expect(warnings).to_contain("CSP blocked script: https://safe.test/app.js")
expect(warnings).to_contain("CSP blocked fetch: https://safe.test/private")
```

</details>

#### intersects bounded header sandbox capabilities and ignores meta sandbox

- Parse intersecting header sandboxes alongside a meta sandbox
   - Expected: meta equals `script-src 'unsafe-inline'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse intersecting header sandboxes alongside a meta sandbox")
val bare = browser_csp_header_sandbox("sandbox")
val allow_scripts = browser_csp_header_sandbox(
    "sandbox allow-scripts allow-forms\nsandbox allow-forms"
)
val comma_intersection = browser_csp_header_sandbox(
    "sandbox allow-scripts, sandbox allow-forms"
)
val first_duplicate = browser_csp_header_sandbox(
    "sandbox allow-scripts; sandbox"
)
val meta = browser_meta_content_security_policy(
    "sandbox allow-scripts; script-src 'unsafe-inline'"
)

expect(bare.active).to_be(true)
expect(bare.allow_scripts).to_be(false)
expect(bare.allow_forms).to_be(false)
expect(bare.allow_same_origin).to_be(false)
expect(bare.allow_popups).to_be(false)
expect(bare.allow_top_navigation).to_be(false)
expect(allow_scripts.active).to_be(true)
expect(allow_scripts.allow_scripts).to_be(false)
expect(allow_scripts.allow_forms).to_be(true)
expect(comma_intersection.allow_scripts).to_be(false)
expect(comma_intersection.allow_forms).to_be(false)
expect(first_duplicate.allow_scripts).to_be(true)
expect(meta).to_equal("script-src 'unsafe-inline'")
```

</details>

#### blocks scripts under intersected header sandbox policies

- Load script content under intersected header sandbox policies
- var session = BrowserSession new
- Some
- fail
   - Expected: session.document_cookie() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load script content under intersected header sandbox policies")
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://safe.test/sandbox", "GET", "", "", ""
).is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        expect(session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: request.kind,
            url: request.url,
            status: 200,
            headers: (
                "Content-Security-Policy: sandbox allow-scripts\n" +
                "Content-Security-Policy: sandbox"
            ),
            body: (
                "<html><body><script>" +
                "document.title='escaped'; localStorage.secret='x';" +
                "document.cookie='sid=x; Path=/';" +
                "</script><script src='/escape.js'></script></body></html>"
            ),
            error: ""
        )).is_ok()).to_be(true)
    nil:
        fail("Expected sandbox document request")

expect(session.current_title).to_equal(
    "https://safe.test/sandbox"
)
expect(session.take_pending_request().is_none()).to_be(true)
expect(session.eval_script("document.title='late'").is_err()).to_be(
    true
)
expect(session.local_storage_item("secret").is_none()).to_be(true)
expect(session.document_cookie()).to_equal("")
expect(session.warnings.join("|")).to_contain(
    "CSP sandbox blocked script execution"
)
```

</details>

#### allows scripts without restoring sandboxed origin storage or navigation

- Run allowed script inside an opaque-origin sandbox
- var session = BrowserSession new
- Some
- fail
   - Expected: session.current_title equals `script-ran`
- Ok
   - Expected: origin equals `null`
- fail
- Ok
   - Expected: kind equals `undefined`
- fail
   - Expected: session.document_cookie() equals ``
   - Expected: session.current_url equals `https://safe.test/sandbox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run allowed script inside an opaque-origin sandbox")
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://safe.test/sandbox", "GET", "", "", ""
).is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        expect(session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: request.kind,
            url: request.url,
            status: 200,
            headers: (
                "Content-Security-Policy: sandbox allow-scripts;" +
                " script-src 'unsafe-inline'"
            ),
            body: (
                "<html><body><script>" +
                "document.title='script-ran';" +
                "document.cookie='sid=x; Path=/';" +
                "location.href='/escape';" +
                "</script></body></html>"
            ),
            error: ""
        )).is_ok()).to_be(true)
    nil:
        fail("Expected allow-scripts sandbox document request")

expect(session.current_title).to_equal("script-ran")
match session.eval_script("location.origin"):
    Ok(JsValue.String(origin)):
        expect(origin).to_equal("null")
    _:
        fail("Expected the sandboxed runtime origin")
match session.eval_script("typeof localStorage"):
    Ok(JsValue.String(kind)):
        expect(kind).to_equal("undefined")
    _:
        fail("Expected sandboxed storage to be absent")
expect(session.local_storage_item("secret").is_none()).to_be(true)
expect(session.document_cookie()).to_equal("")
expect(session.current_url).to_equal("https://safe.test/sandbox")
expect(session.has_pending_requests()).to_be(false)
```

</details>

#### blocks inline DOM handlers when sandbox does not allow scripts

- Dispatch an inline DOM handler in a script-blocked sandbox
- var session = BrowserSession new
   - Expected: dispatch.actions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch an inline DOM handler in a script-blocked sandbox")
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://safe.test/handler", "GET", "", "", ""
).is_ok()).to_be(true)
val document = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document.id, "document", document.url, 200,
    "Content-Security-Policy: sandbox; script-src 'unsafe-inline'",
    "<html><body><button id='go' " +
    "onclick='set-attr:data-fired=yes'>Go</button></body></html>",
    ""
)).is_ok()).to_be(true)

val dispatch = session.dispatch_dom_event(
    "go", "click", true, true
)
expect(dispatch.actions.len()).to_equal(0)
expect(session.render_html_document().contains(
    "data-fired=\"yes\""
)).to_be(false)
expect(session.warnings.join("|")).to_contain(
    "CSP blocked inline event handler"
)
```

</details>

#### carries an opaque cookie-free initiator on sandboxed fetch

- Issue a fetch from an opaque-origin sandbox with ambient cookies
- var session = BrowserSession new
- "fetch
   - Expected: fetch.kind equals `fetch`
   - Expected: fetch.initiator_origin equals `null`
   - Expected: fetch.site_for_cookies_url equals ``
   - Expected: fetch.credentials equals `omit`
   - Expected: fetch.script_cookie_writes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Issue a fetch from an opaque-origin sandbox with ambient cookies")
var session = BrowserSession.new()
expect(session.open_html(
    "https://safe.test/start", "<html><body>start</body></html>"
).is_ok()).to_be(true)
session.apply_set_cookie_header(
    "ambient=secret; Secure; Path=/", "https://safe.test/start"
)
expect(session.begin_network_navigation(
    "https://safe.test/sandbox-fetch", "GET", "", "", ""
).is_ok()).to_be(true)
val document = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document.id, "document", document.url, 200,
    "Content-Security-Policy: sandbox allow-scripts; " +
    "script-src 'unsafe-inline'",
    "<html><body><script>document.cookie='script=x';" +
    "fetch('/data', {credentials:'include'})</script></body></html>",
    ""
)).is_ok()).to_be(true)

val fetch = session.take_pending_request().unwrap()
expect(fetch.kind).to_equal("fetch")
expect(fetch.initiator_origin).to_equal("null")
expect(fetch.site_for_cookies_url).to_equal("")
expect(fetch.credentials).to_equal("omit")
expect(fetch.headers.lower().contains("cookie:")).to_be(false)
expect(fetch.script_cookie_writes.len()).to_equal(0)
```

</details>

#### ignores meta sandbox while retaining its source directives

- Parse a meta CSP containing sandbox and source directives
- var session = BrowserSession new
   - Expected: session.current_title equals `meta-ran`
- Ok
   - Expected: origin equals `https://safe.test`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a meta CSP containing sandbox and source directives")
var session = BrowserSession.new()
expect(session.open_html(
    "https://safe.test/meta",
    "<html><head><meta http-equiv='Content-Security-Policy'" +
    " content=\"sandbox; script-src 'unsafe-inline'\"></head>" +
    "<body><script>document.title='meta-ran'</script></body></html>"
).is_ok()).to_be(true)
expect(session.current_title).to_equal("meta-ran")
match session.eval_script("location.origin"):
    Ok(JsValue.String(origin)):
        expect(origin).to_equal("https://safe.test")
    _:
        fail("Expected meta sandbox to leave the normal origin")
```

</details>

#### rechecks CSP before following style and script redirects

- Redirect admitted style and script requests to CSP-blocked URLs
- var session = BrowserSession new
- Some
- fail
- Some
   - Expected: style_request.kind equals `style`
- fail
- Some
   - Expected: script_request.kind equals `script`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Redirect admitted style and script requests to CSP-blocked URLs")
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "https://safe.test/app", "GET", "", "", ""
)
expect(started.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "Content-Security-Policy: style-src 'self'; script-src 'self'",
                body: "<html><head><link rel='stylesheet' href='/theme.css'></head><body><script src='/app.js'></script></body></html>",
                error: ""
            )
        )
        expect(committed.is_ok()).to_be(true)
    nil:
        fail("Expected CSP redirect document request")

match session.take_pending_request():
    Some(style_request):
        expect(style_request.kind).to_equal("style")
        expect(style_request.url).to_equal(
            "https://safe.test/theme.css"
        )
        val redirected = session.commit_network_response(
            BrowserResponse.create(
                request_id: style_request.id,
                kind: style_request.kind,
                url: style_request.url,
                status: 302,
                headers: "Location: https://evil.test/theme.css",
                body: "",
                error: ""
            )
        )
        expect(redirected.is_ok()).to_be(true)
    nil:
        fail("Expected same-origin stylesheet request")

match session.take_pending_request():
    Some(script_request):
        expect(script_request.kind).to_equal("script")
        expect(script_request.url).to_equal(
            "https://safe.test/app.js"
        )
        val redirected = session.commit_network_response(
            BrowserResponse.create(
                request_id: script_request.id,
                kind: script_request.kind,
                url: script_request.url,
                status: 302,
                headers: "Location: https://evil.test/app.js",
                body: "",
                error: ""
            )
        )
        expect(redirected.is_ok()).to_be(true)
    nil:
        fail("Expected same-origin script request")

expect(session.take_pending_request().is_none()).to_be(true)
val warnings = session.warnings.join("|")
expect(warnings).to_contain(
    "stylesheet load error: CSP blocked redirect: https://evil.test/theme.css"
)
expect(warnings).to_contain(
    "external script error: CSP blocked redirect: https://evil.test/app.js"
)
```

</details>

#### enforces CSP host-source paths before script dispatch

- Dispatch scripts against matching and nonmatching CSP host paths
- var session = BrowserSession new
- Some
- fail
- Some
   - Expected: script_request.kind equals `script`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 112 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch scripts against matching and nonmatching CSP host paths")
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "https://safe.test/app", "GET", "", "", ""
)
expect(started.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "Content-Security-Policy: script-src https://cdn.test/allowed/",
                body: "<html><body><script src='https://cdn.test/evil.js'></script><script src='https://cdn.test/allowed/app.js'></script></body></html>",
                error: ""
            )
        )
        expect(committed.is_ok()).to_be(true)
    nil:
        fail("Expected CSP path document request")

match session.take_pending_request():
    Some(script_request):
        expect(script_request.kind).to_equal("script")
        expect(script_request.url).to_equal(
            "https://cdn.test/allowed/app.js"
        )
    nil:
        fail("Expected script within the CSP source path")
expect(session.warnings).to_contain(
    "CSP blocked script: https://cdn.test/evil.js"
)
expect(browser_csp_allows(
    "script-src HTTPS://cdn.test/allowed/",
    "script-src",
    "https://safe.test/app",
    "https://cdn.test/allowed/upper.js",
    false
)).to_be(true)
expect(browser_csp_allows(
    "script-src https://cdn.test/exact.js",
    "script-src",
    "https://safe.test/app",
    "https://cdn.test/exact.js?version=1",
    false
)).to_be(true)
expect(browser_csp_allows(
    "script-src https://cdn.test/exact.js",
    "script-src",
    "https://safe.test/app",
    "https://cdn.test/exact.js/child",
    false
)).to_be(false)
expect(browser_csp_allows(
    "script-src https://cdn.test/",
    "script-src",
    "https://safe.test/app",
    "https://cdn.test/any/path.js",
    false
)).to_be(true)
expect(browser_csp_source_matches_url(
    "HTTPS://cdn.test/exact.js",
    "https://CDN.test/exact.js?version=1#loaded"
)).to_be(true)
expect(browser_csp_source_matches_url(
    "https://cdn.test/allowed/",
    "https://cdn.test/evil.js"
)).to_be(false)
expect(browser_csp_source_matches_url(
    "https://cdn.test/allowed/",
    "https://cdn.test/allowed/../evil.js"
)).to_be(false)
expect(browser_csp_source_matches_url(
    "https://cdn.test/allowed/",
    "https://cdn.test/allowed/%2e%2e/evil.js"
)).to_be(false)
expect(browser_csp_source_matches_url(
    "https://cdn.test/allowed/",
    "https://cdn.test/allowed/.%2E/evil.js"
)).to_be(false)
expect(browser_csp_source_matches_url(
    "https://cdn.test/allowed/",
    "https://cdn.test/../../allowed/file.js"
)).to_be(true)
expect(browser_csp_source_matches_url(
    "https://cdn.test/evil.js",
    "https://cdn.test/../../evil.js"
)).to_be(true)
expect(browser_csp_source_matches_url(
    "https://cdn.test/allowed/",
    "https://cdn.test/allowed//../file.js"
)).to_be(true)
expect(browser_csp_source_matches_url(
    "https://cdn.test/allowed/",
    "https://cdn.test/allowed/%2e%2e%2fevil.js"
)).to_be(true)
expect(browser_csp_allows_after_redirect(
    "script-src https://cdn.test/exact.js",
    "script-src",
    "https://safe.test/app",
    "https://cdn.test/redirected.js",
    false
)).to_be(true)
expect(browser_csp_allows_after_redirect(
    "script-src https://cdn.test/exact.js",
    "script-src",
    "https://safe.test/app",
    "https://evil.test/redirected.js",
    false
)).to_be(false)
```

</details>

#### upgrades HSTS hosts and subdomains until max-age expires

- Record HSTS and navigate through covered hosts before and after expiry
- var session = BrowserSession new
   - Expected: started.is_ok() is true
- Some
   - Expected: committed.is_ok() is true
- fail
   - Expected: upgraded.is_ok() is true
- Some
   - Expected: request.url equals `https://sub.secure.test/next`
- fail
- Ok
   - Expected: target equals `https://secure.test/reload`
- Err
- fail
   - Expected: expired.is_ok() is true
- Some
   - Expected: request.url equals `http://secure.test/after-expiry`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 72 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record HSTS and navigate through covered hosts before and after expiry")
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "https://secure.test/start", "GET", "", "", ""
)
expect(started.is_ok()).to_equal(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "Strict-Transport-Security: max-age=1; includeSubDomains",
                body: "<html><body>secure</body></html>",
                error: ""
            )
        )
        expect(committed.is_ok()).to_equal(true)
    nil:
        fail("Expected HTTPS document request")

val upgraded = session.begin_network_navigation(
    "http://sub.secure.test/next", "GET", "", "", ""
)
expect(upgraded.is_ok()).to_equal(true)
match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal("https://sub.secure.test/next")
    nil:
        fail("Expected HSTS-upgraded request")
expect(session.open_html(
    "http://secure.test/reload", "<html><body>reload</body></html>"
).is_ok()).to_be(true)
match session.reload_target_url():
    Ok(target):
        expect(target).to_equal("https://secure.test/reload")
    Err(reason):
        fail("Expected HSTS-upgraded reload target: {reason}")
expect(session._hsts_upgrade_url(
    "HTTP://SUB.SECURE.TEST:80/Port?x=1"
)).to_equal("https://sub.secure.test/Port?x=1")
expect(session._hsts_upgrade_url(
    "http://sub.secure.test:8080/other"
)).to_equal("https://sub.secure.test:8080/other")
expect(session._hsts_upgrade_url(
    "secure.test"
)).to_equal("secure.test")
expect(session._hsts_upgrade_url(
    "http://secure.test:nope/path"
)).to_equal("http://secure.test:nope/path")
expect(session._hsts_upgrade_url(
    "http://evilsecure.test/path"
)).to_equal("http://evilsecure.test/path")
expect(session._hsts_upgrade_url(
    "HTTPS://SECURE.TEST:80/path"
)).to_equal("HTTPS://SECURE.TEST:80/path")
expect(session._hsts_upgrade_url(
    "http://secure.test"
)).to_equal("https://secure.test/")

val _ = session.advance_time(1001)
val expired = session.begin_network_navigation(
    "http://secure.test/after-expiry", "GET", "", "", ""
)
expect(expired.is_ok()).to_equal(true)
match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal("http://secure.test/after-expiry")
    nil:
        fail("Expected request after HSTS expiry")
```

</details>

#### ignores signed HSTS max-age but accepts zero clearing

- Apply signed, clearing, and malformed HSTS max-age directives
- var session = BrowserSession new
- Some
- fail
- Some
- fail
- Some
   - Expected: request.url equals `https://secure.test/next`
- fail
- Some
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 77 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply signed, clearing, and malformed HSTS max-age directives")
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "https://secure.test/start", "GET", "", "", ""
)
expect(started.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "Strict-Transport-Security: max-age=10",
                body: "<html><body>secure</body></html>",
                error: ""
            )
        )
        expect(committed.is_ok()).to_be(true)
    nil:
        fail("Expected initial HTTPS document request")

val refreshed = session.begin_network_navigation(
    "https://secure.test/refresh", "GET", "", "", ""
)
expect(refreshed.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "Strict-Transport-Security: max-age=-1",
                body: "<html><body>still secure</body></html>",
                error: ""
            )
        )
        expect(committed.is_ok()).to_be(true)
    nil:
        fail("Expected HTTPS refresh request")

val next = session.begin_network_navigation(
    "http://secure.test/next", "GET", "", "", ""
)
expect(next.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal("https://secure.test/next")
        val cleared = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "Strict-Transport-Security: max-age=0",
                body: "<html><body>cleared</body></html>",
                error: ""
            )
        )
        expect(cleared.is_ok()).to_be(true)
    nil:
        fail("Expected retained HSTS-upgraded request")

val after_clear = session.begin_network_navigation(
    "http://secure.test/after-clear", "GET", "", "", ""
)
expect(after_clear.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal(
            "http://secure.test/after-clear"
        )
    nil:
        fail("Expected HTTP request after HSTS clearing")
```

</details>

#### restores only valid unexpired HSTS state across sessions

- Restore persisted HSTS entries with mixed validity and expiry
- var session = BrowserSession new
- BrowserHstsSnapshot create
   - Expected: accepted equals `1`
   - Expected: saved.entries.len() equals `1`
   - Expected: saved.entries[0].host equals `secure.test`
   - Expected: saved.entries[0].expires_at_unix_ms equals `101000`
   - Expected: upgraded.is_ok() is true
- Some
   - Expected: request.url equals `https://sub.secure.test/next`
- fail
   - Expected: expired.is_ok() is true
- Some
   - Expected: request.url equals `http://secure.test/after-expiry`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Restore persisted HSTS entries with mixed validity and expiry")
var entries: [BrowserHstsSnapshotEntry] = []
entries.push(BrowserHstsSnapshotEntry(
    host: "secure.test",
    received_at_unix_ms: 99500,
    expires_at_unix_ms: 101000,
    include_subdomains: true
))
entries.push(BrowserHstsSnapshotEntry(
    host: "secure.test",
    received_at_unix_ms: 99500,
    expires_at_unix_ms: 102000,
    include_subdomains: false
))
entries.push(BrowserHstsSnapshotEntry(
    host: "com",
    received_at_unix_ms: 99500,
    expires_at_unix_ms: 101000,
    include_subdomains: true
))
entries.push(BrowserHstsSnapshotEntry(
    host: "127.0.0.1",
    received_at_unix_ms: 99500,
    expires_at_unix_ms: 101000,
    include_subdomains: true
))
for invalid_host in [
    "bad host", " secure.test", "user@secure.test", "secure.test:443",
    "-secure.test", "secure-.test", ".secure.test"
]:
    entries.push(BrowserHstsSnapshotEntry(
        host: invalid_host,
        received_at_unix_ms: 99500,
        expires_at_unix_ms: 101000,
        include_subdomains: true
    ))
entries.push(BrowserHstsSnapshotEntry(
    host: "expired.test",
    received_at_unix_ms: 98000,
    expires_at_unix_ms: 99000,
    include_subdomains: true
))

var session = BrowserSession.new()
val accepted = session.load_hsts_snapshot(
    BrowserHstsSnapshot.create(entries), 100000
)
expect(accepted).to_equal(1)
val saved = session.hsts_snapshot(100000)
expect(saved.entries.len()).to_equal(1)
expect(saved.entries[0].host).to_equal("secure.test")
expect(saved.entries[0].expires_at_unix_ms).to_equal(101000)

val upgraded = session.begin_network_navigation(
    "http://sub.secure.test/next", "GET", "", "", ""
)
expect(upgraded.is_ok()).to_equal(true)
match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal("https://sub.secure.test/next")
    nil:
        fail("Expected restored HSTS-upgraded request")

val _ = session.advance_time(1001)
val expired = session.begin_network_navigation(
    "http://secure.test/after-expiry", "GET", "", "", ""
)
expect(expired.is_ok()).to_equal(true)
match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal("http://secure.test/after-expiry")
    nil:
        fail("Expected request after restored HSTS expiry")
```

</details>

#### rejects JavaScript fetches after the document request budget is spent

- Issue JavaScript fetches after exhausting the document request budget
- var session = BrowserSession new
- session open html
- "var outcome = 'pending'; fetch
   - Expected: queued.is_ok() is true
   - Expected: session.take_pending_request().is_none() is true
- Ok
- JsValue String
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Issue JavaScript fetches after exhausting the document request budget")
var session = BrowserSession.new()
session.open_html("https://safe.test/app", "<html><body>safe</body></html>")
session.subresource_request_count = 1024
val queued = session.eval_script(
    "var outcome = 'pending'; fetch('/overflow').catch(function(e) { outcome = e; });"
)
expect(queued.is_ok()).to_equal(true)
expect(session.take_pending_request().is_none()).to_equal(true)
match session.eval_script("outcome"):
    Ok(value):
        match value:
            JsValue.String(message):
                expect(message).to_contain(
                    "resource-limit:too-many-subresource-requests"
                )
            _:
                fail("Expected request-budget rejection text")
    Err(e):
        fail("Expected request-budget rejection to settle: {e}")
```

</details>

#### keeps HttpOnly and transport cookie state outside page-visible JS

- Store transport and HttpOnly cookies, then inspect page-visible state
- var session = BrowserSession new
- Some
- fail
   - Expected: session.document_cookie() equals `public=yes`
- Ok
- JsValue String
   - Expected: cookie_text equals `public=yes`
- fail
- Err
- fail
- Ok
- JsValue String
   - Expected: kind equals `undefined`
- fail
- Err
- fail
- Some
   - Expected: request.url equals `https://safe.test/next`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store transport and HttpOnly cookies, then inspect page-visible state")
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "https://safe.test/app", "GET", "", "", ""
)
expect(started.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: request.kind,
            url: request.url,
            status: 200,
            headers: "Set-Cookie: secret=token; Path=/; Secure; HttpOnly\nSet-Cookie: public=yes; Path=/; Secure",
            body: "<html><body>safe</body></html>",
            error: ""
        ))
        expect(committed.is_ok()).to_be(true)
    nil:
        fail("Expected document request")

expect(session.document_cookie()).to_equal("public=yes")
match session.eval_script("document.cookie"):
    Ok(value):
        match value:
            JsValue.String(cookie_text):
                expect(cookie_text).to_equal("public=yes")
            _:
                fail("Expected document.cookie text")
    Err(e):
        fail("Expected document.cookie read: {e}")

match session.eval_script("typeof __simple_modules"):
    Ok(value):
        match value:
            JsValue.String(kind):
                expect(kind).to_equal("undefined")
            _:
                fail("Expected typeof result")
    Err(e):
        fail("Expected internal-module visibility check: {e}")

val forged = session.eval_script("window.__simple_cookie_header = 'forged=yes'")
expect(forged.is_ok()).to_be(true)
val fetched = session.eval_script("fetch('/next')")
expect(fetched.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal("https://safe.test/next")
        expect(request.headers).to_contain("Cookie: secret=token; public=yes")
        expect(request.headers.contains("forged=yes")).to_be(false)
    nil:
        fail("Expected sanitized same-origin fetch")
```

</details>

#### rejects cookie source controls and delegates serialized byte limits

- Set cookies containing source controls and boundary-sized serialized values
- var session = BrowserSession new
- "long=accepted; ignored=" + "x" repeat
- session apply set cookie header
- session apply set cookie header
- session apply set cookie header
   - Expected: session.document_cookie() equals `long=accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set cookies containing source controls and boundary-sized serialized values")
var session = BrowserSession.new()
session.open_html(
    "https://safe.test/", "<html><body>safe</body></html>"
)
session.apply_set_cookie_header(
    "long=accepted; ignored=" + "x".repeat(5000)
)
session.apply_set_cookie_header("cr=bad\rInjected=yes")
session.apply_set_cookie_header("lf=bad\nInjected=yes")
session.apply_set_cookie_header("nul=bad\0Injected=yes")

expect(session.document_cookie()).to_equal("long=accepted")
expect(session.cookie_header_for_request(
    "https://safe.test/"
)).to_equal("long=accepted")
```

</details>

#### defaults cookie Path to the response URL directory

- Store a response cookie without an explicit Path
- var session = BrowserSession new
- Some
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store a response cookie without an explicit Path")
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "https://safe.test/account/login", "GET", "", "", ""
)
expect(started.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        val committed = session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: request.kind,
                url: request.url,
                status: 200,
                headers: "Set-Cookie: account=private; Secure",
                body: "<html><body>account</body></html>",
                error: ""
            )
        )
        expect(committed.is_ok()).to_be(true)
    nil:
        fail("Expected account document request")

expect(session.cookie_header_for_request(
    "https://safe.test/account/next"
)).to_equal("account=private")
expect(session.cookie_header_for_request(
    "https://safe.test/public"
)).to_equal("")
```

</details>

#### rejects a fetch redirect that crosses the page origin

- Redirect a same-origin page fetch across origins
- var session = BrowserSession new
- "<html><body><script>var outcome = 'pending'; fetch
- Some
   - Expected: redirected.is_ok() is true
- fail
   - Expected: session.take_pending_request().is_none() is true
- Ok
- JsValue String
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Redirect a same-origin page fetch across origins")
var session = BrowserSession.new()
session.open_html(
    "https://safe.test/app",
    "<html><body><script>var outcome = 'pending'; fetch('/start').catch(function(e) { outcome = e; })</script></body></html>"
)
match session.take_pending_request():
    Some(request):
        val redirected = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 302,
            headers: "Location: https://evil.test/private",
            body: "",
            error: ""
        ))
        expect(redirected.is_ok()).to_equal(true)
    nil:
        fail("Expected initial same-origin fetch")

expect(session.take_pending_request().is_none()).to_equal(true)
match session.eval_script("outcome"):
    Ok(value):
        match value:
            JsValue.String(message):
                expect(message).to_contain("cross-origin:https://evil.test/private")
            _:
                fail("Expected redirected fetch rejection text")
    Err(e):
        fail("Expected redirected fetch to reject: {e}")
```

</details>

#### bounds recursive microtask work in one browser flush

- Run a recursively replenished microtask queue
- var session = BrowserSession new
- "var hits = 0; function again
   - Expected: result.is_ok() is true
   - Expected: session.current_title equals `8000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a recursively replenished microtask queue")
var session = BrowserSession.new()
session.open_html(
    "https://safe.test/app",
    "<html><head><title>Initial</title></head><body>Ready</body></html>"
)

val result = session.eval_script(
    "var hits = 0; function again() { hits = hits + 1; document.title = '' + hits; Promise.resolve().then(again); } Promise.resolve().then(again);"
)

expect(result.is_ok()).to_equal(true)
expect(session.current_title).to_equal("8000")
```

</details>

#### strips forbidden and CR-injected request headers

- Issue a fetch with forbidden and CR-injected request headers
- var session = BrowserSession new
- Some
   - Expected: request.headers equals `X-Trace: kept`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Issue a fetch with forbidden and CR-injected request headers")
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "https://safe.test/", "GET",
    "Host: evil.test\nOrigin: https://evil.test\nContent-Length: 999\nX-Bad: ok\rInjected: yes\nX-Trace: kept",
    "", ""
)
expect(started.is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        expect(request.headers).to_equal("X-Trace: kept")
    nil:
        fail("Expected sanitized navigation request")
```

</details>

#### leaves hosted cookie attachment to the broker

- Export a hosted request while page cookies are present
- var session = BrowserSession new
- session open html
- session apply set cookie header
- Some
- fail
- nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Export a hosted request while page cookies are present")
var session = BrowserSession.new()
session.broker_network_policy = true
session.open_html("https://safe.test/app", "<html><body>safe</body></html>")
session.apply_set_cookie_header("sid=secret; Secure; Path=/", "https://safe.test/app")

val _ = session.eval_script("fetch('https://safe.test:8443/omit', { credentials: 'omit' })")
match session.take_pending_request():
    Some(request):
        expect(request.headers.contains("Cookie:")).to_be(false)
        val committed = session.commit_network_response(BrowserResponse.create(
            request.id, request.kind, request.url, 200,
            "Set-Cookie: omitted=bad; Secure; Path=/", "ok", ""
        ))
        expect(committed.is_ok()).to_be(true)
    nil:
        fail("Expected omit request")
expect(session.cookie_header_for_request("https://safe.test/").contains("omitted=bad")).to_be(false)

val _ = session.eval_script("fetch('https://safe.test:8443/include', { credentials: 'include' })")
match session.take_pending_request():
    Some(request): expect(request.headers.contains("Cookie:")).to_be(false)
    nil: fail("Expected include request")
```

</details>

#### retains admitted hosted script cookie setters in order

- Run multiple admitted hosted script cookie assignments
- var session = BrowserSession new
   - Expected: writes.len() equals `2`
   - Expected: writes[0] equals `first=one; Path=/`
   - Expected: writes[1] equals `second=two; Path=/`
   - Expected: session.take_pending_script_cookie_writes().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run multiple admitted hosted script cookie assignments")
var session = BrowserSession.new()
session.broker_network_policy = true
session.open_html(
    "https://safe.test/", "<html><body>safe</body></html>"
)
val _ = session.eval_script(
    "document.cookie = 'first=one; Path=/'"
)
val _ = session.eval_script(
    "document.cookie = 'second=two; Path=/'"
)
val _ = session.eval_script(
    "document.cookie = 'hidden=no; HttpOnly; Path=/'"
)
val writes = session.take_pending_script_cookie_writes()
expect(writes.len()).to_equal(2)
expect(writes[0]).to_equal("first=one; Path=/")
expect(writes[1]).to_equal("second=two; Path=/")
expect(session.take_pending_script_cookie_writes().len()).to_equal(0)
expect(session.document_cookie().contains("hidden=no")).to_be(false)
```

</details>

#### keeps hosted cookie setters ordered around fetch calls

- Set hosted cookies before and after a scripted fetch
- var session = BrowserSession new
- "fetch
- "fetch
- nil: fail
- nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set hosted cookies before and after a scripted fetch")
var session = BrowserSession.new()
session.broker_network_policy = true
session.open_html(
    "https://safe.test/", "<html><body>safe</body></html>"
)
val _ = session.eval_script(
    "document.cookie = 'first=one; Path=/'; " +
    "fetch('/one'); " +
    "document.cookie = 'second=two; Path=/'; " +
    "fetch('/two')"
)
val first = session.take_pending_request()
val second = session.take_pending_request()
match first:
    Some(request): expect(request.script_cookie_writes).to_equal([
        "first=one; Path=/"
    ])
    nil: fail("Expected first fetch request")
match second:
    Some(request): expect(request.script_cookie_writes).to_equal([
        "second=two; Path=/"
    ])
    nil: fail("Expected second fetch request")
```

</details>

#### surfaces hosted script cookie setter overflow

- Exceed the hosted script cookie setter queue limit
- var session = BrowserSession new
   - Expected: writes.len() equals `32`
   - Expected: writes[0] equals `queued0=yes; Path=/`
   - Expected: writes[31] equals `queued31=yes; Path=/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exceed the hosted script cookie setter queue limit")
var session = BrowserSession.new()
session.broker_network_policy = true
session.open_html(
    "https://safe.test/", "<html><body>safe</body></html>"
)
var i: i64 = 0
while i < 33:
    val _ = session.eval_script(
        "document.cookie = 'queued{i}=yes; Path=/'"
    )
    i = i + 1
val writes = session.take_pending_script_cookie_writes()
expect(writes.len()).to_equal(32)
expect(writes[0]).to_equal("queued0=yes; Path=/")
expect(writes[31]).to_equal("queued31=yes; Path=/")
expect(session.document_cookie().contains("queued31=yes")).to_be(true)
expect(session.document_cookie().contains("queued32=yes")).to_be(false)
expect(session.script_cookie_write_overflow).to_be(true)
```

</details>

#### prevents script from replacing an HttpOnly cookie

- Attempt to replace an HttpOnly cookie from page script
- var session = BrowserSession new
- session open html
- session apply set cookie header
   - Expected: session.document_cookie() equals ``
   - Expected: session.cookie_header_for_request("https://safe.test/") equals `sid=secret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt to replace an HttpOnly cookie from page script")
var session = BrowserSession.new()
session.open_html("https://safe.test/", "<html><body>safe</body></html>")
session.apply_set_cookie_header("sid=secret; Secure; HttpOnly; Path=/")
val _ = session.eval_script("document.cookie = 'sid=visible; Path=/'")
expect(session.document_cookie()).to_equal("")
expect(session.cookie_header_for_request("https://safe.test/")).to_equal("sid=secret")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_security_boundary_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession production security boundary.
- BrowserSession production security boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
