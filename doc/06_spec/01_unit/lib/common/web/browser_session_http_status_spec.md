# Browser Session Http Status Specification

> Tests covering BrowserSession HTTP status semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Http Status Specification

## Scenarios

### BrowserSession HTTP status semantics

#### maps unknown valid HTTP status codes to their RFC 9110 class semantics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps unknown valid HTTP status codes to their RFC 9110 class semantics
   - Expected: _commit_fetch_status(success_session, 299, "ok") equals `299:OK:true`
   - Expected: _commit_fetch_status(client_error_session, 471, "bad") equals `471:Bad Request:false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps unknown valid HTTP status codes to their RFC 9110 class semantics")
var success_session = BrowserSession.new()
success_session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = ''; window.fetch('/unknown-2xx').then(function(r) { meta = r.status + ':' + r.statusText + ':' + r.ok; });</script></body></html>"
)
expect(_commit_fetch_status(success_session, 299, "ok")).to_equal("299:OK:true")

var client_error_session = BrowserSession.new()
client_error_session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = ''; window.fetch('/unknown-4xx').then(function(r) { meta = r.status + ':' + r.statusText + ':' + r.ok; });</script></body></html>"
)
expect(_commit_fetch_status(client_error_session, 471, "bad")).to_equal("471:Bad Request:false")
```

</details>

#### processes invalid HTTP status codes as server-error class responses

- processes invalid HTTP status codes as server-error class responses
   - Expected: _commit_fetch_status(session, 701, "invalid") equals `701:Internal Server Error:false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes invalid HTTP status codes as server-error class responses")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = ''; window.fetch('/invalid-status').then(function(r) { meta = r.status + ':' + r.statusText + ':' + r.ok; });</script></body></html>"
)

expect(_commit_fetch_status(session, 701, "invalid")).to_equal("701:Internal Server Error:false")
```

</details>

#### follows same-origin temporary redirects before resolving browser fetch

- follows same-origin temporary redirects before resolving browser fetch
   - Expected: first_request.url equals `https://example.com/old`
   - Expected: first_request.method equals `GET`
   - Expected: second_request.url equals `https://example.com/new`
   - Expected: second_request.method equals `GET`
   - Expected: _display_js(value) equals `done:arrived:done:arrived`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("follows same-origin temporary redirects before resolving browser fetch")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/old').then(function(r) { return r.text(); }).then(function(t) { meta = 'done:' + t; document.body.textContent = meta; }).catch(function(err) { meta = 'error:' + err; });</script></body></html>"
)

match session.take_pending_request():
    Some(first_request):
        expect(first_request.url).to_equal("https://example.com/old")
        expect(first_request.method).to_equal("GET")
        val redirect_result = session.commit_network_response(BrowserResponse.create(
            request_id: first_request.id,
            kind: "fetch",
            url: first_request.url,
            status: 302,
            headers: "Location: /new\n",
            body: "redirect body",
            error: ""
        ))
        match redirect_result:
            Ok(_):
                match session.take_pending_request():
                    Some(second_request):
                        expect(second_request.url).to_equal("https://example.com/new")
                        expect(second_request.method).to_equal("GET")
                        val final_result = session.commit_network_response(BrowserResponse.create(
                            request_id: second_request.id,
                            kind: "fetch",
                            url: second_request.url,
                            status: 200,
                            headers: "",
                            body: "arrived",
                            error: ""
                        ))
                        match final_result:
                            Ok(_):
                                val result = session.eval_script("meta + ':' + document.body.textContent")
                                match result:
                                    Ok(value):
                                        expect(_display_js(value)).to_equal("done:arrived:done:arrived")
                                    Err(e):
                                        fail("Expected redirected fetch output to evaluate: {e}")
                            Err(e):
                                fail("Expected redirected fetch final response commit to succeed: {e}")
                    nil:
                        fail("Expected pending redirected fetch request after 302 Location response")
            Err(e):
                fail("Expected same-origin redirect response commit to settle: {e}")
    nil:
        fail("Expected initial pending fetch request for redirect")
```

</details>

#### preserves HEAD fetch method and exposes an empty response body

- preserves HEAD fetch method and exposes an empty response body
   - Expected: request.url equals `https://example.com/head-check`
   - Expected: request.method equals `HEAD`
   - Expected: _display_js(value) equals `head:0::head:0:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves HEAD fetch method and exposes an empty response body")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/head-check', { method: 'HEAD' }).then(function(r) { return r.text(); }).then(function(t) { meta = 'head:' + t.length + ':' + t; document.body.textContent = meta; }).catch(function(err) { meta = 'error:' + err; });</script></body></html>"
)

match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal("https://example.com/head-check")
        expect(request.method).to_equal("HEAD")
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Length: 11\n",
            body: "server-body",
            error: ""
        ))
        match committed:
            Ok(_):
                val result = session.eval_script("meta + ':' + document.body.textContent")
                match result:
                    Ok(value):
                        expect(_display_js(value)).to_equal("head:0::head:0:")
                    Err(e):
                        fail("Expected HEAD fetch empty-body output to evaluate: {e}")
            Err(e):
                fail("Expected HEAD fetch response commit to succeed: {e}")
    nil:
        fail("Expected pending HEAD fetch request")
```

</details>

#### rewrites POST to GET and drops the body for 303 fetch redirects

- rewrites POST to GET and drops the body for 303 fetch redirects
   - Expected: first_request.url equals `https://example.com/submit`
   - Expected: first_request.method equals `POST`
   - Expected: first_request.body equals `payload`
   - Expected: second_request.url equals `https://example.com/submitted`
   - Expected: second_request.method equals `GET`
   - Expected: second_request.body equals ``
   - Expected: second_request.content_type equals ``
   - Expected: _display_js(value) equals `see-other:accepted:see-other:accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rewrites POST to GET and drops the body for 303 fetch redirects")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/submit', { method: 'POST', headers: { 'Content-Type': 'text/plain' }, body: 'payload' }).then(function(r) { return r.text(); }).then(function(t) { meta = 'see-other:' + t; document.body.textContent = meta; }).catch(function(err) { meta = 'error:' + err; });</script></body></html>"
)

match session.take_pending_request():
    Some(first_request):
        expect(first_request.url).to_equal("https://example.com/submit")
        expect(first_request.method).to_equal("POST")
        expect(first_request.body).to_equal("payload")
        val redirect_result = session.commit_network_response(BrowserResponse.create(
            request_id: first_request.id,
            kind: "fetch",
            url: first_request.url,
            status: 303,
            headers: "Location: /submitted\n",
            body: "",
            error: ""
        ))
        match redirect_result:
            Ok(_):
                match session.take_pending_request():
                    Some(second_request):
                        expect(second_request.url).to_equal("https://example.com/submitted")
                        expect(second_request.method).to_equal("GET")
                        expect(second_request.body).to_equal("")
                        expect(second_request.content_type).to_equal("")
                        val final_result = session.commit_network_response(BrowserResponse.create(
                            request_id: second_request.id,
                            kind: "fetch",
                            url: second_request.url,
                            status: 200,
                            headers: "",
                            body: "accepted",
                            error: ""
                        ))
                        match final_result:
                            Ok(_):
                                val result = session.eval_script("meta + ':' + document.body.textContent")
                                match result:
                                    Ok(value):
                                        expect(_display_js(value)).to_equal("see-other:accepted:see-other:accepted")
                                    Err(e):
                                        fail("Expected 303 redirected POST output to evaluate: {e}")
                            Err(e):
                                fail("Expected 303 redirected final response commit to succeed: {e}")
                    nil:
                        fail("Expected redirected GET request after 303 POST response")
            Err(e):
                fail("Expected 303 redirect response commit to settle: {e}")
    nil:
        fail("Expected initial POST fetch request for 303 redirect")
```

</details>

#### preserves POST method and body for 307 fetch redirects

- preserves POST method and body for 307 fetch redirects
   - Expected: first_request.url equals `https://example.com/upload`
   - Expected: first_request.method equals `POST`
   - Expected: first_request.body equals `payload`
   - Expected: second_request.url equals `https://example.com/upload-target`
   - Expected: second_request.method equals `POST`
   - Expected: second_request.body equals `payload`
   - Expected: second_request.content_type equals `text/plain`
   - Expected: _display_js(value) equals `temporary:stored:temporary:stored`


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves POST method and body for 307 fetch redirects")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/upload', { method: 'POST', headers: { 'Content-Type': 'text/plain' }, body: 'payload' }).then(function(r) { return r.text(); }).then(function(t) { meta = 'temporary:' + t; document.body.textContent = meta; }).catch(function(err) { meta = 'error:' + err; });</script></body></html>"
)

match session.take_pending_request():
    Some(first_request):
        expect(first_request.url).to_equal("https://example.com/upload")
        expect(first_request.method).to_equal("POST")
        expect(first_request.body).to_equal("payload")
        val redirect_result = session.commit_network_response(BrowserResponse.create(
            request_id: first_request.id,
            kind: "fetch",
            url: first_request.url,
            status: 307,
            headers: "Location: /upload-target\n",
            body: "",
            error: ""
        ))
        match redirect_result:
            Ok(_):
                match session.take_pending_request():
                    Some(second_request):
                        expect(second_request.url).to_equal("https://example.com/upload-target")
                        expect(second_request.method).to_equal("POST")
                        expect(second_request.body).to_equal("payload")
                        expect(second_request.content_type).to_equal("text/plain")
                        val final_result = session.commit_network_response(BrowserResponse.create(
                            request_id: second_request.id,
                            kind: "fetch",
                            url: second_request.url,
                            status: 200,
                            headers: "",
                            body: "stored",
                            error: ""
                        ))
                        match final_result:
                            Ok(_):
                                val result = session.eval_script("meta + ':' + document.body.textContent")
                                match result:
                                    Ok(value):
                                        expect(_display_js(value)).to_equal("temporary:stored:temporary:stored")
                                    Err(e):
                                        fail("Expected 307 redirected POST output to evaluate: {e}")
                            Err(e):
                                fail("Expected 307 redirected final response commit to succeed: {e}")
                    nil:
                        fail("Expected redirected POST request after 307 response")
            Err(e):
                fail("Expected 307 redirect response commit to settle: {e}")
    nil:
        fail("Expected initial POST fetch request for 307 redirect")
```

</details>

#### preserves POST method and body for 308 fetch redirects

- preserves POST method and body for 308 fetch redirects
   - Expected: first_request.url equals `https://example.com/permanent-upload`
   - Expected: first_request.method equals `POST`
   - Expected: first_request.body equals `payload`
   - Expected: second_request.url equals `https://example.com/permanent-upload-target`
   - Expected: second_request.method equals `POST`
   - Expected: second_request.body equals `payload`
   - Expected: _display_js(value) equals `permanent:stored:permanent:stored`


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves POST method and body for 308 fetch redirects")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/permanent-upload', { method: 'POST', headers: { 'Content-Type': 'text/plain' }, body: 'payload' }).then(function(r) { return r.text(); }).then(function(t) { meta = 'permanent:' + t; document.body.textContent = meta; }).catch(function(err) { meta = 'error:' + err; });</script></body></html>"
)

match session.take_pending_request():
    Some(first_request):
        expect(first_request.url).to_equal("https://example.com/permanent-upload")
        expect(first_request.method).to_equal("POST")
        expect(first_request.body).to_equal("payload")
        val redirect_result = session.commit_network_response(BrowserResponse.create(
            request_id: first_request.id,
            kind: "fetch",
            url: first_request.url,
            status: 308,
            headers: "Location: /permanent-upload-target\n",
            body: "",
            error: ""
        ))
        match redirect_result:
            Ok(_):
                match session.take_pending_request():
                    Some(second_request):
                        expect(second_request.url).to_equal("https://example.com/permanent-upload-target")
                        expect(second_request.method).to_equal("POST")
                        expect(second_request.body).to_equal("payload")
                        val final_result = session.commit_network_response(BrowserResponse.create(
                            request_id: second_request.id,
                            kind: "fetch",
                            url: second_request.url,
                            status: 200,
                            headers: "",
                            body: "stored",
                            error: ""
                        ))
                        match final_result:
                            Ok(_):
                                val result = session.eval_script("meta + ':' + document.body.textContent")
                                match result:
                                    Ok(value):
                                        expect(_display_js(value)).to_equal("permanent:stored:permanent:stored")
                                    Err(e):
                                        fail("Expected 308 redirected POST output to evaluate: {e}")
                            Err(e):
                                fail("Expected 308 redirected final response commit to succeed: {e}")
                    nil:
                        fail("Expected redirected POST request after 308 response")
            Err(e):
                fail("Expected 308 redirect response commit to settle: {e}")
    nil:
        fail("Expected initial POST fetch request for 308 redirect")
```

</details>

#### blocks active mixed content fetches from secure pages

- blocks active mixed content fetches from secure pages
   - Expected: _display_js(value) equals `true:blocked:mixed-content:http://example.com/insecure.txt:blocked:mixed-cont... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks active mixed content fetches from secure pages")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('http://example.com/insecure.txt').then(function(r) { return r.text(); }).then(function(t) { meta = 'unexpected:' + t; document.body.textContent = meta; }).catch(function(err) { meta = 'blocked:' + err; document.body.textContent = meta; });</script></body></html>"
)

match session.take_pending_request():
    Some(request):
        fail("Expected HTTPS page mixed-content fetch to be blocked before network request: {request.url}")
    nil:
        val result = session.eval_script("window.isSecureContext + ':' + meta + ':' + document.body.textContent")
        match result:
            Ok(value):
                expect(_display_js(value)).to_equal("true:blocked:mixed-content:http://example.com/insecure.txt:blocked:mixed-content:http://example.com/insecure.txt")
            Err(e):
                fail("Expected mixed-content rejection output to evaluate: {e}")
```

</details>

<details>
<summary>Advanced: does not grant loopback trust to a hostname prefix spoof</summary>

#### does not grant loopback trust to a hostname prefix spoof

- does not grant loopback trust to a hostname prefix spoof
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not grant loopback trust to a hostname prefix spoof")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('http://localhost.evil/insecure.txt').then(function(r) { return r.text(); }).then(function(t) { meta = 'unexpected:' + t; }).catch(function(err) { meta = 'blocked:' + err; });</script></body></html>"
)

expect(session.has_pending_requests()).to_equal(false)
val result = session.eval_script("window.isSecureContext + ':' + meta")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal(
            "true:blocked:mixed-content:http://localhost.evil/insecure.txt"
        )
    Err(e):
        fail("Expected spoofed loopback fetch rejection: {e}")
```

</details>


</details>

#### follows stylesheet redirects and never executes an HTTP error as script

- follows stylesheet redirects and never executes an HTTP error as script
   - Expected: next.url equals `https://example.com/new.css`
   - Expected: _display_js(value) equals `safe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("follows stylesheet redirects and never executes an HTTP error as script")
var styles = BrowserSession.new_without_runtime()
expect(styles.open_html(
    "https://example.com/app",
    "<html><head><link rel='stylesheet' href='/old.css'></head><body><div>ok</div></body></html>"
).is_ok()).to_equal(true)
match styles.take_pending_request():
    Some(first):
        expect(styles.commit_network_response(BrowserResponse.create(
            request_id: first.id,
            kind: "style",
            url: first.url,
            status: 302,
            headers: "Location: /new.css\n",
            body: "ignored",
            error: ""
        )).is_ok()).to_equal(true)
        match styles.take_pending_request():
            Some(next):
                expect(next.url).to_equal("https://example.com/new.css")
            nil:
                fail("Expected redirected stylesheet request")
    nil:
        fail("Expected initial stylesheet request")

var scripts = BrowserSession.new()
expect(scripts.open_html(
    "https://example.com/app",
    "<html><body><script>var marker = 'safe';</script><script src='/missing.js'></script></body></html>"
).is_ok()).to_equal(true)
match scripts.take_pending_request():
    Some(request):
        expect(scripts.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "script",
            url: request.url,
            status: 404,
            headers: "",
            body: "marker = 'executed-error-body';",
            error: ""
        )).is_ok()).to_equal(true)
    nil:
        fail("Expected external script request")
match scripts.eval_script("marker"):
    Ok(value):
        expect(_display_js(value)).to_equal("safe")
    Err(e):
        fail("Expected marker after rejected HTTP error body: {e}")
```

</details>

#### uses the final module URL for redirected relative imports

- uses the final module URL for redirected relative imports
   - Expected: main_request.url equals `https://example.com/dir/main.js`
   - Expected: dep_request.url equals `https://example.com/dir/./dep.js`
   - Expected: session.current_title equals `RedirectedModule`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the final module URL for redirected relative imports")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.com/app",
    "<html><body><script type='module' src='/old.js'></script></body></html>"
).is_ok()).to_equal(true)
match session.take_pending_request():
    Some(first):
        expect(session.commit_network_response(BrowserResponse.create(
            request_id: first.id,
            kind: "module",
            url: first.url,
            status: 302,
            headers: "Location: /dir/main.js\n",
            body: "",
            error: ""
        )).is_ok()).to_equal(true)
    nil:
        fail("Expected initial module request")
match session.take_pending_request():
    Some(main_request):
        expect(main_request.url).to_equal("https://example.com/dir/main.js")
        expect(session.commit_network_response(BrowserResponse.create(
            request_id: main_request.id,
            kind: "module",
            url: main_request.url,
            status: 200,
            headers: "",
            body: "import \{ label \} from './dep.js'; document.title = label;",
            error: ""
        )).is_ok()).to_equal(true)
    nil:
        fail("Expected redirected module request")
match session.take_pending_request():
    Some(dep_request):
        expect(dep_request.url).to_equal("https://example.com/dir/./dep.js")
        expect(session.commit_network_response(BrowserResponse.create(
            request_id: dep_request.id,
            kind: "module",
            url: dep_request.url,
            status: 200,
            headers: "",
            body: "export const label = 'RedirectedModule';",
            error: ""
        )).is_ok()).to_equal(true)
    nil:
        fail("Expected final-URL-relative module dependency")
expect(session.current_title).to_equal("RedirectedModule")
```

</details>

#### follows safe document redirects and blocks HTTPS downgrade

- follows safe document redirects and blocks HTTPS downgrade
   - Expected: redirected.is_ok() is true
   - Expected: next.url equals `https://example.com/done`
   - Expected: next.method equals `GET`
   - Expected: next.body equals ``
   - Expected: next.content_type equals ``
   - Expected: blocked.is_err() is true
   - Expected: downgrade.can_stop_loading() is false
   - Expected: downgrade.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("follows safe document redirects and blocks HTTPS downgrade")
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://example.com/submit", "POST", "", "payload", "text/plain"
).is_ok()).to_equal(true)
match session.take_pending_request():
    Some(first):
        val redirected = session.commit_network_response(BrowserResponse.create(
            request_id: first.id,
            kind: "document",
            url: first.url,
            status: 303,
            headers: "Location: /done\n",
            body: "ignored",
            error: ""
        ))
        expect(redirected.is_ok()).to_equal(true)
        match session.take_pending_request():
            Some(next):
                expect(next.url).to_equal("https://example.com/done")
                expect(next.method).to_equal("GET")
                expect(next.body).to_equal("")
                expect(next.content_type).to_equal("")
            nil:
                fail("Expected redirected document request")
    nil:
        fail("Expected initial document request")

var downgrade = BrowserSession.new()
expect(downgrade.begin_network_navigation(
    "https://example.com/start", "GET", "", "", ""
).is_ok()).to_equal(true)
match downgrade.take_pending_request():
    Some(first):
        val blocked = downgrade.commit_network_response(BrowserResponse.create(
            request_id: first.id,
            kind: "document",
            url: first.url,
            status: 302,
            headers: "Location: http://example.com/insecure\n",
            body: "",
            error: ""
        ))
        expect(blocked.is_err()).to_equal(true)
        expect(downgrade.can_stop_loading()).to_equal(false)
        expect(downgrade.has_pending_requests()).to_equal(false)
    nil:
        fail("Expected initial secure document request")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession HTTP status semantics.
- BrowserSession HTTP status semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `380a41fbeaf15876bd9b9c3285fa4185a74d3af68b6492847170b7e6854a4315`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `380a41fbeaf15876bd9b9c3285fa4185a74d3af68b6492847170b7e6854a4315`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `380a41fbeaf15876bd9b9c3285fa4185a74d3af68b6492847170b7e6854a4315`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/web/browser_session_http_status_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_http_status_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps unknown valid HTTP status codes to their RFC 9110 class semantics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_http_status_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'processes invalid HTTP status codes as server-error class responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_http_status_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'follows same-origin temporary redirects before resolving browser fetch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
