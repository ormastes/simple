# Browser Session Http Status Specification

> 1. var success session = BrowserSession new

<!-- sdn-diagram:id=browser_session_http_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_http_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_http_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_http_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Http Status Specification

## Scenarios

### BrowserSession HTTP status semantics

#### maps unknown valid HTTP status codes to their RFC 9110 class semantics

1. var success session = BrowserSession new

2. "<html><body><script>var meta = ''; window fetch
   - Expected: _commit_fetch_status(success_session, 299, "ok") equals `299:OK:true`

3. var client error session = BrowserSession new

4. "<html><body><script>var meta = ''; window fetch
   - Expected: _commit_fetch_status(client_error_session, 471, "bad") equals `471:Bad Request:false`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = BrowserSession new

2. "<html><body><script>var meta = ''; window fetch
   - Expected: _commit_fetch_status(session, 701, "invalid") equals `701:Internal Server Error:false`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = ''; window.fetch('/invalid-status').then(function(r) { meta = r.status + ':' + r.statusText + ':' + r.ok; });</script></body></html>"
)

expect(_commit_fetch_status(session, 701, "invalid")).to_equal("701:Internal Server Error:false")
```

</details>

#### follows same-origin temporary redirects before resolving browser fetch

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some
   - Expected: first_request.url equals `https://example.com/old`
   - Expected: first_request.method equals `GET`

4. Ok

5. Some
   - Expected: second_request.url equals `https://example.com/new`
   - Expected: second_request.method equals `GET`

6. Ok

7. Ok
   - Expected: _display_js(value) equals `done:arrived:done:arrived`

8. Err

9. fail

10. Err

11. fail

12. fail

13. Err

14. fail

15. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some
   - Expected: request.url equals `https://example.com/head-check`
   - Expected: request.method equals `HEAD`

4. Ok

5. Ok
   - Expected: _display_js(value) equals `head:0::head:0:`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some
   - Expected: first_request.url equals `https://example.com/submit`
   - Expected: first_request.method equals `POST`
   - Expected: first_request.body equals `payload`

4. Ok

5. Some
   - Expected: second_request.url equals `https://example.com/submitted`
   - Expected: second_request.method equals `GET`
   - Expected: second_request.body equals ``

6. Ok

7. Ok
   - Expected: _display_js(value) equals `see-other:accepted:see-other:accepted`

8. Err

9. fail

10. Err

11. fail

12. fail

13. Err

14. fail

15. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some
   - Expected: first_request.url equals `https://example.com/upload`
   - Expected: first_request.method equals `POST`
   - Expected: first_request.body equals `payload`

4. Ok

5. Some
   - Expected: second_request.url equals `https://example.com/upload-target`
   - Expected: second_request.method equals `POST`
   - Expected: second_request.body equals `payload`

6. Ok

7. Ok
   - Expected: _display_js(value) equals `temporary:stored:temporary:stored`

8. Err

9. fail

10. Err

11. fail

12. fail

13. Err

14. fail

15. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some
   - Expected: first_request.url equals `https://example.com/permanent-upload`
   - Expected: first_request.method equals `POST`
   - Expected: first_request.body equals `payload`

4. Ok

5. Some
   - Expected: second_request.url equals `https://example.com/permanent-upload-target`
   - Expected: second_request.method equals `POST`
   - Expected: second_request.body equals `payload`

6. Ok

7. Ok
   - Expected: _display_js(value) equals `permanent:stored:permanent:stored`

8. Err

9. fail

10. Err

11. fail

12. fail

13. Err

14. fail

15. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some

4. fail

5. Ok
   - Expected: _display_js(value) equals `true:blocked:mixed-content:http://example.com/insecure.txt:blocked:mixed-cont... (full value in folded executable source)`

6. Err

7. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTTP status semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
