# Browser Session Async Specification

> 1. var session = BrowserSession new

<!-- sdn-diagram:id=browser_session_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_async_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Async Specification

## Scenarios

### BrowserSession async fetch

#### adopts promises returned from then callbacks

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; Promise resolve

3. Ok
   - Expected: _display_js(value) equals `inner`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = 'start'; Promise.resolve('seed').then(function() { return Promise.resolve('inner'); }).then(function(v) { out = v; });</script></body></html>"
)

val result = session.eval_script("out")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("inner")
    Err(e) =>
        fail("Expected adopted promise return value to evaluate: {e}")
```

</details>

#### adopts rejected promises returned from then callbacks

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; Promise resolve

3. Ok
   - Expected: _display_js(value) equals `boom`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = 'start'; Promise.resolve('seed').then(function() { return Promise.reject('boom'); }).catch(function(err) { out = err; });</script></body></html>"
)

val result = session.eval_script("out")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("boom")
    Err(e) =>
        fail("Expected adopted rejected promise callback to evaluate: {e}")
```

</details>

#### installs promise globals

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `function:function`

4. Err

5. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/app", "<html><body>Ready</body></html>")
val result = session.eval_script("typeof Promise.resolve + ':' + typeof Promise.prototype.then")
match result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function:function")
    Err(e) =>
        fail("Expected Promise globals to evaluate: {e}")
```

</details>

#### queues a pending fetch and settles it later

1. var session = BrowserSession new

2. "<html><body><script>var out = ''; window fetch

3. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/data.txt`

4. Ok

5. Ok

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = ''; window.fetch('/data.txt').then(function(r) { return r.text(); }).then(function(t) { out = t; document.body.textContent = t; });</script></body></html>"
)

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
                fail("Expected network response commit for pending fetch to succeed: {e}")
    nil:
        fail("Expected pending fetch request after fetch setup")
```

</details>

#### rejects promise callbacks on transport error

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; window fetch

3. Some

4. Err
   - Expected: e equals `network down`

5. Ok
   - Expected: _display_js(value) equals `network down`

6. Err

7. fail

8. Ok

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

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
                        fail("Expected transport rejection callback output to evaluate: {err}")
            Ok(_) =>
                fail("Expected transport-error commit to reject")
    nil:
        fail("Expected pending fetch request for transport-error path")
```

</details>

#### resolves http error responses with ok false and readable metadata

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `404:false:X-Test: missing\n:missing:missing:404:false:X-Test: missing\n:missi... (full value in folded executable source)`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/missing.txt').then(function(r) { meta = r.status + ':' + r.ok + ':' + r.headersText + ':' + r.text() + ':' + r.text(); document.body.textContent = meta; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 404,
            headers: "X-Test: missing\n",
            body: "missing",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("meta + ':' + document.body.textContent")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("404:false:X-Test: missing\n:missing:missing:404:false:X-Test: missing\n:missing:missing")
                    Err(e) =>
                        fail("Expected HTTP error response metadata output to evaluate: {e}")
            Err(e) =>
                fail("Expected HTTP error response commit to resolve: {e}")
    nil:
        fail("Expected pending fetch request for HTTP error response")
```

</details>

#### exposes response.statusText for resolved fetch responses

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `404:Not Found:false:404:Not Found:false`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/missing.txt').then(function(r) { meta = r.status + ':' + r.statusText + ':' + r.ok; document.body.textContent = meta; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 404,
            headers: "",
            body: "missing",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("meta + ':' + document.body.textContent")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("404:Not Found:false:404:Not Found:false")
                    Err(e) =>
                        fail("Expected response.statusText output to evaluate: {e}")
            Err(e) =>
                fail("Expected statusText response commit to resolve: {e}")
    nil:
        fail("Expected pending fetch request for statusText response")
```

</details>

#### rejects compileStreaming when response content type is not application wasm

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; WebAssembly compileStreaming

3. Some
   - Expected: request.url equals `https://example.com/module.wasm`

4. Ok

5. Ok
   - Expected: _display_js(value) equals `unsupported-wasm-content-type:text/plain`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = 'start'; WebAssembly.compileStreaming(window.fetch('/module.wasm')).then(function(m) { out = 'compiled'; }).catch(function(err) { out = err; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        expect(request.url).to_equal("https://example.com/module.wasm")
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: text/plain\n",
            body: "0061736d01000000",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("out")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("unsupported-wasm-content-type:text/plain")
                    Err(e) =>
                        fail("Expected compileStreaming MIME rejection output to evaluate: {e}")
            Err(e) =>
                fail("Expected compileStreaming non-wasm response commit to settle: {e}")
    nil:
        fail("Expected pending fetch request for compileStreaming MIME check")
```

</details>

#### rejects instantiateStreaming when response content type is not application wasm

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; WebAssembly instantiateStreaming

3. Some
   - Expected: request.url equals `https://example.com/module.wasm`

4. Ok

5. Ok
   - Expected: _display_js(value) equals `unsupported-wasm-content-type:text/plain`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = 'start'; WebAssembly.instantiateStreaming(window.fetch('/module.wasm')).then(function(result) { out = result.instance.status; }).catch(function(err) { out = err; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        expect(request.url).to_equal("https://example.com/module.wasm")
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: text/plain\n",
            body: "0061736d01000000",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("out")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("unsupported-wasm-content-type:text/plain")
                    Err(e) =>
                        fail("Expected instantiateStreaming MIME rejection output to evaluate: {e}")
            Err(e) =>
                fail("Expected instantiateStreaming non-wasm response commit to settle: {e}")
    nil:
        fail("Expected pending fetch request for instantiateStreaming MIME check")
```

</details>

#### blocks mixed content compileStreaming wasm fetches from secure pages

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; WebAssembly compileStreaming

3. Some

4. fail

5. Ok
   - Expected: _display_js(value) equals `true:mixed-content:http://example.com/module.wasm`

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
    "<html><body><script>var out = 'start'; WebAssembly.compileStreaming(window.fetch('http://example.com/module.wasm')).then(function(m) { out = 'compiled'; }).catch(function(err) { out = err; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        fail("Expected secure-page compileStreaming mixed-content fetch to be blocked before network request: {request.url}")
    nil:
        val result = session.eval_script("window.isSecureContext + ':' + out")
        match result:
            Ok(value) =>
                expect(_display_js(value)).to_equal("true:mixed-content:http://example.com/module.wasm")
            Err(e) =>
                fail("Expected compileStreaming mixed-content rejection output to evaluate: {e}")
```

</details>

#### returns a promise from response.text and unwraps it through then chaining

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `function:alpha`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/data.txt').then(function(r) { meta = typeof r.text().then; return r.text(); }).then(function(t) { document.body.textContent = meta + ':' + t; });</script></body></html>"
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
                val result = session.eval_script("document.body.textContent")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("function:alpha")
                    Err(e) =>
                        fail("Expected response.text promise output to evaluate: {e}")
            Err(e) =>
                fail("Expected response.text network response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for response.text promise")
```

</details>

#### marks response.bodyUsed after text consumption

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `false:true:alpha:false:true:alpha`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/data.txt').then(function(r) { var before = r.bodyUsed; var text = r.text(); meta = before + ':' + r.bodyUsed + ':' + text; document.body.textContent = meta; });</script></body></html>"
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
                val result = session.eval_script("meta + ':' + document.body.textContent")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("false:true:alpha:false:true:alpha")
                    Err(e) =>
                        fail("Expected response.bodyUsed output to evaluate: {e}")
            Err(e) =>
                fail("Expected bodyUsed response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for bodyUsed response")
```

</details>

#### returns a promise from response.json for simple JSON bodies

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `function:42`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/data.json').then(function(r) { meta = typeof r.json; return r.json(); }).then(function(v) { document.body.textContent = meta + ':' + v; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: application/json\n",
            body: "42",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("document.body.textContent")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("function:42")
                    Err(e) =>
                        fail("Expected response.json promise output to evaluate: {e}")
            Err(e) =>
                fail("Expected JSON response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for JSON response")
```

</details>

#### serializes plain object fetch headers into the pending request

1. var session = BrowserSession new

2. "<html><body><script>window fetch

3. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.method equals `POST`
   - Expected: request.body equals `alpha`

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>window.fetch('/data.txt', { method: 'POST', headers: { 'X-Test': '1', 'Accept': 'text/plain' }, body: 'alpha' });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        expect(request.kind).to_equal("fetch")
        expect(request.method).to_equal("POST")
        expect(request.body).to_equal("alpha")
        expect(request.headers).to_contain("X-Test: 1")
        expect(request.headers).to_contain("Accept: text/plain")
    nil:
        fail("Expected pending fetch request with plain object headers")
```

</details>

#### ignores caller cookie headers and keeps the session cookie on fetch requests

1. var session = BrowserSession new

2. "<html><body><script>document cookie = 'sid=abc123; Path=/'; window fetch

3. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.headers does not contain `manual=1`
   - Expected: request.headers.split("\n").len() equals `2`

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>document.cookie = 'sid=abc123; Path=/'; window.fetch('/data.txt', { headers: { 'Cookie': 'manual=1', 'X-Test': '1' } });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        expect(request.kind).to_equal("fetch")
        expect(request.headers).to_contain("X-Test: 1")
        expect(request.headers).to_contain("Cookie: sid=abc123")
        expect(request.headers.contains("manual=1")).to_equal(false)
        expect(request.headers.split("\n").len()).to_equal(2)
    nil:
        fail("Expected pending fetch request with sanitized cookie headers")
```

</details>

#### uses cookies set by one fetch response on the next fetch from the same page

1. var session = BrowserSession new

2. "<html><body><script>var first = ''; var second = ''; window fetch

3. Some
   - Expected: first_request.headers does not contain `Cookie:`

4. Ok

5. Some

6. Ok

7. Ok
   - Expected: _display_js(value) equals `token=abc:token=abc:two`

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

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var first = ''; var second = ''; window.fetch('/first.txt').then(function(r) { return r.text(); }).then(function(t) { first = document.cookie; return window.fetch('/second.txt'); }).then(function(r) { return r.text(); }).then(function(t) { second = document.cookie; document.body.textContent = first + ':' + second + ':' + t; });</script></body></html>"
)

match session.take_pending_request():
    Some(first_request) =>
        expect(first_request.headers.contains("Cookie:")).to_equal(false)
        val first_result = session.commit_network_response(BrowserResponse.create(
            request_id: first_request.id,
            kind: "fetch",
            url: first_request.url,
            status: 200,
            headers: "Set-Cookie: token=abc; Path=/\n",
            body: "one",
            error: ""
        ))
        match first_result:
            Ok(_) =>
                match session.take_pending_request():
                    Some(second_request) =>
                        expect(second_request.headers).to_contain("Cookie: token=abc")
                        val second_result = session.commit_network_response(BrowserResponse.create(
                            request_id: second_request.id,
                            kind: "fetch",
                            url: second_request.url,
                            status: 200,
                            headers: "",
                            body: "two",
                            error: ""
                        ))
                        match second_result:
                            Ok(_) =>
                                val result = session.eval_script("document.body.textContent")
                                match result:
                                    Ok(value) =>
                                        expect(_display_js(value)).to_equal("token=abc:token=abc:two")
                                    Err(e) =>
                                        fail("Expected chained fetch cookie/body result to evaluate: {e}")
                            Err(e) =>
                                fail("Expected second chained fetch response commit to succeed: {e}")
                    nil:
                        fail("Expected second pending fetch request after cookie-setting response")
            Err(e) =>
                fail("Expected first chained fetch response commit to succeed: {e}")
    nil:
        fail("Expected first pending fetch request for cookie chaining")
```

</details>

#### applies Set-Cookie from fetch responses without exposing it in response headersText

1. var session = BrowserSession new

2. "<html><body><script>var meta = 'start'; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `X-Test: ok\\n:token=abc:X-Test: ok\\n:token=abc`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var meta = 'start'; window.fetch('/data.txt').then(function(r) { meta = r.headersText + ':' + document.cookie; document.body.textContent = meta; });</script></body></html>"
)

match session.take_pending_request():
    Some(request) =>
        val commit_result = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Set-Cookie: token=abc; Path=/\nX-Test: ok\n",
            body: "alpha",
            error: ""
        ))
        match commit_result:
            Ok(_) =>
                val result = session.eval_script("meta + ':' + document.body.textContent")
                match result:
                    Ok(value) =>
                        expect(_display_js(value)).to_equal("X-Test: ok\\n:token=abc:X-Test: ok\\n:token=abc")
                    Err(e) =>
                        fail("Expected Set-Cookie filtering metadata output to evaluate: {e}")
            Err(e) =>
                fail("Expected Set-Cookie filtering response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for Set-Cookie filtering")
```

</details>

#### settles multiple fetches by request id even when responses arrive out of order

1. var session = BrowserSession new

2. "<html><body><script>var first = ''; var second = ''; window fetch

3. Some

4. req a = Some

5. fail

6. Some

7. req b = Some

8. fail

9. Some

10. Some
   - Expected: first_request.url equals `https://example.com/a.txt`
   - Expected: second_request.url equals `https://example.com/b.txt`

11. Ok

12. Ok
   - Expected: _display_js(value) equals `:B::B`

13. Err

14. fail

15. Err

16. fail

17. Ok

18. Ok
   - Expected: _display_js(value) equals `A:B`

19. Err

20. fail

21. Err

22. fail

23. fail

24. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var first = ''; var second = ''; window.fetch('/a.txt').then(function(r) { return r.text(); }).then(function(t) { first = t; }); window.fetch('/b.txt').then(function(r) { return r.text(); }).then(function(t) { second = t; document.body.textContent = first + ':' + second; });</script></body></html>"
)

var req_a = nil
var req_b = nil
match session.take_pending_request():
    Some(request) =>
        req_a = Some(request)
    nil =>
        fail("Expected first pending fetch request for out-of-order settlement")
        return
match session.take_pending_request():
    Some(request) =>
        req_b = Some(request)
    nil =>
        fail("Expected second pending fetch request for out-of-order settlement")
        return

match req_a:
    Some(first_request) =>
        match req_b:
            Some(second_request) =>
                expect(first_request.url).to_equal("https://example.com/a.txt")
                expect(second_request.url).to_equal("https://example.com/b.txt")
                val second_result = session.commit_network_response(BrowserResponse.create(
                    request_id: second_request.id,
                    kind: "fetch",
                    url: second_request.url,
                    status: 200,
                    headers: "",
                    body: "B",
                    error: ""
                ))
                match second_result:
                    Ok(_) =>
                        val mid = session.eval_script("first + ':' + second + ':' + document.body.textContent")
                        match mid:
                            Ok(value) =>
                                expect(_display_js(value)).to_equal(":B::B")
                            Err(e) =>
                                fail("Expected mid out-of-order fetch state to evaluate: {e}")
                    Err(e) =>
                        fail("Expected second out-of-order fetch response commit to succeed: {e}")
                val first_result = session.commit_network_response(BrowserResponse.create(
                    request_id: first_request.id,
                    kind: "fetch",
                    url: first_request.url,
                    status: 200,
                    headers: "",
                    body: "A",
                    error: ""
                ))
                match first_result:
                    Ok(_) =>
                        val final = session.eval_script("first + ':' + second")
                        match final:
                            Ok(value) =>
                                expect(_display_js(value)).to_equal("A:B")
                            Err(e) =>
                                fail("Expected final out-of-order fetch state to evaluate: {e}")
                    Err(e) =>
                        fail("Expected first out-of-order fetch response commit to succeed: {e}")
            nil =>
                fail("Expected stored second request for out-of-order settlement")
    nil =>
        fail("Expected stored first request for out-of-order settlement")
```

</details>

#### preserves fulfilled values through finally chains

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; window fetch

3. Some

4. Ok

5. Ok
   - Expected: _display_js(value) equals `alpha:cleanup`

6. Err

7. fail

8. Err

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = 'start'; window.fetch('/data.txt').then(function(r) { return r.text(); }).finally(function() { document.body.textContent = 'cleanup'; return 'ignored'; }).then(function(t) { out = t + ':' + document.body.textContent; });</script></body></html>"
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
                        expect(_display_js(value)).to_equal("alpha:cleanup")
                    Err(e) =>
                        fail("Expected fulfilled Promise.finally chain output to evaluate: {e}")
            Err(e) =>
                fail("Expected fulfilled Promise.finally response commit to succeed: {e}")
    nil:
        fail("Expected pending fetch request for fulfilled Promise.finally chain")
```

</details>

#### preserves rejected values through finally chains

1. var session = BrowserSession new

2. "<html><body><script>var out = 'start'; window fetch

3. Some

4. Err
   - Expected: e equals `network down`

5. Ok
   - Expected: _display_js(value) equals `network down:cleanup`

6. Err

7. fail

8. Ok

9. fail

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    "<html><body><script>var out = 'start'; window.fetch('/data.txt').finally(function() { document.body.textContent = 'cleanup'; return 'ignored'; }).catch(function(err) { out = err + ':' + document.body.textContent; });</script></body></html>"
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
                        expect(_display_js(value)).to_equal("network down:cleanup")
                    Err(err) =>
                        fail("Expected rejected Promise.finally chain output to evaluate: {err}")
            Ok(_) =>
                fail("Expected rejected Promise.finally transport commit to reject")
    nil:
        fail("Expected pending fetch request for rejected Promise.finally chain")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession async fetch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
