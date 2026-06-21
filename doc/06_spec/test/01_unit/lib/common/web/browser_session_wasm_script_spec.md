# Browser Session Wasm Script Specification

> <details>

<!-- sdn-diagram:id=browser_session_wasm_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_wasm_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_wasm_script_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_wasm_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Wasm Script Specification

## Scenarios

### BrowserSession WASM script resources

#### records inline application wasm beside JavaScript without evaluating it as JS

- var session = BrowserSession new
- Ok
   - Expected: session.wasm_modules.len() equals `1`
   - Expected: session.wasm_modules[0].url equals `https://example.com/inline-wasm.html`
   - Expected: session.wasm_modules[0].byte_length equals `8`
   - Expected: session.wasm_modules[0].status equals `validated`
   - Expected: session.warnings.len() equals `0`
- Ok
   - Expected: _display_js(value) equals `js-before:js-after:function`
- Err
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script>var before = 'js-before';</script><script type='application/wasm'>0061736d01000000</script><script>var after = before + ':js-after';</script></body></html>"
val result = session.open_html("https://example.com/inline-wasm.html", html)

match result:
    Ok(_):
        expect(session.wasm_modules.len()).to_equal(1)
        expect(session.wasm_modules[0].url).to_equal("https://example.com/inline-wasm.html")
        expect(session.wasm_modules[0].byte_length).to_equal(8)
        expect(session.wasm_modules[0].valid).to_be(true)
        expect(session.wasm_modules[0].status).to_equal("validated")
        expect(session.warnings.len()).to_equal(0)
        val js_result = session.eval_script("after + ':' + typeof WebAssembly.instantiate")
        match js_result:
            Ok(value):
                expect(_display_js(value)).to_equal("js-before:js-after:function")
            Err(err):
                fail("Expected JS after inline WASM to evaluate: {err}")
    Err(err):
        fail("Expected inline WASM page to load: {err}")
```

</details>

#### loads external application wasm in script order and resumes later JavaScript

- var session = BrowserSession new
- Ok
- Some
   - Expected: request.kind equals `wasm`
   - Expected: request.url equals `https://example.com/app.wasm`
   - Expected: request.content_type equals `application/wasm`
- Ok
   - Expected: session.wasm_modules.len() equals `1`
   - Expected: session.wasm_modules[0].url equals `https://example.com/app.wasm`
   - Expected: session.wasm_modules[0].summary() equals `https://example.com/app.wasm:8:validated`
   - Expected: session.warnings.len() equals `0`
- Ok
   - Expected: _display_js(value) equals `before:after`
- Err
- fail
- Err
- fail
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script>var order = 'before';</script><script type='application/wasm' src='/app.wasm'></script><script>order = order + ':after';</script></body></html>"
val result = session.open_html("https://example.com/wasm-page.html", html)

match result:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("wasm")
                expect(request.url).to_equal("https://example.com/app.wasm")
                expect(request.content_type).to_equal("application/wasm")
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "wasm",
                    url: request.url,
                    status: 200,
                    headers: "Content-Type: application/wasm\n",
                    body: "0061736d01000000",
                    error: ""
                ))
                match committed:
                    Ok(_):
                        expect(session.wasm_modules.len()).to_equal(1)
                        expect(session.wasm_modules[0].url).to_equal("https://example.com/app.wasm")
                        expect(session.wasm_modules[0].summary()).to_equal("https://example.com/app.wasm:8:validated")
                        expect(session.warnings.len()).to_equal(0)
                        val js_result = session.eval_script("order")
                        match js_result:
                            Ok(value):
                                expect(_display_js(value)).to_equal("before:after")
                            Err(err):
                                fail("Expected JS after external WASM to evaluate: {err}")
                    Err(err):
                        fail("Expected external WASM response to commit: {err}")
            nil:
                fail("Expected pending external WASM request")
    Err(err):
        fail("Expected external WASM page to start loading: {err}")
```

</details>

#### reports invalid wasm script payloads without running them as JavaScript

- var session = BrowserSession new
- Ok
   - Expected: session.wasm_modules.len() equals `1`
   - Expected: session.wasm_modules[0].status equals `invalid-wasm-header`
   - Expected: session.warnings.len() equals `1`
- Ok
   - Expected: _display_js(value) equals `before:after`
- Err
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script>var marker = 'before';</script><script type='application/wasm'>0061736d00000000</script><script>marker = marker + ':after';</script></body></html>"
val result = session.open_html("https://example.com/invalid-wasm.html", html)

match result:
    Ok(_):
        expect(session.wasm_modules.len()).to_equal(1)
        expect(session.wasm_modules[0].valid).to_be(false)
        expect(session.wasm_modules[0].status).to_equal("invalid-wasm-header")
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("wasm module error")
        val js_result = session.eval_script("marker")
        match js_result:
            Ok(value):
                expect(_display_js(value)).to_equal("before:after")
            Err(err):
                fail("Expected JS after invalid WASM to evaluate: {err}")
    Err(err):
        fail("Expected invalid WASM page to load with warning: {err}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession WASM script resources

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
