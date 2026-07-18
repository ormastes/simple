# Browser Session Wasm Fetch Bridge Specification

> <details>

<!-- sdn-diagram:id=browser_session_wasm_fetch_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_wasm_fetch_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_wasm_fetch_bridge_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_wasm_fetch_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Wasm Fetch Bridge Specification

## Scenarios

### BrowserSession WASM fetch bridge

#### chains fetched application wasm bytes into WebAssembly instantiate

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `queued`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals ``
- Err
- fail
- Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`
- Ok
- Ok
   - Expected: _display_js(value) equals `fetch>arrayBuffer:11>instantiate:instantiated:11:1:object`
- Err
- fail
- Err
- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes); }).then(function(result) { out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + result.module.sectionCount + ':' + typeof result.instance.exports; }); 'queued'")
match queued:
    Ok(value):
        expect(_display_js(value)).to_equal("queued")
    Err(err):
        fail("unexpected queue error: {err}")
match session.eval_script("out"):
    Ok(value):
        expect(_display_js(value)).to_equal("")
    Err(err):
        fail("unexpected pre-commit js error: {err}")

match session.take_pending_request():
    Some(request):
        expect(request.kind).to_equal("fetch")
        expect(request.url).to_equal("https://example.com/mod.wasm")
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: application/wasm\n",
            body: "0061736d01000000010100",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:11>instantiate:instantiated:11:1:object")
                    Err(err):
                        fail("unexpected js error: {err}")
            Err(err):
                fail("unexpected commit error: {err}")
    nil:
        fail("missing fetch request")
```

</details>

#### keeps WebGPU metadata available after fetched WASM instantiation

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `queued`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals ``
- Err
- fail
- Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`
- Ok
- Ok
   - Expected: _display_js(value) equals `instantiated:11:true:bgra8unorm:function`
- Err
- fail
- Ok
   - Expected: _display_js(value) equals ``
- Err
- fail
- Ok
   - Expected: _display_js(value) equals `Simple WebGPU Software Adapter:true`
- Err
- fail
- Err
- fail
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val queued = session.eval_script("var out = ''; var adapterName = ''; window.fetch('/mod.wasm').then(function(r) { return r.arrayBuffer(); }).then(function(bytes) { return WebAssembly.instantiate(bytes); }).then(function(wasm) { out = wasm.status + ':' + wasm.module.byteLength + ':' + navigator.gpu.softwareFallback + ':' + navigator.gpu.preferredCanvasFormat + ':' + typeof navigator.gpu.requestAdapter; }); 'queued'")
match queued:
    Ok(value):
        expect(_display_js(value)).to_equal("queued")
    Err(err):
        fail("unexpected queue error: {err}")
match session.eval_script("out"):
    Ok(value):
        expect(_display_js(value)).to_equal("")
    Err(err):
        fail("unexpected pre-commit js error: {err}")

match session.take_pending_request():
    Some(request):
        expect(request.kind).to_equal("fetch")
        expect(request.url).to_equal("https://example.com/mod.wasm")
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: application/wasm\n",
            body: "0061736d01000000010100",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("instantiated:11:true:bgra8unorm:function")
                    Err(err):
                        fail("unexpected js error: {err}")
                match session.eval_script("navigator.gpu.requestAdapter().then(function(adapter) { adapterName = adapter.name + ':' + adapter.isFallbackAdapter; }); adapterName"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("")
                    Err(err):
                        fail("unexpected adapter queue error: {err}")
                match session.eval_script("adapterName"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("Simple WebGPU Software Adapter:true")
                    Err(err):
                        fail("unexpected adapter js error: {err}")
            Err(err):
                fail("unexpected commit error: {err}")
    nil:
        fail("missing fetch request")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_wasm_fetch_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession WASM fetch bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
