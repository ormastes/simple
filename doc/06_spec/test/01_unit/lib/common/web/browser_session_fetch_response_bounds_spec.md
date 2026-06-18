# Browser Session Fetch Response Bounds Spec

> Fetch responses can flow into `response.text()`, `response.arrayBuffer()`, and WebAssembly streaming paths. Oversized bodies must fail closed at the browser session response boundary instead of materializing a large JS response payload.

<!-- sdn-diagram:id=browser_session_fetch_response_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_fetch_response_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_fetch_response_bounds_spec -> std
browser_session_fetch_response_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_fetch_response_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Fetch Response Bounds Spec

Fetch responses can flow into `response.text()`, `response.arrayBuffer()`, and WebAssembly streaming paths. Oversized bodies must fail closed at the browser session response boundary instead of materializing a large JS response payload.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_fetch_response_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Fetch responses can flow into `response.text()`, `response.arrayBuffer()`, and
WebAssembly streaming paths. Oversized bodies must fail closed at the browser
session response boundary instead of materializing a large JS response payload.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec`, browser-session request/response helpers, and direct
JS-visible state assertions.

## Scenarios

### BrowserSessionFetchResponseBounds

#### rejects oversized fetch responses before body materialization or cookie side effects

- var session = BrowserSession new
- "<html><body>safe<script>var out = 'start'; window fetch
- Ok
- Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/big.bin`
- Ok
- fail
- Err
- Ok
   - Expected: _display_js(value) equals `fetch response exceeds browser session limit:safe:`
- Err
- fail
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val opened = session.open_html(
    "https://example.com/fetch-too-large.html",
    "<html><body>safe<script>var out = 'start'; window.fetch('/big.bin').then(function(r) { return r.text(); }).then(function(t) { out = t; document.body.textContent = t; }).catch(function(err) { out = err; });</script></body></html>"
)

match opened:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("fetch")
                expect(request.url).to_equal("https://example.com/big.bin")
                val oversized_body = str_repeat("x", browser_session_debug_max_fetch_response_bytes() + 1)
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "fetch",
                    url: request.url,
                    status: 200,
                    headers: "Set-Cookie: token=oversized; Path=/\n",
                    body: oversized_body,
                    error: ""
                ))
                match committed:
                    Ok(_):
                        fail("Expected oversized fetch response to be rejected")
                    Err(err):
                        expect(err).to_contain("fetch response exceeds browser session limit")
                        val observed = session.eval_script("out + ':' + document.body.textContent + ':' + document.cookie")
                        match observed:
                            Ok(value):
                                expect(_display_js(value)).to_equal("fetch response exceeds browser session limit:safe:")
                            Err(eval_err):
                                fail("Expected rejected fetch state to be readable: {eval_err}")
            nil:
                fail("Expected pending fetch request")
    Err(err):
        fail("Expected fetch page to load: {err}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
