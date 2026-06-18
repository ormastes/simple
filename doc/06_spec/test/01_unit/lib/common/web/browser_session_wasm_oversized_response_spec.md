# Browser Session Wasm Oversized Response Specification

> <details>

<!-- sdn-diagram:id=browser_session_wasm_oversized_response_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_wasm_oversized_response_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_wasm_oversized_response_spec -> std
browser_session_wasm_oversized_response_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_wasm_oversized_response_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Wasm Oversized Response Specification

## Scenarios

### BrowserSession oversized WASM response

#### records an oversized valid-header wasm response as rejected

- var session = BrowserSession new
- Ok
- Some
- body:  oversized valid wasm hex
- Ok
   - Expected: session.wasm_modules[0].summary() equals `https://example.com/oversized.wasm:8201:wasm-payload-too-large`
   - Expected: session.warnings.len() equals `1`
- Err
- fail
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script>var marker = 'before';</script><script type='application/wasm' src='/oversized.wasm'></script><script>marker = marker + ':after';</script></body></html>"
val opened = session.open_html("https://example.com/oversized-wasm.html", html)

match opened:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "wasm",
                    url: request.url,
                    status: 200,
                    headers: "Content-Type: application/wasm\n",
                    body: _oversized_valid_wasm_hex(),
                    error: ""
                ))
                match committed:
                    Ok(_):
                        expect(session.wasm_modules[0].summary()).to_equal("https://example.com/oversized.wasm:8201:wasm-payload-too-large")
                        expect(session.wasm_modules[0].valid).to_be(false)
                        expect(session.warnings.len()).to_equal(1)
                        expect(session.warnings[0]).to_contain("wasm-payload-too-large")
                    Err(err):
                        fail("Expected commit to continue after oversized WASM warning: {err}")
            nil:
                fail("Expected pending WASM request")
    Err(err):
        fail("Expected page to load: {err}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_wasm_oversized_response_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession oversized WASM response

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
