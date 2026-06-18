# Browser Session JavaScript Source Bounds Spec

> Direct `eval_script`, inline classic scripts, and external classic script responses share a JavaScript source-size limit. Oversized sources must report a warning or error and must not partially define globals or mutate document state. External script rejection must still allow later script blocks to resume.

<!-- sdn-diagram:id=browser_session_js_source_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_js_source_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_js_source_bounds_spec -> std
browser_session_js_source_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_js_source_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session JavaScript Source Bounds Spec

Direct `eval_script`, inline classic scripts, and external classic script responses share a JavaScript source-size limit. Oversized sources must report a warning or error and must not partially define globals or mutate document state. External script rejection must still allow later script blocks to resume.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_js_source_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Direct `eval_script`, inline classic scripts, and external classic script
responses share a JavaScript source-size limit. Oversized sources must report a
warning or error and must not partially define globals or mutate document state.
External script rejection must still allow later script blocks to resume.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec`, browser-session request/response helpers, and
concrete JavaScript runtime state assertions.

## Scenarios

### BrowserSession JavaScript source bounds

#### rejects direct eval_script sources over the browser session limit

- var session = BrowserSession new
- Ok
- Ok
- fail
- Err
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val opened = session.open_html("https://example.com/direct-eval.html", "<html><body>ready</body></html>")

match opened:
    Ok(_):
        val result = session.eval_script(_oversized_js_source())
        match result:
            Ok(_):
                fail("Expected oversized eval_script source to be rejected")
            Err(err):
                expect(err).to_contain("javascript source exceeds browser session limit")
    Err(err):
        fail("Expected setup page to load: {err}")
```

</details>

#### rejects oversized inline JavaScript without applying partial side effects

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `1`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val source = "document.body.textContent = 'changed';\n" + _oversized_js_source()
val html = "<html><body>safe<script>" + source + "</script></body></html>"
val opened = session.open_html("https://example.com/inline-too-large.html", html)

match opened:
    Ok(_):
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("inline script error: javascript source exceeds browser session limit")
        expect(session.current_body_html).to_contain("safe")
    Err(err):
        fail("Expected oversized inline script page to load with warning: {err}")
```

</details>

#### rejects oversized external classic script responses without applying partial side effects

- var session = BrowserSession new
- Ok
- Some
   - Expected: request.kind equals `script`
   - Expected: request.url equals `https://example.com/too-large.js`
- body: "var externalRan = 'yes';\n" +  oversized js source
- Ok
   - Expected: session.warnings.len() equals `1`
- Ok
   - Expected: _display_js(value) equals `undefined`
- Err
- fail
- Err
- fail
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body>safe<script src='/too-large.js'></script><script>var afterExternal = typeof externalRan;</script></body></html>"
val opened = session.open_html("https://example.com/external-too-large.html", html)

match opened:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("script")
                expect(request.url).to_equal("https://example.com/too-large.js")
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "script",
                    url: request.url,
                    status: 200,
                    headers: "Content-Type: text/javascript\n",
                    body: "var externalRan = 'yes';\n" + _oversized_js_source(),
                    error: ""
                ))
                match committed:
                    Ok(_):
                        expect(session.warnings.len()).to_equal(1)
                        expect(session.warnings[0]).to_contain("external script error: javascript source exceeds browser session limit")
                        val result = session.eval_script("afterExternal")
                        match result:
                            Ok(value):
                                expect(_display_js(value)).to_equal("undefined")
                            Err(err):
                                fail("Expected later inline script state to be readable: {err}")
                    Err(err):
                        fail("Expected oversized external script response to commit with warning: {err}")
            nil:
                fail("Expected pending external script request")
    Err(err):
        fail("Expected external script page to start loading: {err}")
```

</details>

#### records external classic script transport errors and resumes later scripts

- var session = BrowserSession new
- Ok
- Some
   - Expected: request.kind equals `script`
   - Expected: request.url equals `https://example.com/missing.js`
- Ok
   - Expected: session.warnings.len() equals `1`
   - Expected: session.warnings[0] equals `external script error: network unavailable`
- Ok
   - Expected: _display_js(value) equals `ran`
- Err
- fail
- Err
- fail
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body>safe<script src='/missing.js'></script><script>var afterExternalError = 'ran';</script></body></html>"
val opened = session.open_html("https://example.com/external-error.html", html)

match opened:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("script")
                expect(request.url).to_equal("https://example.com/missing.js")
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "script",
                    url: request.url,
                    status: 503,
                    headers: "Content-Type: text/javascript\n",
                    body: "",
                    error: "network unavailable"
                ))
                match committed:
                    Ok(_):
                        expect(session.warnings.len()).to_equal(1)
                        expect(session.warnings[0]).to_equal("external script error: network unavailable")
                        val result = session.eval_script("afterExternalError")
                        match result:
                            Ok(value):
                                expect(_display_js(value)).to_equal("ran")
                            Err(err):
                                fail("Expected later inline script after external error to run: {err}")
                    Err(err):
                        fail("Expected external script error response to commit with warning: {err}")
            nil:
                fail("Expected pending external script request")
    Err(err):
        fail("Expected external script error page to start loading: {err}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
