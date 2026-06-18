# Browser Session Simple Script Command Bounds Spec

> Inline and external `text/simple` scripts share a command-count limit. Oversized command blocks must emit a warning, avoid partial drawing output, and preserve the surrounding page load flow.

<!-- sdn-diagram:id=browser_session_simple_script_command_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_simple_script_command_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_simple_script_command_bounds_spec -> std
browser_session_simple_script_command_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_simple_script_command_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Simple Script Command Bounds Spec

Inline and external `text/simple` scripts share a command-count limit. Oversized command blocks must emit a warning, avoid partial drawing output, and preserve the surrounding page load flow.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_simple_script_command_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Inline and external `text/simple` scripts share a command-count limit. Oversized
command blocks must emit a warning, avoid partial drawing output, and preserve
the surrounding page load flow.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec`, browser-session request/response helpers, and body
HTML assertions as the non-raster oracle.

## Scenarios

### BrowserSession Simple script command bounds

#### rejects oversized Simple script command blocks before partial drawing

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
val script = str_repeat("simple2d.fill_rect 1 1 1 1 255\n", 129)
val html = "<html><body><script type='text/simple'>" + script + "</script></body></html>"
val result = session.open_html("https://example.com/simple-script-too-many-commands.html", html)

match result:
    Ok(_):
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("simple script error: command count exceeds limit")
        expect(session.current_body_html).to_contain("simple2d.fill_rect 1 1 1 1 255")
    Err(err):
        fail("Expected oversized Simple script page to load with warning: {err}")
```

</details>

#### rejects oversized external Simple script responses before partial drawing

- var session = BrowserSession new
- Ok
- Some
   - Expected: request.kind equals `script`
   - Expected: request.url equals `https://example.com/too-many.simple`
- body: str repeat
- Ok
   - Expected: session.warnings.len() equals `1`
- Err
- fail
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body>safe<script type='text/simple' src='/too-many.simple'></script></body></html>"
val result = session.open_html("https://example.com/external-simple-script-too-many-commands.html", html)

match result:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("script")
                expect(request.url).to_equal("https://example.com/too-many.simple")
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "script",
                    url: request.url,
                    status: 200,
                    headers: "Content-Type: text/simple\n",
                    body: str_repeat("simple2d.fill_rect 1 1 1 1 255\n", 129),
                    error: ""
                ))
                match committed:
                    Ok(_):
                        expect(session.warnings.len()).to_equal(1)
                        expect(session.warnings[0]).to_contain("simple script error: command count exceeds limit")
                        expect(session.current_body_html).to_contain("safe")
                    Err(err):
                        fail("Expected oversized external Simple script response to commit with warning: {err}")
            nil:
                fail("Expected pending external Simple script request")
    Err(err):
        fail("Expected external Simple script page to start loading: {err}")
```

</details>

#### records external Simple script transport errors and resumes later scripts

- var session = BrowserSession new
- Ok
- Some
   - Expected: request.kind equals `script`
   - Expected: request.url equals `https://example.com/missing.simple`
- Ok
   - Expected: session.warnings.len() equals `1`
   - Expected: session.warnings[0] equals `simple script load error: network unavailable`
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
val html = "<html><body>safe<script type='text/simple' src='/missing.simple'></script><script>var afterSimpleError = 'ran';</script></body></html>"
val result = session.open_html("https://example.com/external-simple-script-error.html", html)

match result:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("script")
                expect(request.url).to_equal("https://example.com/missing.simple")
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "script",
                    url: request.url,
                    status: 503,
                    headers: "Content-Type: text/simple\n",
                    body: "",
                    error: "network unavailable"
                ))
                match committed:
                    Ok(_):
                        expect(session.warnings.len()).to_equal(1)
                        expect(session.warnings[0]).to_equal("simple script load error: network unavailable")
                        val js_result = session.eval_script("afterSimpleError")
                        match js_result:
                            Ok(value):
                                expect(_display_js(value)).to_equal("ran")
                            Err(err):
                                fail("Expected later script after Simple script load error to run: {err}")
                    Err(err):
                        fail("Expected external Simple script error response to commit with warning: {err}")
            nil:
                fail("Expected pending external Simple script request")
    Err(err):
        fail("Expected external Simple script error page to start loading: {err}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
