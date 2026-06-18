# Browser Session HTML Source Bounds Spec

> HTML source feeds title/body extraction, stylesheet extraction, script extraction, runtime creation, and history state. Oversized documents must fail closed at the shared page-source load entrypoint.

<!-- sdn-diagram:id=browser_session_html_source_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_source_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_source_bounds_spec -> std
browser_session_html_source_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_source_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session HTML Source Bounds Spec

HTML source feeds title/body extraction, stylesheet extraction, script extraction, runtime creation, and history state. Oversized documents must fail closed at the shared page-source load entrypoint.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_html_source_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

HTML source feeds title/body extraction, stylesheet extraction, script
extraction, runtime creation, and history state. Oversized documents must fail
closed at the shared page-source load entrypoint.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and browser-session state assertions.

## Scenarios

### BrowserSessionHtmlSourceBounds

#### rejects oversized html without replacing the current page

- var session = BrowserSession new
- Ok
- Ok
- fail
- Err
   - Expected: session.current_url equals `https://example.com/safe.html`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val initial = session.open_html("https://example.com/safe.html", "<html><body>safe</body></html>")
match initial:
    Ok(_):
        val oversized_html = "<html><body>" + str_repeat("x", browser_session_debug_max_html_source_bytes() + 1) + "</body></html>"
        val rejected = session.open_html("https://example.com/too-large.html", oversized_html)
        match rejected:
            Ok(_):
                fail("Expected oversized html to be rejected")
            Err(err):
                expect(err).to_contain("html source exceeds browser session limit")
                expect(session.current_url).to_equal("https://example.com/safe.html")
                expect(session.current_body_html).to_contain("safe")
    Err(err):
        fail("Expected setup page to load: {err}")
```

</details>

#### rejects oversized network document responses before headers or page replacement

- var session = BrowserSession new
- Ok
- Ok
- Some
   - Expected: request.kind equals `document`
- Ok
- fail
- Err
   - Expected: session.current_url equals `https://example.com/safe.html`
- Ok
- JsValue String
   - Expected: cookie equals ``
- fail
- Err
- fail
- fail
- Err
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val initial = session.open_html("https://example.com/safe.html", "<html><body>safe</body></html>")
match initial:
    Ok(_):
        val started = session.begin_network_navigation("https://example.com/too-large-network.html", "GET", "", "", "")
        match started:
            Ok(_):
                match session.take_pending_request():
                    Some(request):
                        expect(request.kind).to_equal("document")
                        val oversized_html = "<html><body>" + str_repeat("x", browser_session_debug_max_document_response_bytes() + 1) + "</body></html>"
                        val rejected = session.commit_network_response(BrowserResponse.create(
                            request_id: request.id,
                            kind: "document",
                            url: request.url,
                            status: 200,
                            headers: "Set-Cookie: token=oversized; Path=/\n",
                            body: oversized_html,
                            error: ""
                        ))
                        match rejected:
                            Ok(_):
                                fail("Expected oversized network document response to be rejected")
                            Err(err):
                                expect(err).to_contain("document response exceeds browser session limit")
                                expect(session.current_url).to_equal("https://example.com/safe.html")
                                expect(session.current_body_html).to_contain("safe")
                                val cookie_result = session.eval_script("document.cookie")
                                match cookie_result:
                                    Ok(value):
                                        match value:
                                            JsValue.String(cookie):
                                                expect(cookie).to_equal("")
                                            _:
                                                fail("Expected cookie result to be a string")
                                    Err(eval_err):
                                        fail("Expected cookie state to be readable: {eval_err}")
                    nil:
                        fail("Expected pending document request")
            Err(err):
                fail("Expected network navigation to start: {err}")
    Err(err):
        fail("Expected setup page to load: {err}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
