# Browser Session Stylesheet Body Bounds Spec

> Inline and external stylesheet bodies pass through `expand_stylesheet_text` before the session appends style HTML or inserts imported stylesheet sources. Oversized bodies must fail closed at that shared expansion point.

<!-- sdn-diagram:id=browser_session_stylesheet_body_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_stylesheet_body_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_stylesheet_body_bounds_spec -> std
browser_session_stylesheet_body_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_stylesheet_body_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Stylesheet Body Bounds Spec

Inline and external stylesheet bodies pass through `expand_stylesheet_text` before the session appends style HTML or inserts imported stylesheet sources. Oversized bodies must fail closed at that shared expansion point.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_stylesheet_body_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Inline and external stylesheet bodies pass through `expand_stylesheet_text`
before the session appends style HTML or inserts imported stylesheet sources.
Oversized bodies must fail closed at that shared expansion point.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct expansion assertions.

## Scenarios

### BrowserSessionStylesheetBodyBounds

#### rejects oversized stylesheet bodies before html or import expansion

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val oversized = str_repeat("@import url('theme.css');\n.body { color: red; }\n", browser_session_debug_max_stylesheet_bytes() / 8)
val rejected = expand_stylesheet_text("https://example.com/index.html", "https://example.com/app.css", oversized)
expect(rejected.html).to_equal("")
expect(rejected.sources.len()).to_equal(0)

val accepted = expand_stylesheet_text("https://example.com/index.html", "https://example.com/app.css", ".body { color: red; }")
expect(accepted.html).to_contain("<style>")
expect(accepted.html).to_contain("color: red")
```

</details>

#### rejects oversized external stylesheet responses before style html or import fanout

- var session = BrowserSession new
- Ok
- Some
   - Expected: request.kind equals `style`
   - Expected: request.url equals `https://example.com/app.css`
- Ok
   - Expected: session.current_style_html equals ``
- Some
- fail
- Err
- fail
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><head><link rel='stylesheet' href='/app.css'></head><body>safe</body></html>"
val opened = session.open_html("https://example.com/external-style-too-large.html", html)

match opened:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("style")
                expect(request.url).to_equal("https://example.com/app.css")
                val oversized = str_repeat("@import url('theme.css');\n.body { color: red; }\n", browser_session_debug_max_stylesheet_bytes() / 8)
                expect(oversized.len()).to_be_greater_than(browser_session_debug_max_stylesheet_bytes())
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "style",
                    url: request.url,
                    status: 200,
                    headers: "Content-Type: text/css\n",
                    body: oversized,
                    error: ""
                ))
                match committed:
                    Ok(_):
                        expect(session.current_body_html).to_contain("safe")
                        expect(session.current_style_html).to_equal("")
                        match session.take_pending_request():
                            Some(next_request):
                                fail("Expected oversized stylesheet to avoid import fanout, found pending request: {next_request.url}")
                            nil:
                                pass_dn
                    Err(err):
                        fail("Expected oversized external stylesheet response to commit closed: {err}")
            nil:
                fail("Expected pending external stylesheet request")
    Err(err):
        fail("Expected external stylesheet page to start loading: {err}")
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
