# Browser Session Module Source Bounds Spec

> Inline, external, cached, and override-backed ES modules share module source execution. Oversized module bodies must fail closed without applying partial runtime side effects or growing the module cache.

<!-- sdn-diagram:id=browser_session_module_source_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_module_source_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_module_source_bounds_spec -> std
browser_session_module_source_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_module_source_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Module Source Bounds Spec

Inline, external, cached, and override-backed ES modules share module source execution. Oversized module bodies must fail closed without applying partial runtime side effects or growing the module cache.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_module_source_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Inline, external, cached, and override-backed ES modules share module source
execution. Oversized module bodies must fail closed without applying partial
runtime side effects or growing the module cache.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and browser-session warning/body assertions.

## Scenarios

### BrowserSessionModuleSourceBounds

#### rejects oversized inline module source before side effects

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `1`
   - Expected: session.loaded_module_urls.len() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body>safe<script type='module'>document.body.textContent = 'changed';\n" + _oversized_module_source() + "</script></body></html>"
val result = session.open_html("https://example.com/inline-module-too-large.html", html)

match result:
    Ok(_):
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("module source exceeds browser session limit")
        expect(session.current_body_html).to_contain("safe")
        expect(session.loaded_module_urls.len()).to_equal(0)
    Err(err):
        fail("Expected oversized inline module page to load with warning: {err}")
```

</details>

#### rejects oversized external module responses before caching or side effects

- var session = BrowserSession new
- Ok
- Some
   - Expected: request.kind equals `module`
   - Expected: request.url equals `https://example.com/too-large.mjs`
- body: "document body textContent = 'changed';\n" +  oversized module source
- Ok
   - Expected: session.warnings.len() equals `1`
   - Expected: session.loaded_module_urls.len() equals `0`
   - Expected: session.module_source_cache.len() equals `0`
- Err
- fail
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body>safe<script type='module' src='/too-large.mjs'></script><script>var moduleAfter = 'ran';</script></body></html>"
val result = session.open_html("https://example.com/external-module-too-large.html", html)

match result:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("module")
                expect(request.url).to_equal("https://example.com/too-large.mjs")
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "module",
                    url: request.url,
                    status: 200,
                    headers: "Content-Type: text/javascript\n",
                    body: "document.body.textContent = 'changed';\n" + _oversized_module_source(),
                    error: ""
                ))
                match committed:
                    Ok(_):
                        expect(session.warnings.len()).to_equal(1)
                        expect(session.warnings[0]).to_contain("module source exceeds browser session limit")
                        expect(session.current_body_html).to_contain("safe")
                        expect(session.loaded_module_urls.len()).to_equal(0)
                        expect(session.module_source_cache.len()).to_equal(0)
                    Err(err):
                        fail("Expected oversized external module response to commit with warning: {err}")
            nil:
                fail("Expected pending external module request")
    Err(err):
        fail("Expected oversized external module page to start loading: {err}")
```

</details>

#### records external module transport errors before continuing later scripts

- var session = BrowserSession new
- Ok
- Some
   - Expected: request.kind equals `module`
   - Expected: request.url equals `https://example.com/missing.mjs`
- Ok
   - Expected: session.warnings.len() equals `1`
   - Expected: session.warnings[0] equals `module load error: network unavailable`
   - Expected: session.loaded_module_urls.len() equals `0`
   - Expected: session.module_source_cache.len() equals `0`
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

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body>safe<script type='module' src='/missing.mjs'></script><script>var moduleAfterError = 'ran';</script></body></html>"
val result = session.open_html("https://example.com/external-module-error.html", html)

match result:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("module")
                expect(request.url).to_equal("https://example.com/missing.mjs")
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "module",
                    url: request.url,
                    status: 503,
                    headers: "Content-Type: text/javascript\n",
                    body: "",
                    error: "network unavailable"
                ))
                match committed:
                    Ok(_):
                        expect(session.warnings.len()).to_equal(1)
                        expect(session.warnings[0]).to_equal("module load error: network unavailable")
                        expect(session.loaded_module_urls.len()).to_equal(0)
                        expect(session.module_source_cache.len()).to_equal(0)
                        val js_result = session.eval_script("moduleAfterError")
                        match js_result:
                            Ok(value):
                                expect(_display_js(value)).to_equal("ran")
                            Err(err):
                                fail("Expected later script after module transport error to run: {err}")
                    Err(err):
                        fail("Expected module transport error to commit with warning: {err}")
            nil:
                fail("Expected pending external module request")
    Err(err):
        fail("Expected external module error page to start loading: {err}")
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
