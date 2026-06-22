# Browser Session Simple Script Specification

> <details>

<!-- sdn-diagram:id=browser_session_simple_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_simple_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_simple_script_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_simple_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Simple Script Specification

## Scenarios

### BrowserSession Simple script support

#### runs text simple beside JavaScript and WebAssembly globals

- var session = BrowserSession new
- Ok
   - Expected: session.current_title equals `SimpleScriptReady`
   - Expected: session.current_body_html equals `simple script beside js`
   - Expected: session.warnings.len() equals `0`
- Err
   - Expected: "unexpected load error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `object:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script>var js_ok = 40 + 2;</script><script type='text/simple'>title \"SimpleScriptReady\"\nbody_text \"simple script beside js\"</script></body></html>"
val result = session.open_html("https://example.com/simple-script.html", html)
match result:
    Ok(_):
        expect(session.current_title).to_equal("SimpleScriptReady")
        expect(session.current_body_html).to_equal("simple script beside js")
        expect(session.warnings.len()).to_equal(0)
    Err(err):
        expect("unexpected load error: {err}").to_equal("")

val wasm_result = session.eval_script("typeof WebAssembly + ':' + typeof WebAssembly.instantiate + ':' + js_ok")
match wasm_result:
    Ok(value):
        expect(_display_js(value)).to_equal("object:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### records Simple 2D command evidence from text simple

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `0`
- Err
   - Expected: "unexpected load error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script type='text/simple'>simple2d.fill_rect 4 6 20 10 255\nsimple2d.text 8|16|\"simple 2d\"|12|16777215</script></body></html>"
val result = session.open_html("https://example.com/simple-2d.html", html)
match result:
    Ok(_):
        expect(session.current_body_html).to_contain("\"op\":\"fillRect\"")
        expect(session.current_body_html).to_contain("\"op\":\"fillText\"")
        expect(session.current_body_html).to_contain("simple 2d")
        expect(session.warnings.len()).to_equal(0)
    Err(err):
        expect("unexpected load error: {err}").to_equal("")
```

</details>

#### records Simple 3D WebGPU upload evidence from text simple

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `0`
- Err
   - Expected: "unexpected load error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script type='text/simple'>simple3d.clear_color 255\nsimple3d.camera_perspective 60 1 1000\nsimple3d.triangle 0 1 0 -1 -1 0 1 -1 0 65535\nsimple3d.submit_webgpu</script></body></html>"
val result = session.open_html("https://example.com/simple-3d.html", html)
match result:
    Ok(_):
        expect(session.current_body_html).to_contain("\"status\":\"submitted-webgpu-3d-scene-upload\"")
        expect(session.current_body_html).to_contain("\"type\":\"simple3d\"")
        expect(session.current_body_html).to_contain("\"op\":\"triangle\"")
        expect(session.current_body_html).to_contain("\"triangles\":1")
        expect(session.current_body_html).to_contain("\"scenePayloadBytes\":217")
        expect(session.current_body_html).to_contain("\"scenePayloadChecksum\":7331173752178674817")
        expect(session.warnings.len()).to_equal(0)
    Err(err):
        expect("unexpected load error: {err}").to_equal("")
```

</details>

#### reports unsupported Simple script commands without running them as JavaScript

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `1`
- Err
   - Expected: "unexpected load error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script type='text/simple'>unknown_command 1 2 3</script></body></html>"
val result = session.open_html("https://example.com/simple-script-error.html", html)
match result:
    Ok(_):
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("simple script unsupported command")
    Err(err):
        expect("unexpected load error: {err}").to_equal("")
```

</details>

#### reports malformed Simple drawing numbers without partial evidence

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `1`
- Err
   - Expected: "unexpected load error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script type='text/simple'>body_text \"safe\"\nsimple2d.fill_rect 4 nope 20 10 255</script></body></html>"
val result = session.open_html("https://example.com/simple-script-numeric-error.html", html)
match result:
    Ok(_):
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("simple2d.fill_rect numeric argument is invalid")
    Err(err):
        expect("unexpected load error: {err}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_simple_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession Simple script support

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
