# WebGPU JS WASM Simple System Evidence

> This executable system manual covers the active GUI hardening JS/WebEngine/WASM lane. It verifies secure WebGPU exposure, canvas WebGPU context behavior, Simple 2D and Simple 3D command facades, software WebGPU command replay, BrowserSession JavaScript and Simple-script integration, WebAssembly validation/compile/instantiate behavior, fetched WASM byte chains, bounded WASM exports, traps, memory/table/global export metadata, imported function binding, and typed-array/DataView access to WebAssembly.Memory. It also covers bounded declared `webgpu.requestAdapter`, `webgpu.dispatch`, and `webgpu.writeBuffer` host-import callbacks from WASM into JavaScript, including dispatch callbacks that receive WASM-provided `x/y/z` workgroup dimensions, buffer callbacks that receive WASM-provided byte payloads, and exported WebAssembly.Memory buffers that expose WASM stores to host callback code. It also proves a bounded software WebGPU device queue where `device.createBuffer` creates an observable buffer and `device.queue.writeBuffer` copies bytes from a `Uint8Array` into that buffer with count, offset, length, and checksum evidence.

<!-- sdn-diagram:id=webgpu_js_wasm_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_js_wasm_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_js_wasm_simple_spec -> std
webgpu_js_wasm_simple_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_js_wasm_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 127 | 127 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WebGPU JS WASM Simple System Evidence

This executable system manual covers the active GUI hardening JS/WebEngine/WASM lane. It verifies secure WebGPU exposure, canvas WebGPU context behavior, Simple 2D and Simple 3D command facades, software WebGPU command replay, BrowserSession JavaScript and Simple-script integration, WebAssembly validation/compile/instantiate behavior, fetched WASM byte chains, bounded WASM exports, traps, memory/table/global export metadata, imported function binding, and typed-array/DataView access to WebAssembly.Memory. It also covers bounded declared `webgpu.requestAdapter`, `webgpu.dispatch`, and `webgpu.writeBuffer` host-import callbacks from WASM into JavaScript, including dispatch callbacks that receive WASM-provided `x/y/z` workgroup dimensions, buffer callbacks that receive WASM-provided byte payloads, and exported WebAssembly.Memory buffers that expose WASM stores to host callback code. It also proves a bounded software WebGPU device queue where `device.createBuffer` creates an observable buffer and `device.queue.writeBuffer` copies bytes from a `Uint8Array` into that buffer with count, offset, length, and checksum evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | .spipe/browser-wasm-webgpu-infra/state.md |
| Plan | doc/03_plan/platform/webgpu_js_wasm_simple.md |
| Design | doc/05_design/browser_wasm_webgpu_infra.md |
| Research | doc/01_research/local/browser_wasm_webgpu_infra.md |
| Source | `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This executable system manual covers the active GUI hardening JS/WebEngine/WASM
lane. It verifies secure WebGPU exposure, canvas WebGPU context behavior,
Simple 2D and Simple 3D command facades, software WebGPU command replay,
BrowserSession JavaScript and Simple-script integration,
WebAssembly validation/compile/instantiate behavior, fetched WASM byte chains,
bounded WASM exports, traps, memory/table/global export metadata, imported
function binding, and typed-array/DataView access to WebAssembly.Memory. It
also covers bounded declared `webgpu.requestAdapter`, `webgpu.dispatch`, and
`webgpu.writeBuffer` host-import callbacks from WASM into JavaScript, including
dispatch callbacks that receive WASM-provided `x/y/z` workgroup dimensions,
buffer callbacks that receive WASM-provided byte payloads, and exported
WebAssembly.Memory buffers that expose WASM stores to host callback code. It
also proves a bounded software WebGPU device queue where `device.createBuffer`
creates an observable buffer and `device.queue.writeBuffer` copies bytes from a
`Uint8Array` into that buffer with count, offset, length, and checksum evidence.

## Examples

Representative browser evidence includes `WebAssembly.instantiate` returning
`status=instantiated`, exported WASM functions returning bounded numeric values
or fail-closed `wasm-trap:*` strings, fetched `/mod.wasm` bytes flowing through
`arrayBuffer()` into instantiation, Simple-script `simple2d.*` and `simple3d.*`
commands becoming structured browser evidence, and WebAssembly.Memory bytes
being shared with `Uint8Array` and `DataView` views. Bounded WebGPU host-import
examples call declared `webgpu.requestAdapter`, `webgpu.dispatch`, and
`webgpu.writeBuffer` callbacks from WASM exports, including WebGPU-like void
dispatch calls, Simple2D rectangle payload bytes, and `Uint8Array` reads from
`i.exports.memory.buffer`. Browser-shaped queue evidence resolves
`adapter.requestDevice`, creates a bounded buffer, records a queue upload from
typed-array backing storage into observable buffer bytes, and forwards
WASM-originated Simple2D fill payload bytes into a WebGPU compute pass.

**Requirements:** .spipe/browser-wasm-webgpu-infra/state.md
**Plan:** doc/03_plan/platform/webgpu_js_wasm_simple.md
**Architecture:** doc/04_architecture/browser_wasm_webgpu_infra.md
**Design:** doc/05_design/browser_wasm_webgpu_infra.md
**Research:** doc/01_research/local/browser_wasm_webgpu_infra.md

## Scenarios

### WebGPU JS WASM Simple system examples

### REQ-WGPU-001: secure context exposure

#### should expose navigator gpu metadata to secure JavaScript pages

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:object:true`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu.html", "<html><body>GPU</body></html>")

val result = session.eval_script("window.isSecureContext + ':' + typeof navigator.gpu + ':' + navigator.gpu.adapterAvailable")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:object:true")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should hide navigator gpu from insecure JavaScript pages

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `false:undefined`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("http://example.com/webgpu.html", "<html><body>GPU</body></html>")

val result = session.eval_script("window.isSecureContext + ':' + typeof navigator.gpu")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("false:undefined")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose requestAdapter as a JavaScript function shape

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `available:function`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu.html", "<html><body>GPU</body></html>")

val result = session.eval_script("navigator.gpu.requestAdapterStatus + ':' + typeof navigator.gpu.requestAdapter")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("available:function")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

### REQ-WGPU-002: canvas WebGPU context

#### should expose Simple 2D drawing evidence beside WebGPU canvas wrappers

- var simple2d = canvas get context simple2d
- simple2d fill rect
- simple2d text
   - Expected: summary.command_count equals `2`
   - Expected: summary.last_kind equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var simple2d = canvas_get_context_simple2d(320, 240)
simple2d.fill_rect(8, 12, 40, 24, 0xFF336699)
simple2d.text(16, 32, "simple wasm webgpu", 14, 0xFFFFFFFF)

val summary = simple2d.summary()
expect(summary.command_count).to_equal(2)
expect(summary.last_kind).to_equal("text")
expect(summary.canvas2d_json).to_contain("\"op\":\"fillRect\"")
expect(summary.canvas2d_json).to_contain("\"op\":\"fillText\"")
expect(summary.canvas2d_json).to_contain("simple wasm webgpu")
```

</details>

#### should submit Simple 2D commands through the WebGPU render path

- var simple2d = canvas get context simple2d
- simple2d fill rect
- simple2d text
   - Expected: evidence.status equals `submitted-webgpu-render`
   - Expected: evidence.command_count equals `2`
   - Expected: evidence.queue_write_count equals `1`
   - Expected: evidence.render_pass_count equals `1`
   - Expected: evidence.draw_call_count equals `1`
   - Expected: evidence.present_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var simple2d = canvas_get_context_simple2d(320, 240)
simple2d.fill_rect(8, 12, 40, 24, 0xFF336699)
simple2d.text(16, 32, "simple wasm webgpu", 14, 0xFFFFFFFF)

val evidence = simple2d.submit_to_webgpu(true)
expect(evidence.available).to_be(true)
expect(evidence.submitted).to_be(true)
expect(evidence.status).to_equal("submitted-webgpu-render")
expect(evidence.command_count).to_equal(2)
expect(evidence.queue_write_count).to_equal(1)
expect(evidence.render_pass_count).to_equal(1)
expect(evidence.draw_call_count).to_equal(1)
expect(evidence.present_count).to_equal(1)
expect(evidence.pipeline_valid).to_be(true)
expect(evidence.canvas2d_json).to_contain("\"op\":\"fillRect\"")
expect(evidence.summary()).to_contain("render_passes=1")
```

</details>

#### should expose Simple 3D command evidence beside WebGPU canvas wrappers

- var simple3d = canvas get context simple3d
- simple3d clear color
- simple3d camera perspective
- simple3d triangle
   - Expected: summary.command_count equals `3`
   - Expected: summary.triangle_count equals `1`
   - Expected: summary.last_kind equals `triangle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var simple3d = canvas_get_context_simple3d(640, 480)
simple3d.clear_color(255)
simple3d.camera_perspective(60, 1, 1000)
simple3d.triangle(0, 1, 0, -1, -1, 0, 1, -1, 0, 65535)

val summary = simple3d.summary()
expect(summary.command_count).to_equal(3)
expect(summary.triangle_count).to_equal(1)
expect(summary.last_kind).to_equal("triangle")
expect(summary.scene3d_json).to_contain("\"type\":\"simple3d\"")
expect(summary.scene3d_json).to_contain("\"op\":\"triangle\"")
expect(summary.scene3d_json).to_contain("\"op\":\"cameraPerspective\"")
```

</details>

#### should submit encoded Simple 3D scene commands through the WebGPU path

- var simple3d = canvas get context simple3d
- simple3d clear color
- simple3d triangle
   - Expected: evidence.status equals `submitted-webgpu-3d-scene-upload`
   - Expected: evidence.command_count equals `2`
   - Expected: evidence.triangle_count equals `1`
   - Expected: evidence.queue_write_count equals `1`
   - Expected: evidence.render_pass_count equals `1`
   - Expected: evidence.draw_call_count equals `1`
   - Expected: evidence.present_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var simple3d = canvas_get_context_simple3d(640, 480)
simple3d.clear_color(255)
simple3d.triangle(0, 1, 0, -1, -1, 0, 1, -1, 0, 65535)

val evidence = simple3d.submit_to_webgpu(true)
expect(evidence.available).to_be(true)
expect(evidence.submitted).to_be(true)
expect(evidence.status).to_equal("submitted-webgpu-3d-scene-upload")
expect(evidence.command_count).to_equal(2)
expect(evidence.triangle_count).to_equal(1)
expect(evidence.scene_payload_bytes).to_be_greater_than(0)
expect(evidence.scene_payload_checksum).to_be_greater_than(0)
expect(evidence.queue_write_count).to_equal(1)
expect(evidence.render_pass_count).to_equal(1)
expect(evidence.draw_call_count).to_equal(1)
expect(evidence.present_count).to_equal(1)
expect(evidence.pipeline_valid).to_be(true)
expect(evidence.scene3d_json).to_contain("\"op\":\"triangle\"")
expect(evidence.summary()).to_contain("scene_checksum=")
```

</details>

#### should not silently report WebGPU for BrowserRenderer fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.create_with_backend(320, 240, "webgpu")
expect(renderer.backend_name()).to_equal("software")
```

</details>

#### should configure and present a secure WebGPU canvas

- var ctx = canvas get context webgpu
   - Expected: ctx.is_available() is true
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: ctx.present() is true
   - Expected: ctx.gpu.present_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.is_available()).to_equal(true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)
expect(ctx.present()).to_equal(true)
expect(ctx.gpu.present_count).to_equal(1)
```

</details>

#### should reject WebGPU canvas device requests from insecure pages

- var ctx = canvas get context webgpu
   - Expected: ctx.is_available() is false
   - Expected: ctx.request_device() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, false)
expect(ctx.is_available()).to_equal(false)
expect(ctx.request_device()).to_equal(false)
```

</details>

#### should create render and compute pipeline handles through the canvas wrapper

- var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: rp.valid is true
   - Expected: cp.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)

val vs = ctx.create_shader_module("vs", "@vertex fn main() -> @builtin(position) vec4f { return vec4f(0.0, 0.0, 0.0, 1.0); }")
val fs = ctx.create_shader_module("fs", "@fragment fn main() -> @location(0) vec4f { return vec4f(0.0, 1.0, 0.0, 1.0); }")
val cs = ctx.create_shader_module("cs", "@compute @workgroup_size(1) fn main() { }")
val rp = ctx.create_render_pipeline(vs, fs)
val cp = ctx.create_compute_pipeline(cs)
expect(rp.valid).to_equal(true)
expect(cp.valid).to_equal(true)
```

</details>

### REQ-WGPU-003 and REQ-WGPU-004: Simple script resource and executor path

#### should execute a Simple-script compute upload through the software executor

- var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: cp.valid is true
   - Expected: gpu_ctx.queue_write_buffer(buffer.id, 0, 32) is true
- var encoder = gpu ctx create command encoder
   - Expected: encoder.begin_compute_pass() is true
   - Expected: encoder.set_pipeline(cp.id) is true
   - Expected: encoder.dispatch_workgroups(4, 1, 1) is true
   - Expected: encoder.end_compute_pass() is true
   - Expected: gpu_ctx.queue_submit([command_buffer]) is true
   - Expected: result.valid is true
   - Expected: result.queue_write_count equals `1`
   - Expected: result.compute_pass_count equals `1`
   - Expected: result.dispatched_workgroups equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)

var gpu_ctx: WebGPUContext = ctx.gpu
var resources = gpu_ctx.resources
val buffer = resources.create_buffer("storage", 64, WEBGPU_BUFFER_USAGE_COPY_DST_FOR_SPEC)
gpu_ctx.resources = resources

val cs = ctx.create_shader_module("cs", "@compute @workgroup_size(1) fn main() { }")
val cp = ctx.create_compute_pipeline(cs)
expect(cp.valid).to_equal(true)
expect(gpu_ctx.queue_write_buffer(buffer.id, 0, 32)).to_equal(true)

var encoder = gpu_ctx.create_command_encoder("compute")
expect(encoder.begin_compute_pass()).to_equal(true)
expect(encoder.set_pipeline(cp.id)).to_equal(true)
expect(encoder.dispatch_workgroups(4, 1, 1)).to_equal(true)
expect(encoder.end_compute_pass()).to_equal(true)

val command_buffer = encoder.finish("compute-commands")
expect(gpu_ctx.queue_submit([command_buffer])).to_equal(true)

val result = webgpu_software_execute_queue(gpu_ctx.queue)
expect(result.valid).to_equal(true)
expect(result.queue_write_count).to_equal(1)
expect(result.compute_pass_count).to_equal(1)
expect(result.dispatched_workgroups).to_equal(4)
```

</details>

#### should reject invalid Simple-script queue writes before executor replay

- var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: gpu_ctx.queue_write_buffer(999, 0, 32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)

var gpu_ctx: WebGPUContext = ctx.gpu
expect(gpu_ctx.queue_write_buffer(999, 0, 32)).to_equal(false)
expect(gpu_ctx.last_error).to_contain("does not exist")
```

</details>

#### should reject command submission after device loss

- var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: lost.lost is true
- var encoder = ctx gpu create command encoder
   - Expected: ctx.gpu.queue_submit([command_buffer]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
val lost = ctx.gpu.lose_device("test reset")
expect(lost.lost).to_equal(true)

var encoder = ctx.gpu.create_command_encoder("after-loss")
val command_buffer = encoder.finish("after-loss")
expect(ctx.gpu.queue_submit([command_buffer])).to_equal(false)
expect(ctx.gpu.last_error).to_contain("device is lost")
```

</details>

### REQ-WGPU-005: JavaScript integration remains available

#### should run ordinary JavaScript beside WebGPU globals

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `42:bgra8unorm`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu.html", "<html><body><div id='out'></div></body></html>")

val result = session.eval_script("var x = 40 + 2; x + ':' + navigator.gpu.preferredCanvasFormat")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("42:bgra8unorm")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should run Simple script beside JavaScript and WebAssembly globals

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

#### should expose Simple script 2D command evidence in the browser session

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

#### should expose Simple script 3D WebGPU scene upload evidence in the browser session

- var session = BrowserSession new
- Ok
   - Expected: session.warnings.len() equals `0`
- Err
   - Expected: "unexpected load error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
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
        expect(session.current_body_html).to_contain("\"scenePayloadChecksum\":")
        expect(session.warnings.len()).to_equal(0)
    Err(err):
        expect("unexpected load error: {err}").to_equal("")
```

</details>

### REQ-WGPU-006: WASM backend smoke

#### should compile an empty Simple MIR module to WAT for wasm32

- var adapter = WasmCodegenAdapter
- Ok
- Err
   - Expected: "compilation failed: {err.message}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = WasmCodegenAdapter(options: _wasm32_options())
val result = adapter.compile_module(_empty_mir_module())
match result:
    Ok(output):
        expect(output.text_output).to_contain("(module")
    Err(err):
        expect("compilation failed: {err.message}").to_equal("")
```

</details>

#### should report wasm32 target support in the adapter

- var adapter = WasmCodegenAdapter
   - Expected: adapter.supports_target(CodegenTarget.Wasm32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = WasmCodegenAdapter(options: _wasm32_options())
expect(adapter.supports_target(CodegenTarget.Wasm32)).to_equal(true)
```

</details>

#### should reject x86_64 target support in the wasm adapter

- var adapter = WasmCodegenAdapter
   - Expected: adapter.supports_target(CodegenTarget.X86_64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = WasmCodegenAdapter(options: _wasm32_options())
expect(adapter.supports_target(CodegenTarget.X86_64)).to_equal(false)
```

</details>

### REQ-WGPU-007: browser WASM to WebGPU bridge

#### should expose the browser WebAssembly host object beside WebGPU

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `object:function:function:function:available:bgra8unorm`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("typeof WebAssembly + ':' + typeof WebAssembly.instantiate + ':' + typeof WebAssembly.validate + ':' + typeof WebAssembly.compile + ':' + WebAssembly.instantiateStatus + ':' + navigator.gpu.preferredCanvasFormat")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("object:function:function:function:available:bgra8unorm")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should validate and instantiate WASM inputs through the hardened JS host

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:false:false:instantiated:invalid`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("WebAssembly.validate('0061736d01000000') + ':' + WebAssembly.validate('0061736d') + ':' + WebAssembly.validate('0061736d00000000') + ':' + WebAssembly.instantiate('0061736d01000000').status + ':' + WebAssembly.instantiate('0061736d00000000').status")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:false:false:instantiated:invalid")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should validate and instantiate byte-array WASM inputs through the JS host

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:false:instantiated`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("WebAssembly.validate([0,97,115,109,1,0,0,0]) + ':' + WebAssembly.validate([0,97,115,109,0,0,0,0]) + ':' + WebAssembly.instantiate([0,97,115,109,1,0,0,0]).status")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:false:instantiated")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should validate Uint8Array WASM inputs through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `function:function:true:8`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("typeof ArrayBuffer + ':' + typeof Uint8Array + ':' + WebAssembly.validate(new Uint8Array([0,97,115,109,1,0,0,0])) + ':' + WebAssembly.instantiate(new Uint8Array([0,97,115,109,1,0,0,0])).module.byteLength")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:function:true:8")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should validate TextEncoder-produced WASM bytes through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `function:function:wasm:true`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("typeof TextEncoder + ':' + typeof TextDecoder + ':' + new TextDecoder().decode(new TextEncoder().encode('wasm')) + ':' + WebAssembly.validate(new TextEncoder().encode('\\u0000asm\\u0001\\u0000\\u0000\\u0000'))")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:function:wasm:true")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should validate TextEncoder encodeInto WASM bytes through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `8:8:true`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var dst = new Uint8Array(8); var r = new TextEncoder().encodeInto('\\u0000asm\\u0001\\u0000\\u0000\\u0000', dst); r.read + ':' + r.written + ':' + WebAssembly.validate(dst)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("8:8:true")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose bounded WASM section metadata through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `1:true:invalid-wasm-section`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("WebAssembly.instantiate('0061736d01000000010100').module.sectionCount + ':' + WebAssembly.instantiate('0061736d01000000010100').module.hasTypeSection + ':' + WebAssembly.instantiate('0061736d010000000105').error")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:true:invalid-wasm-section")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose bounded Module and Instance constructors through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `1:true:instantiated:object`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d01000000010100'); var i = new WebAssembly.Instance(m); m.sectionCount + ':' + m.hasTypeSection + ':' + i.status + ':' + typeof i.exports")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:true:instantiated:object")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose thenable WebAssembly.instantiate result shape through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `function:function:instantiated:1:object`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var r = WebAssembly.instantiate('0061736d01000000010100'); typeof r.then + ':' + typeof r.catch + ':' + r.status + ':' + r.module.sectionCount + ':' + typeof r.instance.exports")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:function:instantiated:1:object")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should resolve WebAssembly.instantiate then callbacks through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `instantiated:1:object`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("WebAssembly.instantiate('0061736d01000000010100').then(function(r) { return r.status + ':' + r.module.sectionCount + ':' + typeof r.instance.exports; })")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:1:object")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should chain fetch arrayBuffer bytes into WebAssembly.instantiate through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `queued`
- Err
   - Expected: "unexpected queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals ``
- Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``
- Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`
- Ok
- Ok
   - Expected: _display_js(value) equals `fetch>arrayBuffer:11>instantiate:instantiated:11:1:object`
- Err
   - Expected: "unexpected js error: {err}" equals ``
- Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes); }).then(function(result) { out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + result.module.sectionCount + ':' + typeof result.instance.exports; }); 'queued'")
match queued:
    Ok(value):
        expect(_display_js(value)).to_equal("queued")
    Err(err):
        expect("unexpected queue error: {err}").to_equal("")
match session.eval_script("out"):
    Ok(value):
        expect(_display_js(value)).to_equal("")
    Err(err):
        expect("unexpected pre-commit js error: {err}").to_equal("")

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
                val result = session.eval_script("out")
                match result:
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:11>instantiate:instantiated:11:1:object")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### should chain fetched WASM instantiation into JS WebGPU globals through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `queued`
- Err
   - Expected: "unexpected queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals ``
- Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``
- Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`
- Ok
- Ok
   - Expected: _display_js(value) equals `instantiated:11:true:bgra8unorm:function`
- Err
   - Expected: "unexpected js error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals ``
- Err
   - Expected: "unexpected adapter queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `Simple WebGPU Software Adapter:true:function`
- Err
   - Expected: "unexpected adapter js error: {err}" equals ``
- Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val queued = session.eval_script("var out = ''; var adapterName = ''; window.fetch('/mod.wasm').then(function(r) { return r.arrayBuffer(); }).then(function(bytes) { return WebAssembly.instantiate(bytes); }).then(function(wasm) { out = wasm.status + ':' + wasm.module.byteLength + ':' + navigator.gpu.softwareFallback + ':' + navigator.gpu.preferredCanvasFormat + ':' + typeof navigator.gpu.requestAdapter; }); 'queued'")
match queued:
    Ok(value):
        expect(_display_js(value)).to_equal("queued")
    Err(err):
        expect("unexpected queue error: {err}").to_equal("")
match session.eval_script("out"):
    Ok(value):
        expect(_display_js(value)).to_equal("")
    Err(err):
        expect("unexpected pre-commit js error: {err}").to_equal("")

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
                val result = session.eval_script("out")
                match result:
                    Ok(value):
                        expect(_display_js(value)).to_equal("instantiated:11:true:bgra8unorm:function")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
                match session.eval_script("navigator.gpu.requestAdapter().then(function(adapter) { adapterName = adapter.name + ':' + adapter.isFallbackAdapter + ':' + typeof adapter.requestDevice; }); adapterName"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("")
                    Err(err):
                        expect("unexpected adapter queue error: {err}").to_equal("")
                match session.eval_script("adapterName"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("Simple WebGPU Software Adapter:true:function")
                    Err(err):
                        expect("unexpected adapter js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### should assimilate nested WebGPU promises returned from fetched WASM instantiation callbacks

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `queued`
- Err
   - Expected: "unexpected queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals ``
- Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``
- Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`
- Ok
- Ok
   - Expected: _display_js(value) equals `Simple WebGPU Software Adapter:true:available`
- Err
   - Expected: "unexpected adapter js error: {err}" equals ``
- Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val queued = session.eval_script("var out = ''; window.fetch('/mod.wasm').then(function(r) { return r.arrayBuffer(); }).then(function(bytes) { return WebAssembly.instantiate(bytes); }).then(function(wasm) { return Promise.resolve(navigator.gpu.requestAdapter()); }).then(function(adapter) { out = adapter.name + ':' + adapter.isFallbackAdapter + ':' + adapter.requestAdapterStatus; }); 'queued'")
match queued:
    Ok(value):
        expect(_display_js(value)).to_equal("queued")
    Err(err):
        expect("unexpected queue error: {err}").to_equal("")
match session.eval_script("out"):
    Ok(value):
        expect(_display_js(value)).to_equal("")
    Err(err):
        expect("unexpected pre-commit js error: {err}").to_equal("")

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
                        expect(_display_js(value)).to_equal("Simple WebGPU Software Adapter:true:available")
                    Err(err):
                        expect("unexpected adapter js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### should create a bounded WebGPU buffer and record queue writes through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `adapter-queued`
- Err
   - Expected: "unexpected adapter queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `device-queued`
- Err
   - Expected: "unexpected device queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `function:6:6:8:1:1:3:24:0,6,8,10,0,0:1:1:3:24`
- Err
   - Expected: "unexpected writeBuffer js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-buffer.html", "<html><body>WebGPU Buffer</body></html>")
match session.eval_script("var adapter = null; var device = null; var buffer = null; var upload = ''; navigator.gpu.requestAdapter().then(function(a) { adapter = a; }); 'adapter-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("adapter-queued")
    Err(err):
        expect("unexpected adapter queue error: {err}").to_equal("")
match session.eval_script("adapter.requestDevice().then(function(d) { device = d; }); 'device-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("device-queued")
    Err(err):
        expect("unexpected device queue error: {err}").to_equal("")
val result = session.eval_script("buffer = device.createBuffer({size: 6, usage: 8}); var data = new Uint8Array(new ArrayBuffer(4)); data.buffer[0] = 4; data.buffer[1] = 6; data.buffer[2] = 8; data.buffer[3] = 10; device.queue.writeBuffer(buffer, 1, data, 1, 3); upload = typeof device.createBuffer + ':' + buffer.size + ':' + buffer.byteLength + ':' + buffer.usage + ':' + buffer.writeCount + ':' + buffer.lastWriteOffset + ':' + buffer.lastWriteByteLength + ':' + buffer.lastWriteChecksum + ':' + buffer[0] + ',' + buffer[1] + ',' + buffer[2] + ',' + buffer[3] + ',' + buffer[4] + ',' + buffer[5] + ':' + device.queue.writeCount + ':' + device.queue.lastWriteBufferOffset + ':' + device.queue.lastWriteByteLength + ':' + device.queue.lastWriteChecksum; upload")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:6:6:8:1:1:3:24:0,6,8,10,0,0:1:1:3:24")
    Err(err):
        expect("unexpected writeBuffer js error: {err}").to_equal("")
```

</details>

#### should upload exported WASM memory bytes through a WebGPU device queue

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `adapter-queued`
- Err
   - Expected: "unexpected adapter queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `device-queued`
- Err
   - Expected: "unexpected device queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `3:1:1:4:3:39:0,0,0,0,12,13,14,0:1:4:3:39`
- Err
   - Expected: "unexpected WASM queue writeBuffer js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-queue-wasm.html", "<html><body>WebGPU Queue WASM</body></html>")
match session.eval_script("var adapter = null; var device = null; navigator.gpu.requestAdapter().then(function(a) { adapter = a; }); 'adapter-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("adapter-queued")
    Err(err):
        expect("unexpected adapter queue error: {err}").to_equal("")
match session.eval_script("adapter.requestDevice().then(function(d) { device = d; }); 'device-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("device-queued")
    Err(err):
        expect("unexpected device queue error: {err}").to_equal("")
val result = session.eval_script("var calls = 0; var i; var imports = { webgpu: { writeBuffer: function(ptr, len) { calls = calls + 1; return len; } } }; var m = new WebAssembly.Module('0061736d01000000010b0260027f7f017f6000017f021601067765626770750b77726974654275666665720000030201010503010001071002066d656d6f727902000372756e00010a1f011d004100410c3a00004101410d3a00004102410e3a00004100410310000b'); i = new WebAssembly.Instance(m, imports); var source = new Uint8Array(i.exports.memory.buffer); var target = device.createBuffer({size: 8, usage: 8}); var runResult = i.exports.run(); device.queue.writeBuffer(target, 4, source, 0, 3); runResult + ':' + calls + ':' + target.writeCount + ':' + target.lastWriteOffset + ':' + target.lastWriteByteLength + ':' + target.lastWriteChecksum + ':' + target[0] + ',' + target[1] + ',' + target[2] + ',' + target[3] + ',' + target[4] + ',' + target[5] + ',' + target[6] + ',' + target[7] + ':' + device.queue.writeCount + ':' + device.queue.lastWriteBufferOffset + ':' + device.queue.lastWriteByteLength + ':' + device.queue.lastWriteChecksum")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("3:1:1:4:3:39:0,0,0,0,12,13,14,0:1:4:3:39")
    Err(err):
        expect("unexpected WASM queue writeBuffer js error: {err}").to_equal("")
```

</details>

#### should encode and submit a bounded WebGPU compute dispatch through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `adapter-queued`
- Err
   - Expected: "unexpected adapter queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `device-queued`
- Err
   - Expected: "unexpected device queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `function:function:function:true:wgsl:true:main:true:1:24:true:1:1:24:1:1:1:1:24`
- Err
   - Expected: "unexpected compute dispatch js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-compute-encoder.html", "<html><body>WebGPU Compute Encoder</body></html>")
match session.eval_script("var adapter = null; var device = null; navigator.gpu.requestAdapter().then(function(a) { adapter = a; }); 'adapter-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("adapter-queued")
    Err(err):
        expect("unexpected adapter queue error: {err}").to_equal("")
match session.eval_script("adapter.requestDevice().then(function(d) { device = d; }); 'device-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("device-queued")
    Err(err):
        expect("unexpected device queue error: {err}").to_equal("")
val result = session.eval_script("var shader = device.createShaderModule({code: '@compute @workgroup_size(1) fn main() {}'}); var pipeline = device.createComputePipeline({module: shader, entryPoint: 'main'}); var encoder = device.createCommandEncoder(); var pass = encoder.beginComputePass(); pass.setPipeline(pipeline); pass.dispatchWorkgroups(2, 3, 4); pass.end(); var commands = encoder.finish(); device.queue.submit([commands]); typeof device.createShaderModule + ':' + typeof device.createComputePipeline + ':' + typeof device.createCommandEncoder + ':' + shader.valid + ':' + shader.sourceFormat + ':' + pipeline.valid + ':' + pipeline.entryPoint + ':' + pass.pipelineValid + ':' + pass.dispatchCallCount + ':' + pass.dispatchedWorkgroups + ':' + commands.valid + ':' + commands.computePassCount + ':' + commands.dispatchCallCount + ':' + commands.dispatchedWorkgroups + ':' + device.queue.submitCount + ':' + device.queue.lastSubmitCommandBufferCount + ':' + device.queue.lastSubmitComputePassCount + ':' + device.queue.lastSubmitDispatchCallCount + ':' + device.queue.lastSubmitDispatchedWorkgroups")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:function:function:true:wgsl:true:main:true:1:24:true:1:1:24:1:1:1:1:24")
    Err(err):
        expect("unexpected compute dispatch js error: {err}").to_equal("")
```

</details>

#### should aggregate WebGPU compute counters and ignore invalid active-pass command buffers

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `adapter-queued`
- Err
   - Expected: "unexpected adapter queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `device-queued`
- Err
   - Expected: "unexpected device queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `2:2:5:false:0:0:0:2:0:0:0:0:2:5`
- Err
   - Expected: "unexpected compute aggregate js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-compute-aggregate.html", "<html><body>WebGPU Compute Aggregate</body></html>")
match session.eval_script("var adapter = null; var device = null; navigator.gpu.requestAdapter().then(function(a) { adapter = a; }); 'adapter-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("adapter-queued")
    Err(err):
        expect("unexpected adapter queue error: {err}").to_equal("")
match session.eval_script("adapter.requestDevice().then(function(d) { device = d; }); 'device-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("device-queued")
    Err(err):
        expect("unexpected device queue error: {err}").to_equal("")
val result = session.eval_script("var shader = device.createShaderModule({code: '@compute @workgroup_size(1) fn main() {}'}); var pipeline = device.createComputePipeline({module: shader, entryPoint: 'main'}); var encoder = device.createCommandEncoder(); var pass1 = encoder.beginComputePass(); pass1.setPipeline(pipeline); pass1.dispatchWorkgroups(2, 1, 1); pass1.end(); pass1.dispatchWorkgroups(7, 1, 1); pass1.end(); var pass2 = encoder.beginComputePass(); pass2.setPipeline(pipeline); pass2.dispatchWorkgroups(3, 1, 1); pass2.end(); var validCommands = encoder.finish(); device.queue.submit([validCommands]); var invalidEncoder = device.createCommandEncoder(); var activePass = invalidEncoder.beginComputePass(); activePass.setPipeline(pipeline); activePass.dispatchWorkgroups(9, 1, 1); var invalidCommands = invalidEncoder.finish(); device.queue.submit([invalidCommands]); validCommands.computePassCount + ':' + validCommands.dispatchCallCount + ':' + validCommands.dispatchedWorkgroups + ':' + invalidCommands.valid + ':' + invalidCommands.computePassCount + ':' + invalidCommands.dispatchCallCount + ':' + invalidCommands.dispatchedWorkgroups + ':' + device.queue.submitCount + ':' + device.queue.lastSubmitCommandBufferCount + ':' + device.queue.lastSubmitComputePassCount + ':' + device.queue.lastSubmitDispatchCallCount + ':' + device.queue.lastSubmitDispatchedWorkgroups + ':' + device.queue.computePassCount + ':' + device.queue.dispatchedWorkgroups")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2:2:5:false:0:0:0:2:0:0:0:0:2:5")
    Err(err):
        expect("unexpected compute aggregate js error: {err}").to_equal("")
```

</details>

#### should drive a WebGPU compute pass with WASM-originated dispatch dimensions

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `adapter-queued`
- Err
   - Expected: "unexpected adapter queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `device-queued`
- Err
   - Expected: "unexpected device queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `instantiated:1:1:2x3x4:1:24:1:1:24:1:1:1:1:24`
- Err
   - Expected: "unexpected WASM compute dispatch js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm-compute.html", "<html><body>WebGPU WASM Compute</body></html>")
match session.eval_script("var adapter = null; var device = null; navigator.gpu.requestAdapter().then(function(a) { adapter = a; }); 'adapter-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("adapter-queued")
    Err(err):
        expect("unexpected adapter queue error: {err}").to_equal("")
match session.eval_script("adapter.requestDevice().then(function(d) { device = d; }); 'device-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("device-queued")
    Err(err):
        expect("unexpected device queue error: {err}").to_equal("")
val result = session.eval_script("var shader = device.createShaderModule({code: '@compute @workgroup_size(1) fn main() {}'}); var pipeline = device.createComputePipeline({module: shader, entryPoint: 'main'}); var encoder = device.createCommandEncoder(); var pass = encoder.beginComputePass(); pass.setPipeline(pipeline); var calls = 0; var dims = ''; var imports = { webgpu: { dispatch: function(x, y, z) { calls = calls + 1; dims = x + 'x' + y + 'x' + z; pass.dispatchWorkgroups(x, y, z); } } }; var m = new WebAssembly.Module('0061736d01000000010b0260037f7f7f006000017f021301067765626770750864697370617463680000030201010707010372756e00010a0e010c00410241034104100041010b'); var i = new WebAssembly.Instance(m, imports); var runResult = i.exports.run(); pass.end(); var commands = encoder.finish(); device.queue.submit([commands]); i.status + ':' + runResult + ':' + calls + ':' + dims + ':' + pass.dispatchCallCount + ':' + pass.dispatchedWorkgroups + ':' + commands.computePassCount + ':' + commands.dispatchCallCount + ':' + commands.dispatchedWorkgroups + ':' + device.queue.submitCount + ':' + device.queue.lastSubmitCommandBufferCount + ':' + device.queue.lastSubmitComputePassCount + ':' + device.queue.lastSubmitDispatchCallCount + ':' + device.queue.lastSubmitDispatchedWorkgroups")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:1:1:2x3x4:1:24:1:1:24:1:1:1:1:24")
    Err(err):
        expect("unexpected WASM compute dispatch js error: {err}").to_equal("")
```

</details>

#### should drive a Simple2D fill compute pass from WASM payload bytes

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `adapter-queued`
- Err
   - Expected: "unexpected Simple2D fill adapter queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `device-queued`
- Err
   - Expected: "unexpected Simple2D fill device queue error: {err}" equals ``
- Ok
   - Expected: _display_js(value) equals `instantiated:1242:1:webgpu:writeBuffer:8,0,0,0,210,4,0,0:8:1234:222:true:simp... (full value in folded executable source)`
- Err
   - Expected: "unexpected WASM Simple2D fill compute js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm-simple2d-fill.html", "<html><body>WebGPU WASM Simple2D Fill</body></html>")
match session.eval_script("var adapter = null; var device = null; navigator.gpu.requestAdapter().then(function(a) { adapter = a; }); 'adapter-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("adapter-queued")
    Err(err):
        expect("unexpected Simple2D fill adapter queue error: {err}").to_equal("")
match session.eval_script("adapter.requestDevice().then(function(d) { device = d; }); 'device-queued'"):
    Ok(value):
        expect(_display_js(value)).to_equal("device-queued")
    Err(err):
        expect("unexpected Simple2D fill device queue error: {err}").to_equal("")
val result = session.eval_script("var calls = 0; var payload = ''; var payloadChecksum = 0; var count = 0; var fillValue = 0; var shaderValid = false; var entry = ''; var m; var i; var imports = { webgpu: { writeBuffer: function(ptr, len) { calls = calls + 1; var source = new Uint8Array(i.exports.memory.buffer); payload = source[0] + ',' + source[1] + ',' + source[2] + ',' + source[3] + ',' + source[4] + ',' + source[5] + ',' + source[6] + ',' + source[7]; payloadChecksum = source[0] + source[1] + source[2] + source[3] + source[4] + source[5] + source[6] + source[7]; count = source[0] + source[1] * 256 + source[2] * 65536 + source[3] * 16777216; fillValue = source[4] + source[5] * 256 + source[6] * 65536 + source[7] * 16777216; var shader = device.createShaderModule({code: '@group(0) @binding(1) var<storage, read_write> dst: array<u32>; struct Simple2DParams { value: u32, count: u32, alpha: u32, width: u32, height: u32 }; @group(0) @binding(3) var<uniform> params: Simple2DParams; @compute @workgroup_size(64) fn simple_2d_fill_u32(@builtin(global_invocation_id) global_id: vec3<u32>) { }'}); shaderValid = shader.valid; var pipeline = device.createComputePipeline({module: shader, entryPoint: 'simple_2d_fill_u32'}); entry = pipeline.entryPoint; var encoder = device.createCommandEncoder(); var pass = encoder.beginComputePass(); pass.setPipeline(pipeline); pass.dispatchWorkgroups(count / 8, 1, 1); pass.end(); var commands = encoder.finish(); device.queue.submit([commands]); return count + fillValue; } } }; m = new WebAssembly.Module('0061736d01000000010b0260027f7f017f6000017f021601067765626770750b77726974654275666665720000030201010503010001071002066d656d6f727902000372756e00010a43014100410041083a0000410141003a0000410241003a0000410341003a0000410441d2013a0000410541043a0000410641003a0000410741003a00004100410810000b'); i = new WebAssembly.Instance(m, imports); var runResult = i.exports.run(); i.status + ':' + runResult + ':' + calls + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + payload + ':' + count + ':' + fillValue + ':' + payloadChecksum + ':' + shaderValid + ':' + entry + ':' + device.queue.submitCount + ':' + device.queue.lastSubmitCommandBufferCount + ':' + device.queue.lastSubmitComputePassCount + ':' + device.queue.lastSubmitDispatchCallCount + ':' + device.queue.lastSubmitDispatchedWorkgroups")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:1242:1:webgpu:writeBuffer:8,0,0,0,210,4,0,0:8:1234:222:true:simple_2d_fill_u32:1:1:1:1:1")
    Err(err):
        expect("unexpected WASM Simple2D fill compute js error: {err}").to_equal("")
```

</details>

#### should expose thenable WebAssembly.compile result shape through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `function:function:compiled:1:true`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var r = WebAssembly.compile('0061736d01000000010100'); typeof r.then + ':' + typeof r.catch + ':' + r.status + ':' + r.module.sectionCount + ':' + r.module.hasTypeSection")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:function:compiled:1:true")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on invalid WebAssembly.compile bytes through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `invalid:invalid-wasm-header`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("WebAssembly.compile('0061736d00000000').status + ':' + WebAssembly.compile('0061736d00000000').error")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("invalid:invalid-wasm-header")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose bounded memory exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:1:1:memory:memory:65536`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000503010001070a01066d656d6f72790200'); var i = new WebAssembly.Instance(m); m.hasMemorySection + ':' + m.memoryMinPages + ':' + m.exportCount + ':' + m.firstExportName + ':' + m.firstExportKind + ':' + i.exports.memory.byteLength")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:1:1:memory:memory:65536")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose bounded callable function exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:run:1:function:undefined`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d01000000010401600000030201000707010372756e00000a040102000b'); var i = new WebAssembly.Instance(m); m.firstExportName + ':' + m.firstExportKind + ':' + m.functionExportName + ':' + m.functionExportCount + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:run:1:function:undefined")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose all bounded callable function exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `2:init:render:function:function:undefined:undefined`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d01000000010401600000030302000007110204696e697400000672656e64657200010a070202000b02000b'); var i = new WebAssembly.Instance(m); m.functionExportCount + ':' + m.functionExportName0 + ':' + m.functionExportName1 + ':' + typeof i.exports.init + ':' + typeof i.exports.render + ':' + i.exports.init() + ':' + i.exports.render()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2:init:render:function:function:undefined:undefined")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute a bounded i32.const WASM function export through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a06010400412a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute a bounded signed i32.const WASM function export through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700417f412b6a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute a bounded i32.add WASM function export through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700412841026a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded WASM function exports with call arguments through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d0100000001070160027f7f017f030201000707010372756e00000a09010700200020016a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run(40, 2)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32 local.set WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0f010d01017f41282100200041026a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32 local.tee WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0d010b01017f4128220041026a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32 global.get WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `40:run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000606017f0041280b0707010372756e00000a09010700230041026a0b'); var i = new WebAssembly.Instance(m); m.globalValue + ':' + m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("40:run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded signed i32 global.get WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `-1:run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000606017f00417f0b0707010372756e00000a090107002300412b6a0b'); var i = new WebAssembly.Instance(m); m.globalValue + ':' + m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("-1:run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded mutable i32 global.set WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `42:44:44`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000606017f0141280b0707010372756e00000a0d010b00230041026a240023000b'); var i = new WebAssembly.Instance(m); i.exports.run() + ':' + i.exports.run() + ':' + m.runtimeGlobalValue0")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("42:44:44")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded memory.grow and memory.size WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `2:3:3`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a0b010900410140001a3f000b'); var i = new WebAssembly.Instance(m); i.exports.run() + ':' + i.exports.run() + ':' + m.runtimeMemoryPages")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2:3:3")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should reject WASM memory.grow beyond declared maximum through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `-1:1:2`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000504010101020707010372756e00000a08010600410240000b'); var i = new WebAssembly.Instance(m); i.exports.run() + ':' + m.runtimeMemoryPages + ':' + m.memoryMaxPages")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("-1:1:2")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded memory.fill WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a120110004100412a4104fc0b0041022d00000b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on bounded memory.fill traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a11010f0041808004412a4101fc0b0041000b'); var i = new WebAssembly.Instance(m); i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("wasm-trap:out-of-bounds-memory-access")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded memory.copy WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a1a0118004100412a3a0000410441004101fc0a000041042d00000b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on bounded memory.copy traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a120110004100418080044101fc0a000041000b'); var i = new WebAssembly.Instance(m); i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("wasm-trap:out-of-bounds-memory-access")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded memory.init WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a13011100410041004101fc08000041002d00000b0b040101012a'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on bounded memory.init traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a10010e00410041014101fc08000041000b0b040101012a'); var i = new WebAssembly.Instance(m); i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("wasm-trap:out-of-bounds-memory-access")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded data.drop zero-length memory.init through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a20011e00410041004101fc080000fc0900410141004100fc08000041002d00000b0b040101012a'); var i = new WebAssembly.Instance(m); i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on memory.init after data.drop through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a13011100fc0900410041004101fc08000041000b0b040101012a'); var i = new WebAssembly.Instance(m); i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("wasm-trap:out-of-bounds-memory-access")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.store and i32.load WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a10010e004100412a36020041002802000b'); var i = new WebAssembly.Instance(m); m.hasMemorySection + ':' + m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on WASM out-of-bounds memory traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access:wasm-trap:out-of-bounds-memory-access`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var ml = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a0b010900418080042802000b'); var il = new WebAssembly.Instance(ml); var ms = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a0f010d0041808004412a36020041010b'); var is = new WebAssembly.Instance(ms); il.exports.run() + ':' + is.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("wasm-trap:out-of-bounds-memory-access:wasm-trap:out-of-bounds-memory-access")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.store8 and i32.load8_u WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a11010f00410041aa023a000041002d00000b'); var i = new WebAssembly.Instance(m); m.hasMemorySection + ':' + m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.load8_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:run:function:-86`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a11010f00410041aa013a000041002c00000b'); var i = new WebAssembly.Instance(m); m.hasMemorySection + ':' + m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:run:function:-86")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.store16 and i32.load16_u WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:run:function:4660`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a11010f00410041b4243b010041002f01000b'); var i = new WebAssembly.Instance(m); m.hasMemorySection + ':' + m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:run:function:4660")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.load16_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:run:function:-128`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f0302010005030100010707010372756e00000a1201100041004180ff033b010041002e01000b'); var i = new WebAssembly.Instance(m); m.hasMemorySection + ':' + m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:run:function:-128")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded internal function call WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f03030200000707010372756e00010a0e02040041280b0700100041026a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded internal function call WASM exports with arguments through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d01000000010b0260027f7f017f6000017f03030200010707010372756e00010a12020700200020016a0b08004128410210000b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded early return WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a07010500412a0f0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded drop WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041091a412a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded select WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0b010900412a410741011b0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded if else WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `42:7`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mt = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0e010c004101047f412a0541070b0b'); var it = new WebAssembly.Instance(mt); var mf = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0e010c004100047f412a0541070b0b'); var iff = new WebAssembly.Instance(mf); it.exports.run() + ':' + iff.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("42:7")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded br_if block WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `42:7`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mt = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a10010e00024041010d0041070f0b412a0b'); var it = new WebAssembly.Instance(mt); var mf = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a10010e00024041000d0041070f0b412a0b'); var iff = new WebAssembly.Instance(mf); it.exports.run() + ':' + iff.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("42:7")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

<details>
<summary>Advanced: should execute bounded loop br_if WASM exports through BrowserSession</summary>

#### should execute bounded loop br_if WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a1b011901017f4103210003402000417f6a22000d000b2000412a6a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>


</details>

#### should execute bounded i32.mul and i32.sub WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0c010a00410741086c410e6b0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should wrap bounded i32 arithmetic overflow through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `-2147483648:2147483647:0`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m1 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0d010b0041ffffffff0741016a0b'); var i1 = new WebAssembly.Instance(m1); var m2 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0d010b0041808080807841016b0b'); var i2 = new WebAssembly.Instance(m2); var m3 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0d010b0041808004418080046c0b'); var i3 = new WebAssembly.Instance(m3); i1.exports.run() + ':' + i2.exports.run() + ':' + i3.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("-2147483648:2147483647:0")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.div_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0a01080041d40041026d0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.rem_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:2`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700412a41056f0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:2")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.rem_u WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:2`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700412a4105700b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:2")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on WASM divide by zero traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:integer-divide-by-zero`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700415441006d0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:wasm-trap:integer-divide-by-zero")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on WASM signed division overflow traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:integer-overflow`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0d010b00418080808078417f6d0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:wasm-trap:integer-overflow")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on WASM remainder divide by zero traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:integer-divide-by-zero`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700412a41006f0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:wasm-trap:integer-divide-by-zero")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on WASM unsigned remainder divide by zero traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:integer-divide-by-zero`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700412a4100700b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:wasm-trap:integer-divide-by-zero")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on WASM unreachable traps through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:unreachable`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a05010300000b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:wasm-trap:unreachable")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32 bitwise WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0f010d00413c410f714102724124730b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.shl WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:40`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041054103740b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:40")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.shr_u WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:5`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041284103760b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:5")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.shr_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:5`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041284103750b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:5")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32 sign-extension WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:-1:-1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var e8 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0801060041ff01c00b'); var e16 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041ffff03c10b'); var i8 = new WebAssembly.Instance(e8); var i16 = new WebAssembly.Instance(e16); e8.functionExportName0 + ':' + typeof i8.exports.run + ':' + i8.exports.run() + ':' + i16.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:-1:-1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.eqz WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a070105004100450b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.eq WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700412a412a460b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.ne WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700412a4107470b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.lt_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041024107480b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.gt_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700410741024a0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.le_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700410741074c0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.ge_s WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700410741024e0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.lt_u WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041024107490b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.gt_u WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700410741024b0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.le_u WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700410741074d0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32.ge_u WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `run:function:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700410741024f0b'); var i = new WebAssembly.Instance(m); m.functionExportName0 + ':' + typeof i.exports.run + ':' + i.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("run:function:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32 div_u and unsigned-order comparisons through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `2147483647:0:1:1:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m1 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700417e41026e0b'); var div = new WebAssembly.Instance(m1); var m2 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700417f4102490b'); var lt = new WebAssembly.Instance(m2); var m3 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700417f41024b0b'); var gt = new WebAssembly.Instance(m3); var m4 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a090107004102417f4d0b'); var le = new WebAssembly.Instance(m4); var m5 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a09010700417f41024f0b'); var ge = new WebAssembly.Instance(m5); div.exports.run() + ':' + lt.exports.run() + ':' + gt.exports.run() + ':' + le.exports.run() + ':' + ge.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2147483647:0:1:1:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32 clz ctz and popcnt WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `27:4:3`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m1 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a070105004110670b'); var i1 = new WebAssembly.Instance(m1); var m2 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a070105004110680b'); var i2 = new WebAssembly.Instance(m2); var m3 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a07010500412a690b'); var i3 = new WebAssembly.Instance(m3); i1.exports.run() + ':' + i2.exports.run() + ':' + i3.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("27:4:3")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should execute bounded i32 rotate WASM exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `8:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m1 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041014103770b'); var i1 = new WebAssembly.Instance(m1); var m2 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a0901070041084103780b'); var i2 = new WebAssembly.Instance(m2); i1.exports.run() + ':' + i2.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("8:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should wrap bounded i32 shift and rotate overflow through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `-2147483648:-2147483648`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m1 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a090107004101411f740b'); var i1 = new WebAssembly.Instance(m1); var m2 = new WebAssembly.Module('0061736d010000000105016000017f030201000707010372756e00000a090107004101411f770b'); var i2 = new WebAssembly.Instance(m2); i1.exports.run() + ':' + i2.exports.run()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("-2147483648:-2147483648")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose bounded table and global exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `table:tbl:1:answer:42:table:1:global:42`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300'); var i = new WebAssembly.Instance(m); m.firstExportKind + ':' + m.tableExportName + ':' + m.tableMinElements + ':' + m.globalExportName + ':' + m.globalValue + ':' + i.exports.tbl.kind + ':' + i.exports.tbl.length + ':' + i.exports.answer.kind + ':' + i.exports.answer.value")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("table:tbl:1:answer:42:table:1:global:42")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose bounded signed global exports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `answer:-1:global:-1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d010000000606017f00417f0b070a0106616e737765720300'); var i = new WebAssembly.Instance(m); m.globalExportName + ':' + m.globalValue + ':' + i.exports.answer.kind + ':' + i.exports.answer.value")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("answer:-1:global:-1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should fail closed on unsupported WASM imports through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:invalid:unsupported-wasm-imports:invalid:unsupported-wasm-imports`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var m = new WebAssembly.Module('0061736d01000000010401600000020b0103656e7603666f6f0000'); var i = new WebAssembly.Instance(m); var r = WebAssembly.instantiate('0061736d01000000010401600000020b0103656e7603666f6f0000'); m.hasImportSection + ':' + i.status + ':' + i.error + ':' + r.status + ':' + r.error")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:invalid:unsupported-wasm-imports:invalid:unsupported-wasm-imports")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should invoke a declared WebGPU host import from WASM through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:webgpu:requestAdapter:function:instantiated:0:7:1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var calls = 0; var imports = { webgpu: { requestAdapter: function() { calls = calls + 1; return 7; } } }; var m = new WebAssembly.Module('0061736d010000000105016000017f021901067765626770750e72657175657374416461707465720000030201000707010372756e00010a0601040010000b'); var i = new WebAssembly.Instance(m, imports); m.hasImportSection + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + m.firstImportKind + ':' + i.status + ':' + calls + ':' + i.exports.run() + ':' + calls")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:webgpu:requestAdapter:function:instantiated:0:7:1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should invoke a declared WebGPU dispatch host import from WASM through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:webgpu:dispatch:function:instantiated:0:9:1:9`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var calls = 0; var last = 0; var imports = { webgpu: { dispatch: function() { calls = calls + 1; last = 9; return last; } } }; var m = new WebAssembly.Module('0061736d010000000105016000017f021301067765626770750864697370617463680000030201000707010372756e00010a0601040010000b'); var i = new WebAssembly.Instance(m, imports); m.hasImportSection + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + m.firstImportKind + ':' + i.status + ':' + calls + ':' + i.exports.run() + ':' + calls + ':' + last")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:webgpu:dispatch:function:instantiated:0:9:1:9")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should pass WASM workgroup dimensions into a declared WebGPU dispatch import

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:webgpu:dispatch:instantiated:0:234:1:2x3x4`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var calls = 0; var dims = ''; var imports = { webgpu: { dispatch: function(x, y, z) { calls = calls + 1; dims = x + 'x' + y + 'x' + z; return x * 100 + y * 10 + z; } } }; var m = new WebAssembly.Module('0061736d01000000010c0260037f7f7f017f6000017f021301067765626770750864697370617463680000030201010707010372756e00010a0c010a0041024103410410000b'); var i = new WebAssembly.Instance(m, imports); m.hasImportSection + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + i.status + ':' + calls + ':' + i.exports.run() + ':' + calls + ':' + dims")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:webgpu:dispatch:instantiated:0:234:1:2x3x4")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should pass WASM workgroup dimensions into a void WebGPU dispatch import

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:webgpu:dispatch:instantiated:0:1:1:2x3x4`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var calls = 0; var dims = ''; var imports = { webgpu: { dispatch: function(x, y, z) { calls = calls + 1; dims = x + 'x' + y + 'x' + z; } } }; var m = new WebAssembly.Module('0061736d01000000010b0260037f7f7f006000017f021301067765626770750864697370617463680000030201010707010372756e00010a0e010c00410241034104100041010b'); var i = new WebAssembly.Instance(m, imports); m.hasImportSection + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + i.status + ':' + calls + ':' + i.exports.run() + ':' + calls + ':' + dims")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:webgpu:dispatch:instantiated:0:1:1:2x3x4")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should pass a WASM memory payload into a declared WebGPU writeBuffer import

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:webgpu:writeBuffer:instantiated:0:23:1:0:3:5,7,11`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var calls = 0; var payload = ''; var m; var imports = { webgpu: { writeBuffer: function(ptr, len) { calls = calls + 1; payload = ptr + ':' + len + ':' + m.runtimeMemoryByte0 + ',' + m.runtimeMemoryByte1 + ',' + m.runtimeMemoryByte2; return m.runtimeMemoryByte0 + m.runtimeMemoryByte1 + m.runtimeMemoryByte2; } } }; m = new WebAssembly.Module('0061736d01000000010b0260027f7f017f6000017f021601067765626770750b777269746542756666657200000302010105030100010707010372756e00010a1f011d00410041053a0000410141073a00004102410b3a00004100410310000b'); var i = new WebAssembly.Instance(m, imports); m.hasImportSection + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + i.status + ':' + calls + ':' + i.exports.run() + ':' + calls + ':' + payload")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:webgpu:writeBuffer:instantiated:0:23:1:0:3:5,7,11")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should mirror WASM halfword and word stores into a WebGPU writeBuffer import

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:webgpu:writeBuffer:instantiated:0:7:1:0:6:1,2,4,0,0,0`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var calls = 0; var payload = ''; var m; var imports = { webgpu: { writeBuffer: function(ptr, len) { calls = calls + 1; payload = ptr + ':' + len + ':' + m.runtimeMemoryByte0 + ',' + m.runtimeMemoryByte1 + ',' + m.runtimeMemoryByte2 + ',' + m.runtimeMemoryByte3 + ',' + m.runtimeMemoryByte4 + ',' + m.runtimeMemoryByte5; return m.runtimeMemoryByte0 + m.runtimeMemoryByte1 + m.runtimeMemoryByte2 + m.runtimeMemoryByte3 + m.runtimeMemoryByte4 + m.runtimeMemoryByte5; } } }; m = new WebAssembly.Module('0061736d01000000010b0260027f7f017f6000017f021601067765626770750b777269746542756666657200000302010105030100010707010372756e00010a1901170041004181043b0100410241043602004100410610000b'); var i = new WebAssembly.Instance(m, imports); m.hasImportSection + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + i.status + ':' + calls + ':' + i.exports.run() + ':' + calls + ':' + payload")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:webgpu:writeBuffer:instantiated:0:7:1:0:6:1,2,4,0,0,0")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should pass a WASM Simple2D rectangle payload into a WebGPU writeBuffer import

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:webgpu:writeBuffer:instantiated:0:645:1:0:8:rect:8,12,40,24:rgba:51,102,... (full value in folded executable source)`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var calls = 0; var payload = ''; var m; var imports = { webgpu: { writeBuffer: function(ptr, len) { calls = calls + 1; payload = ptr + ':' + len + ':rect:' + m.runtimeMemoryByte0 + ',' + m.runtimeMemoryByte1 + ',' + m.runtimeMemoryByte2 + ',' + m.runtimeMemoryByte3 + ':rgba:' + m.runtimeMemoryByte4 + ',' + m.runtimeMemoryByte5 + ',' + m.runtimeMemoryByte6 + ',' + m.runtimeMemoryByte7; return m.runtimeMemoryByte0 + m.runtimeMemoryByte1 + m.runtimeMemoryByte2 + m.runtimeMemoryByte3 + m.runtimeMemoryByte4 + m.runtimeMemoryByte5 + m.runtimeMemoryByte6 + m.runtimeMemoryByte7; } } }; m = new WebAssembly.Module('0061736d01000000010b0260027f7f017f6000017f021601067765626770750b777269746542756666657200000302010105030100010707010372756e00010a45014300410041083a00004101410c3a0000410241283a0000410341183a0000410441333a0000410541e6003a000041064199013a0000410741ff013a00004100410810000b'); var i = new WebAssembly.Instance(m, imports); m.hasImportSection + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + i.status + ':' + calls + ':' + i.exports.run() + ':' + calls + ':' + payload")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:webgpu:writeBuffer:instantiated:0:645:1:0:8:rect:8,12,40,24:rgba:51,102,153,255")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should expose WASM memory stores to a WebGPU writeBuffer import through exported Memory

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `true:webgpu:writeBuffer:instantiated:0:33:1:0:3:9,10,11:65536`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var calls = 0; var payload = ''; var i; var imports = { webgpu: { writeBuffer: function(ptr, len) { calls = calls + 1; var view = new Uint8Array(i.exports.memory.buffer); payload = ptr + ':' + len + ':' + view[ptr] + ',' + view[ptr + 1] + ',' + view[ptr + 2] + ':' + view.length; return view[ptr] + view[ptr + 1] + view[ptr + 2] + len; } } }; var m = new WebAssembly.Module('0061736d01000000010b0260027f7f017f6000017f021601067765626770750b77726974654275666665720000030201010503010001071002066d656d6f727902000372756e00010a1f011d00410041093a00004101410a3a00004102410b3a00004100410310000b'); i = new WebAssembly.Instance(m, imports); m.hasMemorySection + ':' + m.firstImportModuleName + ':' + m.firstImportFieldName + ':' + i.status + ':' + calls + ':' + i.exports.run() + ':' + calls + ':' + payload")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:webgpu:writeBuffer:instantiated:0:33:1:0:3:9,10,11:65536")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should construct bounded WebAssembly.Memory through BrowserSession

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `function:1:2:131072:-1`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mem = new WebAssembly.Memory({initial:1, maximum:2}); var old = mem.grow(1); typeof WebAssembly.Memory + ':' + old + ':' + mem.pages + ':' + mem.buffer.byteLength + ':' + mem.grow(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:1:2:131072:-1")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should share WebAssembly.Memory bytes with BrowserSession Uint8Array views

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `4:4:255:7:65536:65536`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mem = new WebAssembly.Memory({initial:1, maximum:1}); var view = new Uint8Array(mem.buffer); view[0] = 260; view[1] = -1; view[2] = 7; view[0] + ':' + mem.buffer[0] + ':' + view[1] + ':' + mem.buffer[2] + ':' + view.length + ':' + mem.buffer.byteLength")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4:4:255:7:65536:65536")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should window WebAssembly.Memory bytes with BrowserSession Uint8Array subarray views

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `1:2:42:77`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mem = new WebAssembly.Memory({initial:1, maximum:1}); var view = new Uint8Array(mem.buffer); view[1] = 42; var sub = view.subarray(1, 3); sub[1] = 77; sub.byteOffset + ':' + sub.length + ':' + sub[0] + ':' + view[2]")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:2:42:77")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should set WebAssembly.Memory bytes from BrowserSession Uint8Array views

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `7:8`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mem = new WebAssembly.Memory({initial:1, maximum:1}); var view = new Uint8Array(mem.buffer); var src = new Uint8Array(2); src[0] = 7; src[1] = 8; view.set(src, 3); mem.buffer[3] + ':' + mem.buffer[4]")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("7:8")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should set WebAssembly.Memory bytes from computed Uint8Array set calls

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `9`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mem = new WebAssembly.Memory({initial:1, maximum:1}); var view = new Uint8Array(mem.buffer); var src = new Uint8Array(1); src[0] = 9; view[\"set\"](src, 5); mem.buffer[5]")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("9")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should set WebAssembly.Memory bytes from Uint8Array prototype set call dispatch

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `11:12`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mem = new WebAssembly.Memory({initial:1, maximum:1}); var view = new Uint8Array(mem.buffer); var src = new Uint8Array(2); src[0] = 11; src[1] = 12; Uint8Array.prototype.set.call(view, src, 7); mem.buffer[7] + ':' + mem.buffer[8]")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("11:12")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should set WebAssembly.Memory bytes from Uint8Array prototype set apply dispatch

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `21:22`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mem = new WebAssembly.Memory({initial:1, maximum:1}); var view = new Uint8Array(mem.buffer); var src = new Uint8Array(2); src[0] = 21; src[1] = 22; Uint8Array.prototype.set.apply(view, [src, 9]); mem.buffer[9] + ':' + mem.buffer[10]")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("21:22")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should read and write WebAssembly.Memory bytes from DataView glue methods

- var session = BrowserSession new
- session open html
- Ok
   - Expected: _display_js(value) equals `4:3:2:1:16909060:772:-2`
- Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("var mem = new WebAssembly.Memory({initial:1, maximum:1}); var dv = new DataView(mem.buffer); dv.setUint32(4, 16909060, true); dv.setInt32(8, -2, true); mem.buffer[4] + ':' + mem.buffer[5] + ':' + mem.buffer[6] + ':' + mem.buffer[7] + ':' + dv.getUint32(4, true) + ':' + dv.getUint16(4, true) + ':' + dv.getInt32(8, true)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4:3:2:1:16909060:772:-2")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 127 |
| Active scenarios | 127 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [.spipe/browser-wasm-webgpu-infra/state.md](.spipe/browser-wasm-webgpu-infra/state.md)
- **Plan:** [doc/03_plan/platform/webgpu_js_wasm_simple.md](doc/03_plan/platform/webgpu_js_wasm_simple.md)
- **Design:** [doc/05_design/browser_wasm_webgpu_infra.md](doc/05_design/browser_wasm_webgpu_infra.md)
- **Research:** [doc/01_research/local/browser_wasm_webgpu_infra.md](doc/01_research/local/browser_wasm_webgpu_infra.md)


</details>
