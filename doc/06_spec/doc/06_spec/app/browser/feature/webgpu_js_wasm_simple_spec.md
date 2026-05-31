# Webgpu Js Wasm Simple Specification

## Scenarios

### WebGPU JS WASM Simple system examples

### REQ-WGPU-001: secure context exposure

#### should expose navigator gpu metadata to secure JavaScript pages

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:object:true`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `false:undefined`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `available:function`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

#### should configure and present a secure WebGPU canvas

1. var ctx = canvas get context webgpu
   - Expected: ctx.is_available() is true
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: ctx.present() is true
   - Expected: ctx.gpu.present_count equals `1`


<details>
<summary>Executable SPipe</summary>

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

1. var ctx = canvas get context webgpu
   - Expected: ctx.is_available() is false
   - Expected: ctx.request_device() is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, false)
expect(ctx.is_available()).to_equal(false)
expect(ctx.request_device()).to_equal(false)
```

</details>

#### should create render and compute pipeline handles through the canvas wrapper

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: rp.valid is true
   - Expected: cp.valid is true


<details>
<summary>Executable SPipe</summary>

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

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: cp.valid is true
   - Expected: gpu_ctx.queue_write_buffer(buffer.id, 0, 32) is true

2. var encoder = gpu ctx create command encoder
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
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = canvas_get_context_webgpu(320, 240, true)
expect(ctx.request_device()).to_equal(true)
expect(ctx.configure()).to_equal(true)

var gpu_ctx: WebGPUContext = ctx.gpu
var resources = gpu_ctx.resources
val buffer = resources.create_buffer("storage", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
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

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: ctx.configure() is true
   - Expected: gpu_ctx.queue_write_buffer(999, 0, 32) is false


<details>
<summary>Executable SPipe</summary>

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

1. var ctx = canvas get context webgpu
   - Expected: ctx.request_device() is true
   - Expected: lost.lost is true

2. var encoder = ctx gpu create command encoder
   - Expected: ctx.gpu.queue_submit([command_buffer]) is false


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `42:bgra8unorm`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

### REQ-WGPU-006: WASM backend smoke

#### should compile an empty Simple MIR module to WAT for wasm32

1. var adapter = WasmCodegenAdapter

2. Ok

3. Err
   - Expected: "compilation failed: {err.message}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var adapter = WasmCodegenAdapter
   - Expected: adapter.supports_target(CodegenTarget.Wasm32) is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = WasmCodegenAdapter(options: _wasm32_options())
expect(adapter.supports_target(CodegenTarget.Wasm32)).to_equal(true)
```

</details>

#### should reject x86_64 target support in the wasm adapter

1. var adapter = WasmCodegenAdapter
   - Expected: adapter.supports_target(CodegenTarget.X86_64) is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = WasmCodegenAdapter(options: _wasm32_options())
expect(adapter.supports_target(CodegenTarget.X86_64)).to_equal(false)
```

</details>

### REQ-WGPU-007: browser WASM to WebGPU bridge

#### should expose the browser WebAssembly host object beside WebGPU

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `object:function:function:available:bgra8unorm`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")
val result = session.eval_script("typeof WebAssembly + ':' + typeof WebAssembly.instantiate + ':' + typeof WebAssembly.validate + ':' + WebAssembly.instantiateStatus + ':' + navigator.gpu.preferredCanvasFormat")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("object:function:function:available:bgra8unorm")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

#### should validate and instantiate WASM inputs through the hardened JS host

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:false:false:instantiated:invalid`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:false:instantiated`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `function:function:true:8`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

#### should expose bounded WASM section metadata through BrowserSession

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `1:true:invalid-wasm-section`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `1:true:instantiated:object`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `doc/06_spec/app/browser/feature/webgpu_js_wasm_simple_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebGPU JS WASM Simple system examples
- REQ-WGPU-001: secure context exposure
- REQ-WGPU-002: canvas WebGPU context
- REQ-WGPU-003 and REQ-WGPU-004: Simple script resource and executor path
- REQ-WGPU-005: JavaScript integration remains available
- REQ-WGPU-006: WASM backend smoke
- REQ-WGPU-007: browser WASM to WebGPU bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

