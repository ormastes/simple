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
   - Expected: _display_js(value) equals `object:function:function:function:available:bgra8unorm`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

#### should validate TextEncoder-produced WASM bytes through BrowserSession

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `function:function:wasm:true`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `8:8:true`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

#### should expose thenable WebAssembly.instantiate result shape through BrowserSession

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `function:function:instantiated:1:object`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `instantiated:1:object`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `queued`

4. Err
   - Expected: "unexpected queue error: {err}" equals ``

5. Ok
   - Expected: _display_js(value) equals ``

6. Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``

7. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`

8. Ok

9. Ok
   - Expected: _display_js(value) equals `fetch>arrayBuffer:11>instantiate:instantiated:11:1:object`

10. Err
   - Expected: "unexpected js error: {err}" equals ``

11. Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `queued`

4. Err
   - Expected: "unexpected queue error: {err}" equals ``

5. Ok
   - Expected: _display_js(value) equals ``

6. Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``

7. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`

8. Ok

9. Ok
   - Expected: _display_js(value) equals `instantiated:11:true:bgra8unorm:function`

10. Err
   - Expected: "unexpected js error: {err}" equals ``

11. Ok
   - Expected: _display_js(value) equals ``

12. Err
   - Expected: "unexpected adapter queue error: {err}" equals ``

13. Ok
   - Expected: _display_js(value) equals `Simple WebGPU Software Adapter:true`

14. Err
   - Expected: "unexpected adapter js error: {err}" equals ``

15. Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

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
                match session.eval_script("navigator.gpu.requestAdapter().then(function(adapter) { adapterName = adapter.name + ':' + adapter.isFallbackAdapter; }); adapterName"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("")
                    Err(err):
                        expect("unexpected adapter queue error: {err}").to_equal("")
                match session.eval_script("adapterName"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("Simple WebGPU Software Adapter:true")
                    Err(err):
                        expect("unexpected adapter js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### should expose thenable WebAssembly.compile result shape through BrowserSession

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `function:function:compiled:1:true`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `invalid:invalid-wasm-header`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:1:1:memory:memory:65536`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:run:1:function:undefined`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `2:init:render:function:function:undefined:undefined`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `40:run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `-1:run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `42:44:44`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `2:3:3`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `-1:1:2`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `wasm-trap:out-of-bounds-memory-access:wasm-trap:out-of-bounds-memory-access`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:run:function:-86`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:run:function:4660`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:run:function:-128`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `42:7`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `42:7`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `-2147483648:2147483647:0`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:2`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:2`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:integer-divide-by-zero`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:integer-overflow`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:integer-divide-by-zero`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:integer-divide-by-zero`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:wasm-trap:unreachable`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:40`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:5`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:5`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:-1:-1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `run:function:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `2147483647:0:1:1:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `27:4:3`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `8:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `-2147483648:-2147483648`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `table:tbl:1:answer:42:table:1:global:42`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `answer:-1:global:-1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:invalid:unsupported-wasm-imports:invalid:unsupported-wasm-imports`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:webgpu:requestAdapter:function:instantiated:0:7:1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

#### should construct bounded WebAssembly.Memory through BrowserSession

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `function:1:2:131072:-1`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `4:4:255:7:65536:65536`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `1:2:42:77`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `7:8`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `9`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `11:12`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `21:22`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `4:3:2:1:16909060:772:-2`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` |
| Updated | 2026-06-01 |
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
| Total scenarios | 105 |
| Active scenarios | 105 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

