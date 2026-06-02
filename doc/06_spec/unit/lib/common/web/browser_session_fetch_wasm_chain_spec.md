# Browser Session Fetch Wasm Chain Specification

## Scenarios

### BrowserSession fetch WASM promise chain

#### chains fetched arrayBuffer bytes into WebAssembly.instantiate

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `queued`

3. Err
   - Expected: "unexpected queue error: {err}" equals ``

4. Ok
   - Expected: _display_js(value) equals ``

5. Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``

6. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`

7. Ok

8. Ok
   - Expected: _display_js(value) equals `fetch>arrayBuffer:11>instantiate:instantiated:11:1:object`

9. Err
   - Expected: "unexpected js error: {err}" equals ``

10. Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
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
                match session.eval_script("out"):
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

#### chains fetched arrayBuffer bytes into WebAssembly.compile

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `queued`

3. Err
   - Expected: "unexpected queue error: {err}" equals ``

4. Ok
   - Expected: _display_js(value) equals ``

5. Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``

6. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`

7. Ok

8. Ok
   - Expected: _display_js(value) equals `fetch>arrayBuffer:11>compile:11:1:true`

9. Err
   - Expected: "unexpected js error: {err}" equals ``

10. Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { out = stages + 'compile:' + module.byteLength + ':' + module.sectionCount + ':' + module.hasTypeSection; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:11>compile:11:1:true")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes invalid WebAssembly.compile results through catch in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `invalid:invalid-wasm-header:8:0`

3. Err
   - Expected: "unexpected wasm compile catch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var out = ''; WebAssembly.compile('0061736d00000000').catch(function(err) { out = err.status + ':' + err.error; }); var valid = WebAssembly.compile('0061736d01000000'); valid.then(function(module) { out = out + ':' + module.byteLength + ':' + module.sectionCount; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("invalid:invalid-wasm-header:8:0")
    Err(err):
        expect("unexpected wasm compile catch js error: {err}").to_equal("")
```

</details>

#### routes invalid WebAssembly.instantiate results through catch in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `invalid:invalid-wasm-header:invalid:unsupported-wasm-imports:instantiated:8`

3. Err
   - Expected: "unexpected wasm instantiate catch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var out = ''; WebAssembly.instantiate('0061736d00000000').catch(function(err) { out = err.status + ':' + err.error; }); var imports = {}; WebAssembly.instantiate('0061736d01000000010401600000020b0103656e7603666f6f0000', imports).catch(function(err) { out = out + ':' + err.status + ':' + err.error; }); WebAssembly.instantiate('0061736d01000000').then(function(result) { out = out + ':' + result.status + ':' + result.module.byteLength; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("invalid:invalid-wasm-header:invalid:unsupported-wasm-imports:instantiated:8")
    Err(err):
        expect("unexpected wasm instantiate catch js error: {err}").to_equal("")
```

</details>

#### chains compiled WebAssembly modules into instantiate

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `queued`

3. Err
   - Expected: "unexpected queue error: {err}" equals ``

4. Ok
   - Expected: _display_js(value) equals ``

5. Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``

6. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`

7. Ok

8. Ok
   - Expected: _display_js(value) equals `fetch>arrayBuffer:11>compile:11>instantiate:instantiated:11:object`

9. Err
   - Expected: "unexpected js error: {err}" equals ``

10. Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { stages = stages + 'compile:' + module.byteLength + '>'; return WebAssembly.instantiate(module); }).then(function(result) { out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + typeof result.instance.exports; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:11>compile:11>instantiate:instantiated:11:object")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates streaming fetch responses with imports

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `queued`

3. Err
   - Expected: "unexpected queue error: {err}" equals ``

4. Ok
   - Expected: _display_js(value) equals ``

5. Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``

6. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`

7. Ok

8. Ok
   - Expected: _display_js(value) equals `stream:instantiated:1:42`

9. Err
   - Expected: "unexpected js error: {err}" equals ``

10. Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val queued = session.eval_script("var out = ''; var imports = { env: { foo: function(x) { return x + 1; } } }; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm'), imports).then(function(result) { out = 'stream:' + result.status + ':' + result.module.importCount + ':' + result.instance.exports.run(41); }); 'queued'")
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
            body: "0061736d0100000001060160017f017f020b0103656e7603666f6f0000030201000707010372756e00010a08010600200010000b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("stream:instantiated:1:42")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### compiles streaming fetch responses into modules

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `queued`

3. Err
   - Expected: "unexpected queue error: {err}" equals ``

4. Ok
   - Expected: _display_js(value) equals ``

5. Err
   - Expected: "unexpected pre-commit js error: {err}" equals ``

6. Some
   - Expected: request.kind equals `fetch`
   - Expected: request.url equals `https://example.com/mod.wasm`

7. Ok

8. Ok
   - Expected: _display_js(value) equals `compileStreaming:11:1:true`

9. Err
   - Expected: "unexpected js error: {err}" equals ``

10. Err
   - Expected: "unexpected commit error: {err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { out = 'compileStreaming:' + module.byteLength + ':' + module.sectionCount + ':' + module.hasTypeSection; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("compileStreaming:11:1:true")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### exposes Module imports and exports descriptors in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `2:tbl:table:answer:global:1:env:foo:function`

3. Err
   - Expected: "unexpected descriptor js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var tableGlobal = new WebAssembly.Module('0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300'); var exports = WebAssembly.Module.exports(tableGlobal); var imported = new WebAssembly.Module('0061736d01000000010401600000020b0103656e7603666f6f0000'); var imports = WebAssembly.Module.imports(imported); exports.length + ':' + exports[0].name + ':' + exports[0].kind + ':' + exports[1].name + ':' + exports[1].kind + ':' + imports.length + ':' + imports[0].module + ':' + imports[0].name + ':' + imports[0].kind")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2:tbl:table:answer:global:1:env:foo:function")
    Err(err):
        expect("unexpected descriptor js error: {err}").to_equal("")
```

</details>

#### constructs Table and Global objects in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `2:1:slot0:slot1:i32:true:7`

3. Err
   - Expected: "unexpected table/global js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var table = new WebAssembly.Table({ element: 'externref', initial: 1, maximum: 2 }); table.set(0, 'slot0'); var old = table.grow(1, 'slot1'); var global = new WebAssembly.Global({ value: 'i32', mutable: true }, 7); table.length + ':' + old + ':' + table.get(0) + ':' + table.get(1) + ':' + global.valueType + ':' + global.mutable + ':' + global.value")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2:1:slot0:slot1:i32:true:7")
    Err(err):
        expect("unexpected table/global js error: {err}").to_equal("")
```

</details>

#### fills and searches Uint8Array values in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `0:4:4:0:1:2:3:true:false`

3. Err
   - Expected: "unexpected uint8 js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(5); b.fill(260, 1, 4); b[0] + ':' + b[1] + ':' + b[3] + ':' + b[4] + ':' + b.indexOf(4) + ':' + b.indexOf(4, 2) + ':' + b.indexOf(4, -2) + ':' + b.includes(4) + ':' + b.includes(5)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("0:4:4:0:1:2:3:true:false")
    Err(err):
        expect("unexpected uint8 js error: {err}").to_equal("")
```

</details>

#### joins and reverses Uint8Array values in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1-4-255-7:7,255,4,1:7/255/4/1`

3. Err
   - Expected: "unexpected uint8 join reverse js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; var before = b.join('-'); var returned = b.reverse(); before + ':' + b.join(',') + ':' + returned.join('/')")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1-4-255-7:7,255,4,1:7/255/4/1")
    Err(err):
        expect("unexpected uint8 join reverse js error: {err}").to_equal("")
```

</details>

#### searches Uint8Array values backward in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `3:2:3:0:-1`

3. Err
   - Expected: "unexpected uint8 lastIndexOf js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(5); b[0] = 4; b[1] = 7; b[2] = 260; b[3] = 4; b[4] = 0; b.lastIndexOf(4) + ':' + b.lastIndexOf(4, 2) + ':' + b.lastIndexOf(4, -2) + ':' + b.lastIndexOf(4, -4) + ':' + b.lastIndexOf(5)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("3:2:3:0:-1")
    Err(err):
        expect("unexpected uint8 lastIndexOf js error: {err}").to_equal("")
```

</details>

#### stringifies Uint8Array values in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,4,255,7:1|4|255|7`

3. Err
   - Expected: "unexpected uint8 toString js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; b.toString() + ':' + b.join('|')")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,4,255,7:1|4|255|7")
    Err(err):
        expect("unexpected uint8 toString js error: {err}").to_equal("")
```

</details>

#### reads Uint8Array values by relative index in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1:4:7:255:undefined`

3. Err
   - Expected: "unexpected uint8 at js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; b.at(0) + ':' + b.at(1) + ':' + b.at(-1) + ':' + b.at(-2) + ':' + b.at(9)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:4:7:255:undefined")
    Err(err):
        expect("unexpected uint8 at js error: {err}").to_equal("")
```

</details>

#### copies Uint8Array values within the same storage in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,7,9,7,9:7`

3. Err
   - Expected: "unexpected uint8 copyWithin js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(5); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; b[4] = 9; var returned = b.copyWithin(1, -2); b.toString() + ':' + returned.at(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,7,9,7,9:7")
    Err(err):
        expect("unexpected uint8 copyWithin js error: {err}").to_equal("")
```

</details>

#### checks Uint8Array values with callback predicates in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `true:true:false`

3. Err
   - Expected: "unexpected uint8 callback js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; b.some(function(v, i, arr) { return v == 255 && i == 2 && arr.at(3) == 7; }) + ':' + b.every(function(v) { return v >= 0; }) + ':' + b.every(function(v) { return false; })")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:true:false")
    Err(err):
        expect("unexpected uint8 callback js error: {err}").to_equal("")
```

</details>

#### iterates Uint8Array values with side-effect callbacks in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `266:0=4;1=255;2=7;:undefined`

3. Err
   - Expected: "unexpected uint8 forEach js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; var total = 0; var seen = ''; var returned = b.forEach(function(v, i, arr) { total = total + v; seen = seen + i + '=' + arr.at(i) + ';'; }); total + ':' + seen + ':' + returned")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("266:0=4;1=255;2=7;:undefined")
    Err(err):
        expect("unexpected uint8 forEach js error: {err}").to_equal("")
```

</details>

#### finds Uint8Array values with callback predicates in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4:1:undefined:-1`

3. Err
   - Expected: "unexpected uint8 find js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; b.find(function(v, i, arr) { return i; }) + ':' + b.findIndex(function(v, i, arr) { return i; }) + ':' + b.find(function(v) { return false; }) + ':' + b.findIndex(function(v) { return false; })")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4:1:undefined:-1")
    Err(err):
        expect("unexpected uint8 find js error: {err}").to_equal("")
```

</details>

#### reduces Uint8Array values with accumulator callbacks in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `535`

3. Err
   - Expected: "unexpected uint8 reduce js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; b.reduce(function(acc, v, i, arr) { return acc + v + i + arr.at(i); }, 0)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("535")
    Err(err):
        expect("unexpected uint8 reduce js error: {err}").to_equal("")
```

</details>

#### reduces Uint8Array values from the right in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `16511008`

3. Err
   - Expected: "unexpected uint8 reduceRight js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; b.reduceRight(function(acc, v, i, arr) { return acc * 1000 + v + i + arr.at(i); }, 0)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("16511008")
    Err(err):
        expect("unexpected uint8 reduceRight js error: {err}").to_equal("")
```

</details>

#### constructs Uint8Array values from indexed sources in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4,255:4,255:4,0,9:3:0`

3. Err
   - Expected: "unexpected uint8 from js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var src = new Uint8Array(2); src[0] = 260; src[1] = -1; var copied = Uint8Array.from(src); var mapped = Uint8Array.from([260, -1, 7], function(v, i) { return v + i; }); copied.toString() + ':' + src.toString() + ':' + mapped.toString() + ':' + mapped.length + ':' + mapped.at(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4,255:4,255:4,0,9:3:0")
    Err(err):
        expect("unexpected uint8 from js error: {err}").to_equal("")
```

</details>

#### constructs Uint8Array values from varargs in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4,255,7:3:4:255:0:`

3. Err
   - Expected: "unexpected uint8 of js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var made = Uint8Array.of(260, -1, 7); var empty = Uint8Array.of(); made.toString() + ':' + made.length + ':' + made.at(0) + ':' + made.at(1) + ':' + empty.length + ':' + empty.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4,255,7:3:4:255:0:")
    Err(err):
        expect("unexpected uint8 of js error: {err}").to_equal("")
```

</details>

#### maps Uint8Array values into a new coerced array in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `8,255,16:4,255,7:3:255`

3. Err
   - Expected: "unexpected uint8 map js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; var mapped = b.map(function(v, i, arr) { return v + i + arr.at(i); }); mapped.toString() + ':' + b.toString() + ':' + mapped.length + ':' + mapped.at(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("8,255,16:4,255,7:3:255")
    Err(err):
        expect("unexpected uint8 map js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype map with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `8,255,16:4,255,7:3:255`

3. Err
   - Expected: "unexpected uint8 prototype map dispatch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; var mapped = Uint8Array.prototype.map.call(b, function(v, i, arr) { return v + i + arr.at(i); }); mapped.toString() + ':' + b.toString() + ':' + mapped.length + ':' + mapped.at(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("8,255,16:4,255,7:3:255")
    Err(err):
        expect("unexpected uint8 prototype map dispatch js error: {err}").to_equal("")
```

</details>

#### filters Uint8Array values into a new coerced array in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `255,7,8:4,255,7,8:3:7`

3. Err
   - Expected: "unexpected uint8 filter js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 260; b[1] = -1; b[2] = 7; b[3] = 8; var filtered = b.filter(function(v, i) { return i; }); filtered.toString() + ':' + b.toString() + ':' + filtered.length + ':' + filtered.at(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("255,7,8:4,255,7,8:3:7")
    Err(err):
        expect("unexpected uint8 filter js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype filter with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `255,7,8:4,255,7,8:3:7`

3. Err
   - Expected: "unexpected uint8 prototype filter dispatch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 260; b[1] = -1; b[2] = 7; b[3] = 8; var filtered = Uint8Array.prototype.filter.call(b, function(v, i, arr) { return i && arr.at(0) == 4; }); filtered.toString() + ':' + b.toString() + ':' + filtered.length + ':' + filtered.at(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("255,7,8:4,255,7,8:3:7")
    Err(err):
        expect("unexpected uint8 prototype filter dispatch js error: {err}").to_equal("")
```

</details>

#### slices Uint8Array ranges into returned typed arrays in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4,255,7:3:4:255,7:2:1,4,255,7,9`

3. Err
   - Expected: "unexpected uint8 slice js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(5); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; b[4] = 9; var sub = b.subarray(1, -1); var sl = b.slice(-3, -1); sub.toString() + ':' + sub.length + ':' + sub.at(0) + ':' + sl.toString() + ':' + sl.length + ':' + b.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4,255,7:3:4:255,7:2:1,4,255,7,9")
    Err(err):
        expect("unexpected uint8 slice js error: {err}").to_equal("")
```

</details>

#### sets Uint8Array ranges from another typed array in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,4,255,7,9:undefined:5:4,255,7`

3. Err
   - Expected: "unexpected uint8 set js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var dst = new Uint8Array(5); dst[0] = 1; dst[4] = 9; var src = new Uint8Array(3); src[0] = 260; src[1] = -1; src[2] = 7; var returned = dst.set(src, 1); dst.toString() + ':' + returned + ':' + dst.length + ':' + src.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,4,255,7,9:undefined:5:4,255,7")
    Err(err):
        expect("unexpected uint8 set js error: {err}").to_equal("")
```

</details>

#### sorts Uint8Array values numerically in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,4,7,255:1,4,7,255:1:255`

3. Err
   - Expected: "unexpected uint8 sort js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 260; b[1] = -1; b[2] = 7; b[3] = 1; var returned = b.sort(); returned.toString() + ':' + b.toString() + ':' + returned.at(0) + ':' + returned.at(3)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,4,7,255:1,4,7,255:1:255")
    Err(err):
        expect("unexpected uint8 sort js error: {err}").to_equal("")
```

</details>

#### sorts Uint8Array values with comparator callbacks in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `255,7,4,1:255,7,4,1:255:1`

3. Err
   - Expected: "unexpected uint8 comparator sort js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; var returned = b.sort(function(x, y) { return y - x; }); returned.toString() + ':' + b.toString() + ':' + returned.at(0) + ':' + returned.at(3)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("255,7,4,1:255,7,4,1:255:1")
    Err(err):
        expect("unexpected uint8 comparator sort js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype sort with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,4,7,255:1,4,7,255:1:255`

3. Err
   - Expected: "unexpected uint8 prototype sort dispatch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 260; b[1] = -1; b[2] = 7; b[3] = 1; var returned = Uint8Array.prototype.sort.call(b); returned.toString() + ':' + b.toString() + ':' + returned.at(0) + ':' + returned.at(3)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,4,7,255:1,4,7,255:1:255")
    Err(err):
        expect("unexpected uint8 prototype sort dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype sort with apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,4,7,255:1,4,7,255:1:255`

3. Err
   - Expected: "unexpected uint8 prototype sort apply dispatch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = -1; b[1] = 1; b[2] = 260; b[3] = 7; var returned = Uint8Array.prototype.sort.apply(b, []); returned.toString() + ':' + b.toString() + ':' + returned.at(0) + ':' + returned.at(3)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,4,7,255:1,4,7,255:1:255")
    Err(err):
        expect("unexpected uint8 prototype sort apply dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype comparator sort with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `255,7,4,1:255,7,4,1:255:1`

3. Err
   - Expected: "unexpected uint8 prototype comparator sort dispatch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; var returned = Uint8Array.prototype.sort.call(b, function(x, y) { return y - x; }); returned.toString() + ':' + b.toString() + ':' + returned.at(0) + ':' + returned.at(3)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("255,7,4,1:255,7,4,1:255:1")
    Err(err):
        expect("unexpected uint8 prototype comparator sort dispatch js error: {err}").to_equal("")
```

</details>

#### iterates Uint8Array keys and values in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `0:1:true:4:255:true`

3. Err
   - Expected: "unexpected uint8 iterator js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(2); b[0] = 260; b[1] = -1; var keys = b.keys(); var values = b.values(); var k0 = keys.next(); var k1 = keys.next(); var k2 = keys.next(); var v0 = values.next(); var v1 = values.next(); var v2 = values.next(); k0.value + ':' + k1.value + ':' + k2.done + ':' + v0.value + ':' + v1.value + ':' + v2.done")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("0:1:true:4:255:true")
    Err(err):
        expect("unexpected uint8 iterator js error: {err}").to_equal("")
```

</details>

#### iterates Uint8Array entries in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `0=4:1=255:true`

3. Err
   - Expected: "unexpected uint8 entries iterator js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(2); b[0] = 260; b[1] = -1; var entries = b.entries(); var e0 = entries.next(); var e1 = entries.next(); var e2 = entries.next(); e0.value[0] + '=' + e0.value[1] + ':' + e1.value[0] + '=' + e1.value[1] + ':' + e2.done")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("0=4:1=255:true")
    Err(err):
        expect("unexpected uint8 entries iterator js error: {err}").to_equal("")
```

</details>

#### iterates Uint8Array values through Symbol iterator in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `function:function:4:255`

3. Err
   - Expected: "unexpected uint8 symbol iterator js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(2); b[0] = 260; b[1] = -1; var iterator = b[Symbol.iterator](); var iter2 = iterator[Symbol.iterator](); var i0 = iter2.next(); var i1 = iterator.next(); typeof b[Symbol.iterator] + ':' + typeof iterator[Symbol.iterator] + ':' + i0.value + ':' + i1.value")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:function:4:255")
    Err(err):
        expect("unexpected uint8 symbol iterator js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype Symbol iterator with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4:255:true`

3. Err
   - Expected: "unexpected uint8 prototype symbol iterator dispatch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var b = new Uint8Array(2); b[0] = 260; b[1] = -1; var iterator = Uint8Array.prototype[Symbol.iterator].call(b); var first = iterator.next(); var second = iterator.next(); var third = iterator.next(); first.value + ':' + second.value + ':' + third.done")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4:255:true")
    Err(err):
        expect("unexpected uint8 prototype symbol iterator dispatch js error: {err}").to_equal("")
```

</details>

#### reports Uint8Array view buffer metadata in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1:1:1:3:3:8:4,255,0:0,4,255,0,0,0,0,0`

3. Err
   - Expected: "unexpected uint8 metadata js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var buffer = new ArrayBuffer(8); var full = new Uint8Array(buffer); full[1] = 260; full[2] = -1; var view = new Uint8Array(buffer, 1, 3); Uint8Array.BYTES_PER_ELEMENT + ':' + view.BYTES_PER_ELEMENT + ':' + view.byteOffset + ':' + view.byteLength + ':' + view.length + ':' + view.buffer.byteLength + ':' + view.toString() + ':' + full.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:1:1:3:3:8:4,255,0:0,4,255,0,0,0,0,0")
    Err(err):
        expect("unexpected uint8 metadata js error: {err}").to_equal("")
```

</details>

#### reports Uint8Array prototype metadata in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `true:object:1:function:function:function`

3. Err
   - Expected: "unexpected uint8 prototype metadata js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("(Uint8Array.prototype === Uint8Array.prototype) + ':' + typeof Uint8Array.prototype + ':' + Uint8Array.prototype.BYTES_PER_ELEMENT + ':' + typeof Uint8Array.prototype.subarray + ':' + typeof Uint8Array.prototype.values + ':' + typeof Uint8Array.prototype[Symbol.iterator]")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:object:1:function:function:function")
    Err(err):
        expect("unexpected uint8 prototype metadata js error: {err}").to_equal("")
```

</details>

#### evaluates strict equality for browser script values

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `true:true:true:true:true`

3. Err
   - Expected: "unexpected strict equality js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("(1 === 1) + ':' + ('a' === 'a') + ':' + (1 !== 2) + ':' + (window === window) + ':' + (document === document)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:true:true:true:true")
    Err(err):
        expect("unexpected strict equality js error: {err}").to_equal("")
```

</details>

#### detects ArrayBuffer view objects in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `true:true:false:false:false`

3. Err
   - Expected: "unexpected arraybuffer isView js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var buffer = new ArrayBuffer(8); var bytes = new Uint8Array(buffer); var data = new DataView(buffer); ArrayBuffer.isView(bytes) + ':' + ArrayBuffer.isView(data) + ':' + ArrayBuffer.isView(buffer) + ':' + ArrayBuffer.isView({}) + ':' + ArrayBuffer.isView(null)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:true:false:false:false")
    Err(err):
        expect("unexpected arraybuffer isView js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype helpers with call and apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4,255,7:255,7,9:1`

3. Err
   - Expected: "unexpected uint8 prototype dispatch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var bytes = new Uint8Array(5); bytes[0] = 1; bytes[1] = 260; bytes[2] = -1; bytes[3] = 7; bytes[4] = 9; var sub = Uint8Array.prototype.subarray.call(bytes, 1, 4); var sl = Uint8Array.prototype.slice.apply(bytes, [2, 5]); var it = Uint8Array.prototype.values.call(bytes); var first = it.next(); sub.toString() + ':' + sl.toString() + ':' + first.value")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4,255,7:255,7,9:1")
    Err(err):
        expect("unexpected uint8 prototype dispatch js error: {err}").to_equal("")
```

</details>

#### reports ArrayBuffer and typed-array constructor metadata in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `Uint8Array:3:ArrayBuffer:1:DataView:1:true:true:true:true:true:function`

3. Err
   - Expected: "unexpected constructor metadata js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("Uint8Array.name + ':' + Uint8Array.length + ':' + ArrayBuffer.name + ':' + ArrayBuffer.length + ':' + DataView.name + ':' + DataView.length + ':' + (Uint8Array.prototype.constructor === Uint8Array) + ':' + (ArrayBuffer.prototype === ArrayBuffer.prototype) + ':' + (ArrayBuffer.prototype.constructor === ArrayBuffer) + ':' + (DataView.prototype === DataView.prototype) + ':' + (DataView.prototype.constructor === DataView) + ':' + typeof DataView.prototype.getUint8")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("Uint8Array:3:ArrayBuffer:1:DataView:1:true:true:true:true:true:function")
    Err(err):
        expect("unexpected constructor metadata js error: {err}").to_equal("")
```

</details>

#### reads and writes ArrayBuffer bytes through DataView in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `16909060:-2:4,3,2,1,254,255,255,255:0:8`

3. Err
   - Expected: "unexpected dataview js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var buffer = new ArrayBuffer(8); var view = new DataView(buffer); view.setUint32(0, 16909060, true); view.setInt32(4, -2, true); var bytes = new Uint8Array(buffer); view.getUint32(0, true) + ':' + view.getInt32(4, true) + ':' + bytes.toString() + ':' + view.byteOffset + ':' + view.byteLength")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("16909060:-2:4,3,2,1,254,255,255,255:0:8")
    Err(err):
        expect("unexpected dataview js error: {err}").to_equal("")
```

</details>

#### dispatches DataView prototype helpers with call and apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `258:-1:16909060:255,2,1,2,3,4`

3. Err
   - Expected: "unexpected dataview prototype dispatch js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var buffer = new ArrayBuffer(6); var view = new DataView(buffer); DataView.prototype.setUint16.call(view, 1, 258, true); DataView.prototype.setInt8.apply(view, [0, -1]); DataView.prototype.setUint32.call(view, 2, 16909060, false); var bytes = new Uint8Array(buffer); DataView.prototype.getUint16.apply(view, [1, true]) + ':' + DataView.prototype.getInt8.call(view, 0) + ':' + DataView.prototype.getUint32.apply(view, [2, false]) + ':' + bytes.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("258:-1:16909060:255,2,1,2,3,4")
    Err(err):
        expect("unexpected dataview prototype dispatch js error: {err}").to_equal("")
```

</details>

#### reads signed ArrayBuffer bytes through DataView in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `-1:255:-2:65534:-32768:32768:255,254,255,128,0,0`

3. Err
   - Expected: "unexpected signed dataview js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var buffer = new ArrayBuffer(6); var view = new DataView(buffer); view.setInt8(0, -1); view.setInt16(1, -2, true); view.setInt16(3, -32768, false); var bytes = new Uint8Array(buffer); view.getInt8(0) + ':' + view.getUint8(0) + ':' + view.getInt16(1, true) + ':' + view.getUint16(1, true) + ':' + view.getInt16(3, false) + ':' + view.getUint16(3, false) + ':' + bytes.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("-1:255:-2:65534:-32768:32768:255,254,255,128,0,0")
    Err(err):
        expect("unexpected signed dataview js error: {err}").to_equal("")
```

</details>

#### windows DataView bytes over ArrayBuffer offsets in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `2:4:3:258:-1:1,2,3,2,1,255,0,0`

3. Err
   - Expected: "unexpected dataview window js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var buffer = new ArrayBuffer(8); var bytes = new Uint8Array(buffer); bytes[0] = 1; bytes[1] = 2; bytes[2] = 3; bytes[3] = 4; bytes[4] = 5; var view = new DataView(buffer, 2, 4); view.setUint16(1, 258, true); view.setInt8(3, -1); view.byteOffset + ':' + view.byteLength + ':' + view.getUint8(0) + ':' + view.getUint16(1, true) + ':' + view.getInt8(3) + ':' + bytes.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2:4:3:258:-1:1,2,3,2,1,255,0,0")
    Err(err):
        expect("unexpected dataview window js error: {err}").to_equal("")
```

</details>

#### shares WebAssembly Memory buffer bytes with typed array views in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1:131072:131072:4:2:1`

3. Err
   - Expected: "unexpected wasm memory view js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var memory = new WebAssembly.Memory({ initial: 1, maximum: 2 }); var bytes = new Uint8Array(memory.buffer); bytes[4] = 260; var view = new DataView(memory.buffer); view.setUint16(6, 258, true); var old = memory.grow(1); var grown = new Uint8Array(memory.buffer); old + ':' + memory.buffer.byteLength + ':' + grown.length + ':' + grown[4] + ':' + grown[6] + ':' + grown[7]")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:131072:131072:4:2:1")
    Err(err):
        expect("unexpected wasm memory view js error: {err}").to_equal("")
```

</details>

#### preserves WebAssembly Memory state when grow exceeds maximum in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `65536:65536:1:-1:65536`

3. Err
   - Expected: "unexpected wasm memory grow limit js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val result = session.eval_script("var memory = new WebAssembly.Memory({ initial: 1, maximum: 1 }); var before = memory.buffer.byteLength; var first = memory.grow(0); var fail = memory.grow(1); var after = memory.buffer.byteLength; var bytes = new Uint8Array(memory.buffer); bytes.length + ':' + before + ':' + first + ':' + fail + ':' + after")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("65536:65536:1:-1:65536")
    Err(err):
        expect("unexpected wasm memory grow limit js error: {err}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession fetch WASM promise chain

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

