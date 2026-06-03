# Browser Session Fetch Wasm Chain Specification

> 1. var session = BrowserSession new

<!-- sdn-diagram:id=browser_session_fetch_wasm_chain_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_fetch_wasm_chain_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_fetch_wasm_chain_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_fetch_wasm_chain_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 142 | 142 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

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

#### exposes fetched arrayBuffer instantiated module export descriptors

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:40>instantiate:instantiated:40:2:tbl:table:answer:global`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes); }).then(function(result) { var exports = WebAssembly.Module.exports(result.module); out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + exports.length + ':' + exports[0].name + ':' + exports[0].kind + ':' + exports[1].name + ':' + exports[1].kind; }); 'queued'")
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
            body: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:40>instantiate:instantiated:40:2:tbl:table:answer:global")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer bytes into WebAssembly function body calls

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:41>instantiate:instantiated:41:function:42:42`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes); }).then(function(result) { out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + typeof result.instance.exports.run + ':' + result.instance.exports.run(40, 2) + ':' + result.instance.exports.run(7, 35); }); 'queued'")
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
            body: "0061736d0100000001070160027f7f017f030201000707010372756e00000a09010700200020016a0b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:41>instantiate:instantiated:41:function:42:42")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer bytes into multiple WebAssembly function exports

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:47>instantiate:instantiated:47:2:function:function:undefine... (full value in folded executable source)`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes); }).then(function(result) { var exports = result.instance.exports; out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + result.module.functionExportCount + ':' + typeof exports.init + ':' + typeof exports.render + ':' + exports.init() + ':' + exports.render(); }); 'queued'")
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
            body: "0061736d01000000010401600000030302000007110204696e697400000672656e64657200010a070202000b02000b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:47>instantiate:instantiated:47:2:function:function:undefined:undefined")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer bytes into WebAssembly table and global exports

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:40>instantiate:instantiated:40:table:funcref:null:1:2:globa... (full value in folded executable source)`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes); }).then(function(result) { var table = result.instance.exports.tbl; var global = result.instance.exports.answer; var before = table.get(0); var old = table.grow(1, null); out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + table.kind + ':' + table.element + ':' + before + ':' + old + ':' + table.length + ':' + global.kind + ':' + global.valueType + ':' + global.mutable + ':' + global.value; }); 'queued'")
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
            body: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:40>instantiate:instantiated:40:table:funcref:null:1:2:global:i32:false:42")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer bytes into WebAssembly memory exports

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:25>instantiate:instantiated:25:131072:65536:4:1:131072:4`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes); }).then(function(result) { var memory = result.instance.exports.memory; var bytes = new Uint8Array(memory.buffer); bytes[6] = 260; var old = memory.grow(1); var grown = new Uint8Array(memory.buffer); out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + memory.byteLength + ':' + memory.pageSize + ':' + bytes[6] + ':' + old + ':' + grown.length + ':' + grown[6]; }); 'queued'")
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
            body: "0061736d010000000503010001070a01066d656d6f72790200",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:25>instantiate:instantiated:25:131072:65536:4:1:131072:4")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer bytes into WebAssembly import calls

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:52>instantiate:instantiated:1:52:42:1`

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
val queued = session.eval_script("var out = ''; var stages = ''; var calls = 0; var imports = { env: { foo: function(x) { calls = calls + 1; return x + 2; } } }; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes, imports); }).then(function(result) { out = stages + 'instantiate:' + result.status + ':' + result.module.importCount + ':' + result.module.byteLength + ':' + result.instance.exports.run(40) + ':' + calls; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:52>instantiate:instantiated:1:52:42:1")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### exposes fetched arrayBuffer instantiated module import descriptors

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:27>instantiate:instantiated:1:27:1:env:foo:function:object`

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
val queued = session.eval_script("var out = ''; var stages = ''; var imports = { env: { foo: function() { return 7; } } }; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes, imports); }).then(function(result) { var descriptors = WebAssembly.Module.imports(result.module); out = stages + 'instantiate:' + result.status + ':' + result.module.importCount + ':' + result.module.byteLength + ':' + descriptors.length + ':' + descriptors[0].module + ':' + descriptors[0].name + ':' + descriptors[0].kind + ':' + typeof result.instance.exports; }); 'queued'")
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
            body: "0061736d01000000010401600000020b0103656e7603666f6f0000",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:27>instantiate:instantiated:1:27:1:env:foo:function:object")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes fetched arrayBuffer missing imports through catch

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:52>instantiateImports:invalid:unsupported-wasm-imports`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes, {}); }).then(function(result) { out = 'unexpected:' + result.status; }).catch(function(err) { out = stages + 'instantiateImports:' + err.status + ':' + err.error; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:52>instantiateImports:invalid:unsupported-wasm-imports")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer compiled modules into WebAssembly table and global exports

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:40>compile:40>instantiate:instantiated:40:table:funcref:nul... (full value in folded executable source)`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { stages = stages + 'compile:' + module.byteLength + '>'; return WebAssembly.instantiate(module); }).then(function(result) { var table = result.instance.exports.tbl; var global = result.instance.exports.answer; var before = table.get(0); var old = table.grow(1, null); out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + table.kind + ':' + table.element + ':' + before + ':' + old + ':' + table.length + ':' + global.kind + ':' + global.valueType + ':' + global.mutable + ':' + global.value; }); 'queued'")
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
            body: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:40>compile:40>instantiate:instantiated:40:table:funcref:null:1:2:global:i32:false:42")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer compiled modules into WebAssembly memory exports

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:25>compile:25>instantiate:instantiated:25:131072:65536:4:1:... (full value in folded executable source)`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { stages = stages + 'compile:' + module.byteLength + '>'; return WebAssembly.instantiate(module); }).then(function(result) { var memory = result.instance.exports.memory; var bytes = new Uint8Array(memory.buffer); bytes[8] = 260; var old = memory.grow(1); var grown = new Uint8Array(memory.buffer); out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + memory.byteLength + ':' + memory.pageSize + ':' + bytes[8] + ':' + old + ':' + grown.length + ':' + grown[8]; }); 'queued'")
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
            body: "0061736d010000000503010001070a01066d656d6f72790200",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:25>compile:25>instantiate:instantiated:25:131072:65536:4:1:131072:4")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer compiled modules into multiple WebAssembly function exports

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:47>compile:47>instantiate:instantiated:47:2:function:functi... (full value in folded executable source)`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { stages = stages + 'compile:' + module.byteLength + '>'; return WebAssembly.instantiate(module); }).then(function(result) { var exports = result.instance.exports; out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + result.module.functionExportCount + ':' + typeof exports.init + ':' + typeof exports.render + ':' + exports.init() + ':' + exports.render(); }); 'queued'")
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
            body: "0061736d01000000010401600000030302000007110204696e697400000672656e64657200010a070202000b02000b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:47>compile:47>instantiate:instantiated:47:2:function:function:undefined:undefined")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer compiled modules into WebAssembly import calls

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:52>compile:52>instantiate:instantiated:1:52:42:1`

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
val queued = session.eval_script("var out = ''; var stages = ''; var calls = 0; var imports = { env: { foo: function(x) { calls = calls + 1; return x + 3; } } }; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { stages = stages + 'compile:' + module.byteLength + '>'; return WebAssembly.instantiate(module, imports); }).then(function(result) { out = stages + 'instantiate:' + result.status + ':' + result.module.importCount + ':' + result.module.byteLength + ':' + result.instance.exports.run(39) + ':' + calls; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:52>compile:52>instantiate:instantiated:1:52:42:1")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes fetched arrayBuffer compiled missing imports through catch

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:52>compile:52>compileInstantiateImports:invalid:unsupported... (full value in folded executable source)`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { stages = stages + 'compile:' + module.byteLength + '>'; return WebAssembly.instantiate(module, {}); }).then(function(result) { out = 'unexpected:' + result.status; }).catch(function(err) { out = stages + 'compileInstantiateImports:' + err.status + ':' + err.error; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:52>compile:52>compileInstantiateImports:invalid:unsupported-wasm-imports")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes fetched invalid arrayBuffer instantiate results through catch

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
   - Expected: request.url equals `https://example.com/bad.wasm`

7. Ok

8. Ok
   - Expected: _display_js(value) equals `fetch>arrayBuffer:16>instantiateInvalid:invalid:invalid-wasm-header`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/bad.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.instantiate(bytes); }).then(function(result) { out = 'unexpected:' + result.status; }).catch(function(err) { out = stages + 'instantiateInvalid:' + err.status + ':' + err.error; }); 'queued'")
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
        expect(request.url).to_equal("https://example.com/bad.wasm")
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: application/wasm\n",
            body: "0061736d00000000",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:16>instantiateInvalid:invalid:invalid-wasm-header")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes fetched arrayBuffer instantiate fetch errors through catch

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
   - Expected: request.url equals `https://example.com/down.wasm`

7. Ok
   - Expected: "expected fetch commit error" equals ``

8. Err
   - Expected: err equals `network-down`

9. Ok
   - Expected: _display_js(value) equals `instantiateFetchError:network-down`

10. Err
   - Expected: "unexpected js error: {js_err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val queued = session.eval_script("var out = ''; window.fetch('/down.wasm').then(function(r) { return r.arrayBuffer(); }).then(function(bytes) { return WebAssembly.instantiate(bytes); }).then(function(result) { out = 'unexpected:' + result.status; }).catch(function(err) { out = 'instantiateFetchError:' + err; }); 'queued'")
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
        expect(request.url).to_equal("https://example.com/down.wasm")
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 0,
            headers: "",
            body: "",
            error: "network-down"
        ))
        match committed:
            Ok(_):
                expect("expected fetch commit error").to_equal("")
            Err(err):
                expect(err).to_equal("network-down")
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("instantiateFetchError:network-down")
                    Err(js_err):
                        expect("unexpected js error: {js_err}").to_equal("")
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

#### exposes fetched arrayBuffer compiled module export descriptors

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:40>compile:40:2:tbl:table:answer:global`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { var exports = WebAssembly.Module.exports(module); out = stages + 'compile:' + module.byteLength + ':' + exports.length + ':' + exports[0].name + ':' + exports[0].kind + ':' + exports[1].name + ':' + exports[1].kind; }); 'queued'")
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
            body: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:40>compile:40:2:tbl:table:answer:global")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### exposes fetched arrayBuffer compiled module import descriptors

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:27>compile:1:27:1:env:foo:function`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { var descriptors = WebAssembly.Module.imports(module); out = stages + 'compile:' + module.importCount + ':' + module.byteLength + ':' + descriptors.length + ':' + descriptors[0].module + ':' + descriptors[0].name + ':' + descriptors[0].kind; }); 'queued'")
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
            body: "0061736d01000000010401600000020b0103656e7603666f6f0000",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:27>compile:1:27:1:env:foo:function")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes fetched invalid arrayBuffer compile results through catch

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
   - Expected: request.url equals `https://example.com/bad.wasm`

7. Ok

8. Ok
   - Expected: _display_js(value) equals `fetch>arrayBuffer:16>compileInvalid:invalid:invalid-wasm-header`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/bad.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { out = 'unexpected:' + module.byteLength; }).catch(function(err) { out = stages + 'compileInvalid:' + err.status + ':' + err.error; }); 'queued'")
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
        expect(request.url).to_equal("https://example.com/bad.wasm")
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 200,
            headers: "Content-Type: application/wasm\n",
            body: "0061736d00000000",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:16>compileInvalid:invalid:invalid-wasm-header")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes fetched arrayBuffer compile fetch errors through catch

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
   - Expected: request.url equals `https://example.com/down.wasm`

7. Ok
   - Expected: "expected fetch commit error" equals ``

8. Err
   - Expected: err equals `network-down`

9. Ok
   - Expected: _display_js(value) equals `compileFetchError:network-down`

10. Err
   - Expected: "unexpected js error: {js_err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val queued = session.eval_script("var out = ''; window.fetch('/down.wasm').then(function(r) { return r.arrayBuffer(); }).then(function(bytes) { return WebAssembly.compile(bytes); }).then(function(module) { out = 'unexpected:' + module.byteLength; }).catch(function(err) { out = 'compileFetchError:' + err; }); 'queued'")
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
        expect(request.url).to_equal("https://example.com/down.wasm")
        val committed = session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: "fetch",
            url: request.url,
            status: 0,
            headers: "",
            body: "",
            error: "network-down"
        ))
        match committed:
            Ok(_):
                expect("expected fetch commit error").to_equal("")
            Err(err):
                expect(err).to_equal("network-down")
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileFetchError:network-down")
                    Err(js_err):
                        expect("unexpected js error: {js_err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### chains fetched arrayBuffer bytes through WebAssembly.compile into function body calls

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
   - Expected: _display_js(value) equals `fetch>arrayBuffer:41>compile:41>instantiate:instantiated:41:function:42:42`

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
val queued = session.eval_script("var out = ''; var stages = ''; window.fetch('/mod.wasm').then(function(r) { stages = stages + 'fetch>'; return r.arrayBuffer(); }).then(function(bytes) { stages = stages + 'arrayBuffer:' + bytes.byteLength + '>'; return WebAssembly.compile(bytes); }).then(function(module) { stages = stages + 'compile:' + module.byteLength + '>'; return WebAssembly.instantiate(module); }).then(function(result) { out = stages + 'instantiate:' + result.status + ':' + result.module.byteLength + ':' + typeof result.instance.exports.run + ':' + result.instance.exports.run(40, 2) + ':' + result.instance.exports.run(7, 35); }); 'queued'")
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
            body: "0061736d0100000001070160027f7f017f030201000707010372756e00000a09010700200020016a0b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("fetch>arrayBuffer:41>compile:41>instantiate:instantiated:41:function:42:42")
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

#### exposes instantiated WebAssembly module export descriptors in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:40:2:tbl:table:answer:global`

3. Err
   - Expected: "unexpected instantiated descriptor js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; WebAssembly.instantiate('0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300').then(function(result) { var exports = WebAssembly.Module.exports(result.module); out = result.status + ':' + result.module.byteLength + ':' + exports.length + ':' + exports[0].name + ':' + exports[0].kind + ':' + exports[1].name + ':' + exports[1].kind; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:40:2:tbl:table:answer:global")
    Err(err):
        expect("unexpected instantiated descriptor js error: {err}").to_equal("")
```

</details>

#### exposes compiled WebAssembly module export descriptors in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `40:2:tbl:table:answer:global`

3. Err
   - Expected: "unexpected compiled export descriptor js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; WebAssembly.compile('0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300').then(function(module) { var exports = WebAssembly.Module.exports(module); out = module.byteLength + ':' + exports.length + ':' + exports[0].name + ':' + exports[0].kind + ':' + exports[1].name + ':' + exports[1].kind; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("40:2:tbl:table:answer:global")
    Err(err):
        expect("unexpected compiled export descriptor js error: {err}").to_equal("")
```

</details>

#### exposes instantiated WebAssembly module import descriptors in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:1:1:env:foo:function:object`

3. Err
   - Expected: "unexpected instantiated import descriptor js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; var imports = { env: { foo: function() { return 7; } } }; WebAssembly.instantiate('0061736d01000000010401600000020b0103656e7603666f6f0000', imports).then(function(result) { var descriptors = WebAssembly.Module.imports(result.module); out = result.status + ':' + result.module.importCount + ':' + descriptors.length + ':' + descriptors[0].module + ':' + descriptors[0].name + ':' + descriptors[0].kind + ':' + typeof result.instance.exports; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:1:1:env:foo:function:object")
    Err(err):
        expect("unexpected instantiated import descriptor js error: {err}").to_equal("")
```

</details>

#### exposes compiled WebAssembly module import descriptors in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1:27:1:env:foo:function`

3. Err
   - Expected: "unexpected compiled import descriptor js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; WebAssembly.compile('0061736d01000000010401600000020b0103656e7603666f6f0000').then(function(module) { var descriptors = WebAssembly.Module.imports(module); out = module.importCount + ':' + module.byteLength + ':' + descriptors.length + ':' + descriptors[0].module + ':' + descriptors[0].name + ':' + descriptors[0].kind; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:27:1:env:foo:function")
    Err(err):
        expect("unexpected compiled import descriptor js error: {err}").to_equal("")
```

</details>

#### invokes direct WebAssembly instantiate imports through exported functions

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:1:42:1`

3. Err
   - Expected: "unexpected direct instantiate import call js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; var calls = 0; var imports = { env: { foo: function(x) { calls = calls + 1; return x + 2; } } }; WebAssembly.instantiate('0061736d0100000001060160017f017f020b0103656e7603666f6f0000030201000707010372756e00010a08010600200010000b', imports).then(function(result) { out = result.status + ':' + result.module.importCount + ':' + result.instance.exports.run(40) + ':' + calls; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:1:42:1")
    Err(err):
        expect("unexpected direct instantiate import call js error: {err}").to_equal("")
```

</details>

#### instantiates compiled WebAssembly imports through exported functions

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:1:52:42:1`

3. Err
   - Expected: "unexpected compiled instantiate import call js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; var calls = 0; var imports = { env: { foo: function(x) { calls = calls + 1; return x + 3; } } }; WebAssembly.compile('0061736d0100000001060160017f017f020b0103656e7603666f6f0000030201000707010372756e00010a08010600200010000b').then(function(module) { return WebAssembly.instantiate(module, imports); }).then(function(result) { out = result.status + ':' + result.module.importCount + ':' + result.module.byteLength + ':' + result.instance.exports.run(39) + ':' + calls; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:1:52:42:1")
    Err(err):
        expect("unexpected compiled instantiate import call js error: {err}").to_equal("")
```

</details>

#### instantiates compiled WebAssembly function export bodies with call arguments

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:41:function:42:42`

3. Err
   - Expected: "unexpected compiled function export body argument js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; WebAssembly.compile('0061736d0100000001070160027f7f017f030201000707010372756e00000a09010700200020016a0b').then(function(module) { return WebAssembly.instantiate(module); }).then(function(result) { out = result.status + ':' + result.module.byteLength + ':' + typeof result.instance.exports.run + ':' + result.instance.exports.run(40, 2) + ':' + result.instance.exports.run(7, 35); }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:41:function:42:42")
    Err(err):
        expect("unexpected compiled function export body argument js error: {err}").to_equal("")
```

</details>

#### constructs WebAssembly Instance imports through exported functions

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1:52:instantiated:function:42:1`

3. Err
   - Expected: "unexpected instance constructor import call js error: {err}" equals ``


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
val result = session.eval_script("var calls = 0; var imports = { env: { foo: function(x) { calls = calls + 1; return x + 5; } } }; var module = new WebAssembly.Module('0061736d0100000001060160017f017f020b0103656e7603666f6f0000030201000707010372756e00010a08010600200010000b'); var instance = new WebAssembly.Instance(module, imports); module.importCount + ':' + module.byteLength + ':' + instance.status + ':' + typeof instance.exports.run + ':' + instance.exports.run(37) + ':' + calls")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:52:instantiated:function:42:1")
    Err(err):
        expect("unexpected instance constructor import call js error: {err}").to_equal("")
```

</details>

#### constructs WebAssembly Instance function export bodies with call arguments

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `41:instantiated:function:42:42`

3. Err
   - Expected: "unexpected instance constructor function export body argument js error: {err}" equals ``


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
val result = session.eval_script("var module = new WebAssembly.Module('0061736d0100000001070160027f7f017f030201000707010372756e00000a09010700200020016a0b'); var instance = new WebAssembly.Instance(module); module.byteLength + ':' + instance.status + ':' + typeof instance.exports.run + ':' + instance.exports.run(40, 2) + ':' + instance.exports.run(7, 35)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("41:instantiated:function:42:42")
    Err(err):
        expect("unexpected instance constructor function export body argument js error: {err}").to_equal("")
```

</details>

#### synthesizes multiple WebAssembly function exports in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:47:2:function:function:undefined:undefined`

3. Err
   - Expected: "unexpected multiple function export js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; WebAssembly.instantiate('0061736d01000000010401600000030302000007110204696e697400000672656e64657200010a070202000b02000b').then(function(result) { var exports = result.instance.exports; out = result.status + ':' + result.module.byteLength + ':' + result.module.functionExportCount + ':' + typeof exports.init + ':' + typeof exports.render + ':' + exports.init() + ':' + exports.render(); }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:47:2:function:function:undefined:undefined")
    Err(err):
        expect("unexpected multiple function export js error: {err}").to_equal("")
```

</details>

#### executes WebAssembly function export bodies with call arguments in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:41:function:42:42`

3. Err
   - Expected: "unexpected function export body argument js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; WebAssembly.instantiate('0061736d0100000001070160027f7f017f030201000707010372756e00000a09010700200020016a0b').then(function(result) { out = result.status + ':' + result.module.byteLength + ':' + typeof result.instance.exports.run + ':' + result.instance.exports.run(40, 2) + ':' + result.instance.exports.run(7, 35); }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:41:function:42:42")
    Err(err):
        expect("unexpected function export body argument js error: {err}").to_equal("")
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

#### exposes instantiateStreaming module export descriptors

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
   - Expected: _display_js(value) equals `streamExportDescriptors:instantiated:40:2:tbl:table:answer:global`

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
val queued = session.eval_script("var out = ''; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm')).then(function(result) { var exports = WebAssembly.Module.exports(result.module); out = 'streamExportDescriptors:' + result.status + ':' + result.module.byteLength + ':' + exports.length + ':' + exports[0].name + ':' + exports[0].kind + ':' + exports[1].name + ':' + exports[1].kind; }); 'queued'")
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
            body: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("streamExportDescriptors:instantiated:40:2:tbl:table:answer:global")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates streaming multiple function exports in browser scripts

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
   - Expected: _display_js(value) equals `streamFunctions:instantiated:47:2:function:function:undefined:undefined`

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
val queued = session.eval_script("var out = ''; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm')).then(function(result) { var exports = result.instance.exports; out = 'streamFunctions:' + result.status + ':' + result.module.byteLength + ':' + result.module.functionExportCount + ':' + typeof exports.init + ':' + typeof exports.render + ':' + exports.init() + ':' + exports.render(); }); 'queued'")
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
            body: "0061736d01000000010401600000030302000007110204696e697400000672656e64657200010a070202000b02000b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("streamFunctions:instantiated:47:2:function:function:undefined:undefined")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates streaming WebAssembly function export bodies with call arguments

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
   - Expected: _display_js(value) equals `streamArgBody:instantiated:41:function:42:42`

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
val queued = session.eval_script("var out = ''; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm')).then(function(result) { out = 'streamArgBody:' + result.status + ':' + result.module.byteLength + ':' + typeof result.instance.exports.run + ':' + result.instance.exports.run(40, 2) + ':' + result.instance.exports.run(7, 35); }); 'queued'")
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
            body: "0061736d0100000001070160027f7f017f030201000707010372756e00000a09010700200020016a0b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("streamArgBody:instantiated:41:function:42:42")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates streaming table and global exports in browser scripts

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
   - Expected: _display_js(value) equals `streamExports:instantiated:40:table:funcref:null:1:2:global:i32:false:42`

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
val queued = session.eval_script("var out = ''; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm')).then(function(result) { var table = result.instance.exports.tbl; var global = result.instance.exports.answer; var before = table.get(0); var old = table.grow(1, null); out = 'streamExports:' + result.status + ':' + result.module.byteLength + ':' + table.kind + ':' + table.element + ':' + before + ':' + old + ':' + table.length + ':' + global.kind + ':' + global.valueType + ':' + global.mutable + ':' + global.value; }); 'queued'")
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
            body: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("streamExports:instantiated:40:table:funcref:null:1:2:global:i32:false:42")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates streaming memory exports in browser scripts

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
   - Expected: _display_js(value) equals `streamMemory:instantiated:25:131072:65536:4:1:131072:4`

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
val queued = session.eval_script("var out = ''; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm')).then(function(result) { var memory = result.instance.exports.memory; var bytes = new Uint8Array(memory.buffer); bytes[5] = 260; var old = memory.grow(1); var grown = new Uint8Array(memory.buffer); out = 'streamMemory:' + result.status + ':' + result.module.byteLength + ':' + memory.byteLength + ':' + memory.pageSize + ':' + bytes[5] + ':' + old + ':' + grown.length + ':' + grown[5]; }); 'queued'")
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
            body: "0061736d010000000503010001070a01066d656d6f72790200",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("streamMemory:instantiated:25:131072:65536:4:1:131072:4")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes invalid instantiateStreaming responses through catch

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
   - Expected: _display_js(value) equals `instantiateStreamInvalid:invalid:invalid-wasm-header`

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
val queued = session.eval_script("var out = ''; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm'), {}).then(function(result) { out = 'unexpected:' + result.status; }).catch(function(err) { out = 'instantiateStreamInvalid:' + err.status + ':' + err.error; }); 'queued'")
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
            body: "0061736d00000000",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("instantiateStreamInvalid:invalid:invalid-wasm-header")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes instantiateStreaming fetch errors through catch

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
   - Expected: "expected fetch commit error" equals ``

8. Err
   - Expected: err equals `network-down`

9. Ok
   - Expected: _display_js(value) equals `instantiateStreamFetchError:network-down`

10. Err
   - Expected: "unexpected js error: {js_err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val queued = session.eval_script("var out = ''; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm'), {}).then(function(result) { out = 'unexpected:' + result.status; }).catch(function(err) { out = 'instantiateStreamFetchError:' + err; }); 'queued'")
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
            status: 0,
            headers: "",
            body: "",
            error: "network-down"
        ))
        match committed:
            Ok(_):
                expect("expected fetch commit error").to_equal("")
            Err(err):
                expect(err).to_equal("network-down")
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("instantiateStreamFetchError:network-down")
                    Err(js_err):
                        expect("unexpected js error: {js_err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes instantiateStreaming missing imports through catch

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
   - Expected: _display_js(value) equals `instantiateStreamImports:invalid:unsupported-wasm-imports`

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
val queued = session.eval_script("var out = ''; WebAssembly.instantiateStreaming(window.fetch('/mod.wasm'), {}).then(function(result) { out = 'unexpected:' + result.status; }).catch(function(err) { out = 'instantiateStreamImports:' + err.status + ':' + err.error; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("instantiateStreamImports:invalid:unsupported-wasm-imports")
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

#### routes invalid compileStreaming responses through catch

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
   - Expected: _display_js(value) equals `compileStreamInvalid:invalid-wasm-header`

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
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { out = 'unexpected:' + module.byteLength; }).catch(function(err) { out = 'compileStreamInvalid:' + err; }); 'queued'")
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
            body: "0061736d00000000",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileStreamInvalid:invalid-wasm-header")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes compileStreaming fetch errors through catch

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
   - Expected: "expected fetch commit error" equals ``

8. Err
   - Expected: err equals `network-down`

9. Ok
   - Expected: _display_js(value) equals `compileStreamFetchError:network-down`

10. Err
   - Expected: "unexpected js error: {js_err}" equals ``
   - Expected: "missing fetch request" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/webgpu-wasm.html",
    "<html><body>WASM GPU</body></html>"
)
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { out = 'unexpected:' + module.byteLength; }).catch(function(err) { out = 'compileStreamFetchError:' + err; }); 'queued'")
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
            status: 0,
            headers: "",
            body: "",
            error: "network-down"
        ))
        match committed:
            Ok(_):
                expect("expected fetch commit error").to_equal("")
            Err(err):
                expect(err).to_equal("network-down")
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileStreamFetchError:network-down")
                    Err(js_err):
                        expect("unexpected js error: {js_err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### exposes compileStreaming module export descriptors

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
   - Expected: _display_js(value) equals `compileStreamExports:40:2:tbl:table:answer:global`

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
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { var exports = WebAssembly.Module.exports(module); out = 'compileStreamExports:' + module.byteLength + ':' + exports.length + ':' + exports[0].name + ':' + exports[0].kind + ':' + exports[1].name + ':' + exports[1].kind; }); 'queued'")
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
            body: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileStreamExports:40:2:tbl:table:answer:global")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates compileStreaming table and global exports in browser scripts

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
   - Expected: _display_js(value) equals `compileStreamExports:instantiated:40:table:funcref:null:1:2:global:i32:false:42`

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
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { return WebAssembly.instantiate(module).then(function(result) { var table = result.instance.exports.tbl; var global = result.instance.exports.answer; var before = table.get(0); var old = table.grow(1, null); out = 'compileStreamExports:' + result.status + ':' + result.module.byteLength + ':' + table.kind + ':' + table.element + ':' + before + ':' + old + ':' + table.length + ':' + global.kind + ':' + global.valueType + ':' + global.mutable + ':' + global.value; }); }); 'queued'")
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
            body: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileStreamExports:instantiated:40:table:funcref:null:1:2:global:i32:false:42")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates compileStreaming multiple function exports in browser scripts

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
   - Expected: _display_js(value) equals `compileStreamFunctions:instantiated:47:2:function:function:undefined:undefined`

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
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { return WebAssembly.instantiate(module).then(function(result) { var exports = result.instance.exports; out = 'compileStreamFunctions:' + result.status + ':' + result.module.byteLength + ':' + result.module.functionExportCount + ':' + typeof exports.init + ':' + typeof exports.render + ':' + exports.init() + ':' + exports.render(); }); }); 'queued'")
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
            body: "0061736d01000000010401600000030302000007110204696e697400000672656e64657200010a070202000b02000b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileStreamFunctions:instantiated:47:2:function:function:undefined:undefined")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates compileStreaming WebAssembly function export bodies with call arguments

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
   - Expected: _display_js(value) equals `compileStreamArgBody:instantiated:41:function:42:42`

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
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { return WebAssembly.instantiate(module).then(function(result) { out = 'compileStreamArgBody:' + result.status + ':' + result.module.byteLength + ':' + typeof result.instance.exports.run + ':' + result.instance.exports.run(40, 2) + ':' + result.instance.exports.run(7, 35); }); }); 'queued'")
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
            body: "0061736d0100000001070160027f7f017f030201000707010372756e00000a09010700200020016a0b",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileStreamArgBody:instantiated:41:function:42:42")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates compileStreaming memory exports in browser scripts

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
   - Expected: _display_js(value) equals `compileStreamMemory:instantiated:25:131072:65536:4:1:131072:4`

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
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { return WebAssembly.instantiate(module).then(function(result) { var memory = result.instance.exports.memory; var bytes = new Uint8Array(memory.buffer); bytes[7] = 260; var old = memory.grow(1); var grown = new Uint8Array(memory.buffer); out = 'compileStreamMemory:' + result.status + ':' + result.module.byteLength + ':' + memory.byteLength + ':' + memory.pageSize + ':' + bytes[7] + ':' + old + ':' + grown.length + ':' + grown[7]; }); }); 'queued'")
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
            body: "0061736d010000000503010001070a01066d656d6f72790200",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileStreamMemory:instantiated:25:131072:65536:4:1:131072:4")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### exposes compileStreaming module import descriptors

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
   - Expected: _display_js(value) equals `compileStreamImports:1:27:1:env:foo:function`

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
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { var descriptors = WebAssembly.Module.imports(module); out = 'compileStreamImports:' + module.importCount + ':' + module.byteLength + ':' + descriptors.length + ':' + descriptors[0].module + ':' + descriptors[0].name + ':' + descriptors[0].kind; }); 'queued'")
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
            body: "0061736d01000000010401600000020b0103656e7603666f6f0000",
            error: ""
        ))
        match committed:
            Ok(_):
                match session.eval_script("out"):
                    Ok(value):
                        expect(_display_js(value)).to_equal("compileStreamImports:1:27:1:env:foo:function")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### instantiates compileStreaming modules with imports

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
   - Expected: _display_js(value) equals `compileStreamImport:1:52:42:1`

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
val queued = session.eval_script("var out = ''; var calls = 0; var imports = { env: { foo: function(x) { calls = calls + 1; return x + 4; } } }; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { return WebAssembly.instantiate(module, imports); }).then(function(result) { out = 'compileStreamImport:' + result.module.importCount + ':' + result.module.byteLength + ':' + result.instance.exports.run(38) + ':' + calls; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("compileStreamImport:1:52:42:1")
                    Err(err):
                        expect("unexpected js error: {err}").to_equal("")
            Err(err):
                expect("unexpected commit error: {err}").to_equal("")
    nil:
        expect("missing fetch request").to_equal("")
```

</details>

#### routes compileStreaming instantiate missing imports through catch

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
   - Expected: _display_js(value) equals `compileStreamInstantiateImports:invalid:unsupported-wasm-imports`

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
val queued = session.eval_script("var out = ''; WebAssembly.compileStreaming(window.fetch('/mod.wasm')).then(function(module) { return WebAssembly.instantiate(module, {}); }).then(function(result) { out = 'unexpected:' + result.status; }).catch(function(err) { out = 'compileStreamInstantiateImports:' + err.status + ':' + err.error; }); 'queued'")
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
                        expect(_display_js(value)).to_equal("compileStreamInstantiateImports:invalid:unsupported-wasm-imports")
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

#### exposes instantiated WebAssembly table and global exports in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:table:funcref:null:1:2:global:i32:false:42`

3. Err
   - Expected: "unexpected instantiated table/global export js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; WebAssembly.instantiate('0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300').then(function(result) { var table = result.instance.exports.tbl; var global = result.instance.exports.answer; var before = table.get(0); var old = table.grow(1, null); out = result.status + ':' + table.kind + ':' + table.element + ':' + before + ':' + old + ':' + table.length + ':' + global.kind + ':' + global.valueType + ':' + global.mutable + ':' + global.value; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:table:funcref:null:1:2:global:i32:false:42")
    Err(err):
        expect("unexpected instantiated table/global export js error: {err}").to_equal("")
```

</details>

#### exposes instantiated WebAssembly memory exports in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `instantiated:25:131072:65536:4:1:131072:4`

3. Err
   - Expected: "unexpected instantiated memory export js error: {err}" equals ``


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
val result = session.eval_script("var out = ''; WebAssembly.instantiate('0061736d010000000503010001070a01066d656d6f72790200').then(function(result) { var memory = result.instance.exports.memory; var bytes = new Uint8Array(memory.buffer); bytes[3] = 260; var old = memory.grow(1); var grown = new Uint8Array(memory.buffer); out = result.status + ':' + result.module.byteLength + ':' + memory.byteLength + ':' + memory.pageSize + ':' + bytes[3] + ':' + old + ':' + grown.length + ':' + grown[3]; }); out")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("instantiated:25:131072:65536:4:1:131072:4")
    Err(err):
        expect("unexpected instantiated memory export js error: {err}").to_equal("")
```

</details>

#### mutates WebAssembly Global values in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `7:9:i32:true:3:false`

3. Err
   - Expected: "unexpected global mutation js error: {err}" equals ``


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
val result = session.eval_script("var global = new WebAssembly.Global({ value: 'i32', mutable: true }, 7); var before = global.value; global.value = 9; var immutable = new WebAssembly.Global({ value: 'i32', mutable: false }, 3); before + ':' + global.value + ':' + global.valueType + ':' + global.mutable + ':' + immutable.value + ':' + immutable.mutable")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("7:9:i32:true:3:false")
    Err(err):
        expect("unexpected global mutation js error: {err}").to_equal("")
```

</details>

#### preserves WebAssembly Table slots when grow exceeds maximum

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `2:1:-1:slot0:slot1`

3. Err
   - Expected: "unexpected table grow limit js error: {err}" equals ``


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
val result = session.eval_script("var table = new WebAssembly.Table({ element: 'externref', initial: 1, maximum: 2 }); table.set(0, 'slot0'); var old = table.grow(1, 'slot1'); var fail = table.grow(1, 'slot2'); table.length + ':' + old + ':' + fail + ':' + table.get(0) + ':' + table.get(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2:1:-1:slot0:slot1")
    Err(err):
        expect("unexpected table grow limit js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype lastIndexOf edge ranges with apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4:2:3:-1`

3. Err
   - Expected: "unexpected uint8 lastIndexOf apply edge dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(6); b[0] = 4; b[1] = 7; b[2] = 4; b[3] = -1; b[4] = 4; b[5] = 0; Uint8Array.prototype.lastIndexOf.apply(b, [4, -2]) + ':' + Uint8Array.prototype.lastIndexOf.apply(b, [4, -3]) + ':' + Uint8Array.prototype.lastIndexOf.apply(b, [-1, -2]) + ':' + Uint8Array.prototype.lastIndexOf.apply(b, [-1, -4])")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4:2:3:-1")
    Err(err):
        expect("unexpected uint8 lastIndexOf apply edge dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype string helpers with apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1|4|255|7:1,4,255,7:1,4,255,7`

3. Err
   - Expected: "unexpected uint8 string apply dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; Uint8Array.prototype.join.apply(b, ['|']) + ':' + Uint8Array.prototype.join.apply(b, []) + ':' + Uint8Array.prototype.toString.apply(b, [])")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1|4|255|7:1,4,255,7:1,4,255,7")
    Err(err):
        expect("unexpected uint8 string apply dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype at and reverse with complementary call and apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `255:undefined:7,255,4,1:true:7`

3. Err
   - Expected: "unexpected uint8 at reverse complementary dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; var neg = Uint8Array.prototype.at.call(b, -2); var miss = Uint8Array.prototype.at.call(b, 9); var returned = Uint8Array.prototype.reverse.apply(b, []); neg + ':' + miss + ':' + b.toString() + ':' + (returned === b) + ':' + returned.at(0)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("255:undefined:7,255,4,1:true:7")
    Err(err):
        expect("unexpected uint8 at reverse complementary dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype mutating and search helpers with call and apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `0-4-4-4-0:true:2:0,4,4,4,0:0,4,0,4,0:4`

3. Err
   - Expected: "unexpected uint8 prototype helper dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(5); Uint8Array.prototype.fill.call(b, 260, 1, 4); var search = Uint8Array.prototype.includes.call(b, 4) + ':' + Uint8Array.prototype.indexOf.apply(b, [4, 2]); var joined = Uint8Array.prototype.join.call(b, '-'); var reversed = Uint8Array.prototype.reverse.call(b); var reversedJoin = reversed.join(','); var copied = Uint8Array.prototype.copyWithin.apply(b, [1, -2]); joined + ':' + search + ':' + reversedJoin + ':' + b.join(',') + ':' + copied.at(1)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("0-4-4-4-0:true:2:0,4,4,4,0:0,4,0,4,0:4")
    Err(err):
        expect("unexpected uint8 prototype helper dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype search edge ranges with complementary call and apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `true:false:false:4:3`

3. Err
   - Expected: "unexpected uint8 search edge complementary dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(6); b[0] = 4; b[1] = 7; b[2] = 4; b[3] = -1; b[4] = 4; b[5] = 0; Uint8Array.prototype.includes.apply(b, [4, -2]) + ':' + Uint8Array.prototype.includes.apply(b, [-1, -2]) + ':' + Uint8Array.prototype.includes.apply(b, [7, -2]) + ':' + Uint8Array.prototype.indexOf.call(b, 4, -3) + ':' + Uint8Array.prototype.indexOf.call(b, -1, -4)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:false:false:4:3")
    Err(err):
        expect("unexpected uint8 search edge complementary dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype fill edge ranges with apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,254,254,254,5,6:true:254`

3. Err
   - Expected: "unexpected uint8 fill edge apply dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(6); b[0] = 1; b[1] = 2; b[2] = 3; b[3] = 4; b[4] = 5; b[5] = 6; var returned = Uint8Array.prototype.fill.apply(b, [-2, -5, -2]); b.toString() + ':' + (returned === b) + ':' + returned.at(3)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,254,254,254,5,6:true:254")
    Err(err):
        expect("unexpected uint8 fill edge apply dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype copyWithin edge ranges with call and apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,2,1,2,3,6:2,3,1,2,3,6:true:true`

3. Err
   - Expected: "unexpected uint8 copyWithin edge dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(6); b[0] = 1; b[1] = 2; b[2] = 3; b[3] = 4; b[4] = 5; b[5] = 6; var viaCall = Uint8Array.prototype.copyWithin.call(b, -4, 0, 3); var afterCall = b.toString(); var viaApply = Uint8Array.prototype.copyWithin.apply(b, [0, -3, -1]); afterCall + ':' + b.toString() + ':' + (viaCall === b) + ':' + (viaApply === b)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,2,1,2,3,6:2,3,1,2,3,6:true:true")
    Err(err):
        expect("unexpected uint8 copyWithin edge dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches remaining Uint8Array prototype helpers with call and apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,4,255,7,9:undefined:2:7:0,1:0=1,1=4`

3. Err
   - Expected: "unexpected uint8 remaining prototype helper dispatch js error: {err}" equals ``


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
val result = session.eval_script("var dst = new Uint8Array(5); dst[0] = 1; dst[4] = 9; var src = new Uint8Array(3); src[0] = 260; src[1] = -1; src[2] = 7; var setRet = Uint8Array.prototype.set.call(dst, src, 1); var last = Uint8Array.prototype.lastIndexOf.call(dst, 255); var str = Uint8Array.prototype.toString.call(dst); var at = Uint8Array.prototype.at.apply(dst, [-2]); var keys = Uint8Array.prototype.keys.call(dst); var k0 = keys.next(); var k1 = keys.next(); var entries = Uint8Array.prototype.entries.apply(dst, []); var e0 = entries.next(); var e1 = entries.next(); str + ':' + setRet + ':' + last + ':' + at + ':' + k0.value + ',' + k1.value + ':' + e0.value[0] + '=' + e0.value[1] + ',' + e1.value[0] + '=' + e1.value[1]")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,4,255,7,9:undefined:2:7:0,1:0=1,1=4")
    Err(err):
        expect("unexpected uint8 remaining prototype helper dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype some with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `true`

3. Err
   - Expected: "unexpected uint8 prototype some dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; Uint8Array.prototype.some.call(b, function(v, i, arr) { return v == 255 && i == 2 && arr.at(3) == 7; })")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true")
    Err(err):
        expect("unexpected uint8 prototype some dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype every with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `true:false`

3. Err
   - Expected: "unexpected uint8 prototype every dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; Uint8Array.prototype.every.call(b, function(v, i, arr) { return arr.at(i) == v && v >= 0; }) + ':' + Uint8Array.prototype.every.call(b, function(v, i, arr) { return i < 2 || arr.at(i) < 10; })")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:false")
    Err(err):
        expect("unexpected uint8 prototype every dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype predicates with apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `true:false`

3. Err
   - Expected: "unexpected uint8 prototype predicate apply js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; var some = Uint8Array.prototype.some.apply(b, [function(v, i, arr) { return v == 255 && i == 2 && arr.at(3) == 7; }]); var every = Uint8Array.prototype.every.apply(b, [function(v, i, arr) { return arr.at(i) == v && v < 255; }]); some + ':' + every")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:false")
    Err(err):
        expect("unexpected uint8 prototype predicate apply js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype forEach with call and apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `532:0=4;1=255;2=7;:undefined:undefined`

3. Err
   - Expected: "unexpected uint8 prototype forEach dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; var total = 0; var seen = ''; var ret1 = Uint8Array.prototype.forEach.call(b, function(v, i, arr) { total = total + v; seen = seen + i + '=' + arr.at(i) + ';'; }); var ret2 = Uint8Array.prototype.forEach.apply(b, [function(v, i, arr) { total = total + arr.at(i); }]); total + ':' + seen + ':' + ret1 + ':' + ret2")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("532:0=4;1=255;2=7;:undefined:undefined")
    Err(err):
        expect("unexpected uint8 prototype forEach dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype find helpers with call and apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `255:3:undefined:-1`

3. Err
   - Expected: "unexpected uint8 prototype find dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; var found = Uint8Array.prototype.find.call(b, function(v, i, arr) { return v == 255 && i == 2 && arr.at(3) == 7; }); var idx = Uint8Array.prototype.findIndex.call(b, function(v, i, arr) { return arr.at(i) == 7; }); var miss = Uint8Array.prototype.find.apply(b, [function(v) { return v == 99; }]); var missIdx = Uint8Array.prototype.findIndex.apply(b, [function(v) { return v == 99; }]); found + ':' + idx + ':' + miss + ':' + missIdx")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("255:3:undefined:-1")
    Err(err):
        expect("unexpected uint8 prototype find dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches Uint8Array prototype transform helpers with apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `8,255,16,19:255,7,8:554:19016511008:4,255,7,8`

3. Err
   - Expected: "unexpected uint8 prototype transform apply dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 260; b[1] = -1; b[2] = 7; b[3] = 8; var mapped = Uint8Array.prototype.map.apply(b, [function(v, i, arr) { return v + i + arr.at(i); }]); var filtered = Uint8Array.prototype.filter.apply(b, [function(v, i, arr) { return i && arr.at(0) == 4; }]); var reduced = Uint8Array.prototype.reduce.apply(b, [function(acc, v, i, arr) { return acc + v + i + arr.at(i); }, 0]); var reducedRight = Uint8Array.prototype.reduceRight.apply(b, [function(acc, v, i, arr) { return acc * 1000 + v + i + arr.at(i); }, 0]); mapped.toString() + ':' + filtered.toString() + ':' + reduced + ':' + reducedRight + ':' + b.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("8,255,16,19:255,7,8:554:19016511008:4,255,7,8")
    Err(err):
        expect("unexpected uint8 prototype transform apply dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype reduce with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `535`

3. Err
   - Expected: "unexpected uint8 prototype reduce dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; Uint8Array.prototype.reduce.call(b, function(acc, v, i, arr) { return acc + v + i + arr.at(i); }, 0)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("535")
    Err(err):
        expect("unexpected uint8 prototype reduce dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype reduceRight with call in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `16511008`

3. Err
   - Expected: "unexpected uint8 prototype reduceRight dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; Uint8Array.prototype.reduceRight.call(b, function(acc, v, i, arr) { return acc * 1000 + v + i + arr.at(i); }, 0)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("16511008")
    Err(err):
        expect("unexpected uint8 prototype reduceRight dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype range helpers with complementary call and apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4,255,7:3:4:255,7,8:3:1,4,255,7,8,9`

3. Err
   - Expected: "unexpected uint8 range complementary dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(6); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; b[4] = 8; b[5] = 9; var sub = Uint8Array.prototype.subarray.apply(b, [-5, -2]); var sl = Uint8Array.prototype.slice.call(b, -4, -1); sub.toString() + ':' + sub.length + ':' + sub.at(0) + ':' + sl.toString() + ':' + sl.length + ':' + b.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4,255,7:3:4:255,7,8:3:1,4,255,7,8,9")
    Err(err):
        expect("unexpected uint8 range complementary dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype set with apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1,2,4,255,8,6:undefined:4,255,8:6`

3. Err
   - Expected: "unexpected uint8 set apply dispatch js error: {err}" equals ``


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
val result = session.eval_script("var dst = new Uint8Array(6); dst[0] = 1; dst[1] = 2; dst[2] = 3; dst[3] = 4; dst[4] = 5; dst[5] = 6; var src = new Uint8Array(3); src[0] = 260; src[1] = -1; src[2] = 8; var returned = Uint8Array.prototype.set.apply(dst, [src, 2]); dst.toString() + ':' + returned + ':' + src.toString() + ':' + dst.length")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1,2,4,255,8,6:undefined:4,255,8:6")
    Err(err):
        expect("unexpected uint8 set apply dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype comparator sort with apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `255,7,4,1:255,7,4,1:255:1`

3. Err
   - Expected: "unexpected uint8 prototype comparator sort apply dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(4); b[0] = 1; b[1] = 260; b[2] = -1; b[3] = 7; var returned = Uint8Array.prototype.sort.apply(b, [function(x, y) { return y - x; }]); returned.toString() + ':' + b.toString() + ':' + returned.at(0) + ':' + returned.at(3)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("255,7,4,1:255,7,4,1:255:1")
    Err(err):
        expect("unexpected uint8 prototype comparator sort apply dispatch js error: {err}").to_equal("")
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

#### dispatches Uint8Array prototype iterators with complementary call and apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `0:1:4:255:0=4:4`

3. Err
   - Expected: "unexpected uint8 iterator complementary dispatch js error: {err}" equals ``


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
val result = session.eval_script("var b = new Uint8Array(3); b[0] = 260; b[1] = -1; b[2] = 7; var keys = Uint8Array.prototype.keys.apply(b, []); var k0 = keys.next(); var k1 = keys.next(); var values = Uint8Array.prototype.values.apply(b, []); var v0 = values.next(); var v1 = values.next(); var entries = Uint8Array.prototype.entries.call(b); var e0 = entries.next(); var sym = Uint8Array.prototype[Symbol.iterator].apply(b, []); var s0 = sym.next(); k0.value + ':' + k1.value + ':' + v0.value + ':' + v1.value + ':' + e0.value[0] + '=' + e0.value[1] + ':' + s0.value")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("0:1:4:255:0=4:4")
    Err(err):
        expect("unexpected uint8 iterator complementary dispatch js error: {err}").to_equal("")
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

#### dispatches ArrayBuffer prototype slice with call and apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `function:4:4,255,7,8:3:255,7,8:4:255,7,8,9:1,4,5,7,8,9`

3. Err
   - Expected: "unexpected arraybuffer prototype slice js error: {err}" equals ``


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
val result = session.eval_script("var buffer = new ArrayBuffer(6); var bytes = new Uint8Array(buffer); bytes[0] = 1; bytes[1] = 260; bytes[2] = -1; bytes[3] = 7; bytes[4] = 8; bytes[5] = 9; var direct = buffer.slice(1, 5); var viaCall = ArrayBuffer.prototype.slice.call(buffer, -4, -1); var viaApply = ArrayBuffer.prototype.slice.apply(buffer, [2]); var directView = new Uint8Array(direct); var callView = new Uint8Array(viaCall); var applyView = new Uint8Array(viaApply); bytes[2] = 5; (typeof ArrayBuffer.prototype.slice) + ':' + direct.byteLength + ':' + directView.toString() + ':' + viaCall.byteLength + ':' + callView.toString() + ':' + viaApply.byteLength + ':' + applyView.toString() + ':' + bytes.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("function:4:4,255,7,8:3:255,7,8:4:255,7,8,9:1,4,5,7,8,9")
    Err(err):
        expect("unexpected arraybuffer prototype slice js error: {err}").to_equal("")
```

</details>

#### dispatches ordinary function call and apply with explicit receivers in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `15:29`

3. Err
   - Expected: "unexpected ordinary function call/apply js error: {err}" equals ``


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
val result = session.eval_script("var add = function(a, b) { return this.base + a + b; }; var callReceiver = []; callReceiver.base = 10; var applyReceiver = []; applyReceiver.base = 20; var applyArgs = [4, 5]; var called = add.call(callReceiver, 2, 3); var applied = add.apply(applyReceiver, applyArgs); called + ':' + applied")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("15:29")
    Err(err):
        expect("unexpected ordinary function call/apply js error: {err}").to_equal("")
```

</details>

#### dispatches ordinary function call and apply with object literal receivers in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `15:29`

3. Err
   - Expected: "unexpected object literal function call/apply js error: {err}" equals ``


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
val result = session.eval_script('var add = function(a, b) { return this.base + a + b; }; var applyArgs = [4, 5]; var called = add.call({ base: 10 }, 2, 3); var applied = add.apply({ base: 20 }, applyArgs); called + ":" + applied')
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("15:29")
    Err(err):
        expect("unexpected object literal function call/apply js error: {err}").to_equal("")
```

</details>

#### dispatches ordinary function bind with receiver and partial arguments in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `19:5,7,9:function`

3. Err
   - Expected: "unexpected ordinary function bind js error: {err}" equals ``


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
val result = session.eval_script('var add = function(a, b, c) { return this.base + a + b + c; }; var bound = add.bind({ base: 10 }, 2); var bytes = new Uint8Array(3); bytes[0] = 1; bytes[1] = 2; bytes[2] = 3; var mapper = function(v, i) { return this.offset + v + i; }.bind({ offset: 4 }); var mapped = bytes.map(mapper); bound(3, 4) + ":" + mapped.toString() + ":" + typeof bound')
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("19:5,7,9:function")
    Err(err):
        expect("unexpected ordinary function bind js error: {err}").to_equal("")
```

</details>

#### dispatches bound function call and apply without replacing the bound receiver

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `19:23:function`

3. Err
   - Expected: "unexpected bound function call/apply js error: {err}" equals ``


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
val result = session.eval_script('var add = function(a, b, c) { return this.base + a + b + c; }; var bound = add.bind({ base: 10 }, 2); var ignored = { base: 99 }; var viaCall = bound.call(ignored, 3, 4); var viaApply = bound.apply(ignored, [5, 6]); viaCall + ":" + viaApply + ":" + typeof bound')
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("19:23:function")
    Err(err):
        expect("unexpected bound function call/apply js error: {err}").to_equal("")
```

</details>

#### dispatches chained function bind with accumulated partial arguments

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `20:21:function`

3. Err
   - Expected: "unexpected chained function bind js error: {err}" equals ``


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
val result = session.eval_script('var add = function(a, b, c, d) { return this.base + a + b + c + d; }; var first = add.bind({ base: 10 }, 1); var second = first.bind({ base: 99 }, 2, 3); var viaDirect = second(4); var viaCall = second.call({ base: 50 }, 5); viaDirect + ":" + viaCall + ":" + typeof second')
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("20:21:function")
    Err(err):
        expect("unexpected chained function bind js error: {err}").to_equal("")
```

</details>

#### dispatches chained function bind with apply arguments

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `25:function`

3. Err
   - Expected: "unexpected chained function bind apply js error: {err}" equals ``


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
val result = session.eval_script('var add = function(a, b, c, d, e) { return this.base + a + b + c + d + e; }; var first = add.bind({ base: 10 }, 1); var second = first.bind({ base: 99 }, 2); var args = [3, 4, 5]; var applied = second.apply({ base: 50 }, args); applied + ":" + typeof second')
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("25:function")
    Err(err):
        expect("unexpected chained function bind apply js error: {err}").to_equal("")
```

</details>

#### binds arguments object through function call apply and bind

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `call:2:1:2:1|apply:2:3:4:3|bound:2:5:6:5|bound:2:5:7:5`

3. Err
   - Expected: "unexpected function arguments binding js error: {err}" equals ``


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
val result = session.eval_script('var inspect = function(a) { return this.base + ":" + arguments.length + ":" + arguments[0] + ":" + arguments[1] + ":" + a; }; var viaCall = inspect.call({ base: "call" }, 1, 2); var viaApply = inspect.apply({ base: "apply" }, [3, 4]); var bound = inspect.bind({ base: "bound" }, 5); var viaBound = bound(6); var viaBoundApply = bound.apply({ base: "ignored" }, [7]); viaCall + "|" + viaApply + "|" + viaBound + "|" + viaBoundApply')
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("call:2:1:2:1|apply:2:3:4:3|bound:2:5:6:5|bound:2:5:7:5")
    Err(err):
        expect("unexpected function arguments binding js error: {err}").to_equal("")
```

</details>

#### dispatches function apply with array-like argument objects

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `plain:3:2:3:4|bound:3:5:6:7`

3. Err
   - Expected: "unexpected function array-like apply js error: {err}" equals ``


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
val result = session.eval_script('var add = function(a, b, c) { return this.base + ":" + arguments.length + ":" + a + ":" + b + ":" + c; }; var args = { 0: 2, 1: 3, 2: 4, length: 3 }; var viaApply = add.apply({ base: "plain" }, args); var bound = add.bind({ base: "bound" }, 5); var viaBoundApply = bound.apply({ base: "ignored" }, { 0: 6, 1: 7, length: 2 }); viaApply + "|" + viaBoundApply')
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("plain:3:2:3:4|bound:3:5:6:7")
    Err(err):
        expect("unexpected function array-like apply js error: {err}").to_equal("")
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

#### dispatches remaining DataView prototype helpers with call and apply in browser scripts

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4:-2:-3:4,254,255,255,255,255,253,0`

3. Err
   - Expected: "unexpected remaining dataview prototype dispatch js error: {err}" equals ``


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
val result = session.eval_script("var buffer = new ArrayBuffer(8); var view = new DataView(buffer); DataView.prototype.setUint8.call(view, 0, 260); DataView.prototype.setInt16.apply(view, [1, -2, true]); DataView.prototype.setInt32.call(view, 3, -3, false); var bytes = new Uint8Array(buffer); DataView.prototype.getUint8.apply(view, [0]) + ':' + DataView.prototype.getInt16.call(view, 1, true) + ':' + DataView.prototype.getInt32.apply(view, [3, false]) + ':' + bytes.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4:-2:-3:4,254,255,255,255,255,253,0")
    Err(err):
        expect("unexpected remaining dataview prototype dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches DataView prototype helpers with complementary call and apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `258:-1:16909060:1,2,255,4,3,2,1`

3. Err
   - Expected: "unexpected dataview complementary dispatch js error: {err}" equals ``


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
val result = session.eval_script("var buffer = new ArrayBuffer(7); var view = new DataView(buffer); DataView.prototype.setUint16.apply(view, [0, 258, false]); DataView.prototype.setInt8.call(view, 2, -1); DataView.prototype.setUint32.apply(view, [3, 16909060, true]); var bytes = new Uint8Array(buffer); DataView.prototype.getUint16.call(view, 0, false) + ':' + DataView.prototype.getInt8.apply(view, [2]) + ':' + DataView.prototype.getUint32.call(view, 3, true) + ':' + bytes.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("258:-1:16909060:1,2,255,4,3,2,1")
    Err(err):
        expect("unexpected dataview complementary dispatch js error: {err}").to_equal("")
```

</details>

#### dispatches remaining DataView prototype helpers with complementary call and apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4:-2:-3:4,254,255,255,255,255,253,0`

3. Err
   - Expected: "unexpected remaining dataview complementary dispatch js error: {err}" equals ``


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
val result = session.eval_script("var buffer = new ArrayBuffer(8); var view = new DataView(buffer); DataView.prototype.setUint8.apply(view, [0, 260]); DataView.prototype.setInt16.call(view, 1, -2, true); DataView.prototype.setInt32.apply(view, [3, -3, false]); var bytes = new Uint8Array(buffer); DataView.prototype.getUint8.call(view, 0) + ':' + DataView.prototype.getInt16.apply(view, [1, true]) + ':' + DataView.prototype.getInt32.call(view, 3, false) + ':' + bytes.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4:-2:-3:4,254,255,255,255,255,253,0")
    Err(err):
        expect("unexpected remaining dataview complementary dispatch js error: {err}").to_equal("")
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

#### dispatches windowed DataView prototype helpers with call and apply

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `2:4:3:258:-1:1,2,3,2,1,255,0,0`

3. Err
   - Expected: "unexpected dataview window prototype js error: {err}" equals ``


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
val result = session.eval_script("var buffer = new ArrayBuffer(8); var bytes = new Uint8Array(buffer); bytes[0] = 1; bytes[1] = 2; bytes[2] = 3; bytes[3] = 4; bytes[4] = 5; var view = new DataView(buffer, 2, 4); DataView.prototype.setUint16.apply(view, [1, 258, true]); DataView.prototype.setInt8.call(view, 3, -1); view.byteOffset + ':' + view.byteLength + ':' + DataView.prototype.getUint8.call(view, 0) + ':' + DataView.prototype.getUint16.apply(view, [1, true]) + ':' + DataView.prototype.getInt8.call(view, 3) + ':' + bytes.toString()")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("2:4:3:258:-1:1,2,3,2,1,255,0,0")
    Err(err):
        expect("unexpected dataview window prototype js error: {err}").to_equal("")
```

</details>

#### encodes browser TextEncoder bytes into WASM validation buffers

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `utf-8:utf-8:3:97,115,109:true:asm`

3. Err
   - Expected: "unexpected text codec wasm header js error: {err}" equals ``


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
val result = session.eval_script("var encoder = new TextEncoder(); var decoder = new TextDecoder('utf8'); var header = new Uint8Array(8); var letters = encoder.encode('asm'); header[0] = 0; Uint8Array.prototype.set.call(header, letters, 1); header[4] = 1; header[5] = 0; header[6] = 0; header[7] = 0; encoder.encoding + ':' + decoder.encoding + ':' + letters.length + ':' + header[1] + ',' + header[2] + ',' + header[3] + ':' + WebAssembly.validate(header) + ':' + decoder.decode(header.slice(1, 4))")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("utf-8:utf-8:3:97,115,109:true:asm")
    Err(err):
        expect("unexpected text codec wasm header js error: {err}").to_equal("")
```

</details>

#### reports partial browser TextEncoder writes before WASM validation

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `3:3:109,111,100:mod:false`

3. Err
   - Expected: "unexpected partial text codec wasm validation js error: {err}" equals ``


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
val result = session.eval_script("var encoder = new TextEncoder(); var decoder = new TextDecoder(); var dst = new Uint8Array(3); var written = encoder.encodeInto('module', dst); written.read + ':' + written.written + ':' + dst.toString() + ':' + decoder.decode(dst) + ':' + WebAssembly.validate(dst)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("3:3:109,111,100:mod:false")
    Err(err):
        expect("unexpected partial text codec wasm validation js error: {err}").to_equal("")
```

</details>

#### replaces invalid browser TextDecoder bytes before WASM validation

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `65533:(:195,40:false`

3. Err
   - Expected: "unexpected invalid text decoder wasm validation js error: {err}" equals ``


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
val result = session.eval_script("var bytes = new Uint8Array(2); bytes[0] = 195; bytes[1] = 40; var text = new TextDecoder().decode(bytes); text.charCodeAt(0) + ':' + text.charAt(1) + ':' + bytes.toString() + ':' + WebAssembly.validate(bytes)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("65533:(:195,40:false")
    Err(err):
        expect("unexpected invalid text decoder wasm validation js error: {err}").to_equal("")
```

</details>

#### replaces truncated browser TextDecoder bytes before WASM validation

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `65533:226,130:false`

3. Err
   - Expected: "unexpected truncated text decoder wasm validation js error: {err}" equals ``


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
val result = session.eval_script("var bytes = new Uint8Array(2); bytes[0] = 226; bytes[1] = 130; var text = new TextDecoder().decode(bytes); text.charCodeAt(0) + ':' + bytes.toString() + ':' + WebAssembly.validate(bytes)")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("65533:226,130:false")
    Err(err):
        expect("unexpected truncated text decoder wasm validation js error: {err}").to_equal("")
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

#### dispatches prototype helpers over WebAssembly Memory buffer views

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `4:255:7:258:2:1:65536`

3. Err
   - Expected: "unexpected wasm memory prototype dispatch js error: {err}" equals ``


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
val result = session.eval_script("var memory = new WebAssembly.Memory({ initial: 1, maximum: 2 }); var bytes = new Uint8Array(memory.buffer); var src = new Uint8Array(3); src[0] = 260; src[1] = -1; src[2] = 7; Uint8Array.prototype.set.apply(bytes, [src, 5]); var view = new DataView(memory.buffer); DataView.prototype.setUint16.call(view, 9, 258, true); bytes[5] + ':' + bytes[6] + ':' + bytes[7] + ':' + DataView.prototype.getUint16.apply(view, [9, true]) + ':' + bytes[9] + ':' + bytes[10] + ':' + memory.buffer.byteLength")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("4:255:7:258:2:1:65536")
    Err(err):
        expect("unexpected wasm memory prototype dispatch js error: {err}").to_equal("")
```

</details>

#### preserves prototype-dispatched WebAssembly Memory bytes after grow

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `1:131072:1,4,255:2,1:131072`

3. Err
   - Expected: "unexpected wasm memory prototype grow js error: {err}" equals ``


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
val result = session.eval_script("var memory = new WebAssembly.Memory({ initial: 1, maximum: 2 }); var before = new Uint8Array(memory.buffer); var src = new Uint8Array(3); src[0] = 1; src[1] = 260; src[2] = -1; Uint8Array.prototype.set.call(before, src, 12); var view = new DataView(memory.buffer); DataView.prototype.setUint16.apply(view, [20, 258, true]); var old = memory.grow(1); var after = new Uint8Array(memory.buffer); old + ':' + memory.buffer.byteLength + ':' + after[12] + ',' + after[13] + ',' + after[14] + ':' + after[20] + ',' + after[21] + ':' + after.length")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("1:131072:1,4,255:2,1:131072")
    Err(err):
        expect("unexpected wasm memory prototype grow js error: {err}").to_equal("")
```

</details>

#### preserves prototype-dispatched WebAssembly Memory bytes after failed grow

1. var session = BrowserSession new

2. Ok
   - Expected: _display_js(value) equals `-1:65536:4,255:2,1:258`

3. Err
   - Expected: "unexpected wasm memory prototype failed grow js error: {err}" equals ``


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
val result = session.eval_script("var memory = new WebAssembly.Memory({ initial: 1, maximum: 1 }); var bytes = new Uint8Array(memory.buffer); var src = new Uint8Array(2); src[0] = 260; src[1] = -1; Uint8Array.prototype.set.apply(bytes, [src, 30]); var view = new DataView(memory.buffer); DataView.prototype.setUint16.call(view, 40, 258, true); var fail = memory.grow(1); var after = new Uint8Array(memory.buffer); fail + ':' + memory.buffer.byteLength + ':' + after[30] + ',' + after[31] + ':' + after[40] + ',' + after[41] + ':' + DataView.prototype.getUint16.apply(new DataView(memory.buffer), [40, true])")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("-1:65536:4,255:2,1:258")
    Err(err):
        expect("unexpected wasm memory prototype failed grow js error: {err}").to_equal("")
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
| Total scenarios | 142 |
| Active scenarios | 142 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
