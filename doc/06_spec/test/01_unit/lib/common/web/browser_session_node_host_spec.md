# Browser Session Node Host Specification

> 1. var interp =  new interpreter

<!-- sdn-diagram:id=browser_session_node_host_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_node_host_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_node_host_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_node_host_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Node Host Specification

## Scenarios

### BrowserSession deterministic Node host surface

#### builds deterministic process and Buffer globals without host state

1. var interp =  new interpreter
   - Expected: _display_js(process_platform([])) equals `linux`
   - Expected: _display_js(os_platform([])) equals `linux`
   - Expected: _display_js(process_versions_node([])) equals `0.0.0-simple`
   - Expected: _display_js(process_env_get([JsValue.String(v: "PATH")])) equals `undefined`
   - Expected: _display_js(interp._native_node_buffer_global()) equals `[object Object]`
   - Expected: _display_js(interp._native_node_require_function()) equals `[Function]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

expect(_display_js(process_platform([]))).to_equal("linux")
expect(_display_js(os_platform([]))).to_equal("linux")
expect(_display_js(process_versions_node([]))).to_equal("0.0.0-simple")
expect(_display_js(process_env_get([JsValue.String(v: "PATH")]))).to_equal("undefined")
expect(_display_js(interp._native_node_buffer_global())).to_equal("[object Object]")
expect(_display_js(interp._native_node_require_function())).to_equal("[Function]")
```

</details>

#### loads deterministic path and Buffer modules through require dispatch

1. var interp =  new interpreter
   - Expected: _display_js(interp._dispatch_native_with_receiver(-106, JsValue.Undefined, [JsValue.String(v: "/usr"), JsValue.String(v: "local"), JsValue.String(v: ".."), JsValue.String(v: "bin")], 0)) equals `/usr/bin`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-102, JsValue.Undefined, [JsValue.String(v: "/tmp/demo.txt")], 0)) equals `demo.txt`
   - Expected: _object_property_text(interp, path, "join") equals `[Function]`
   - Expected: _object_property_text(interp, buffer_module, "Buffer") equals `[object Object]`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-110, JsValue.Undefined, [JsValue.String(v: "68656c6c6f"), JsValue.String(v: "hex")], 0)) equals `5`
2. JsValue Object
3. JsValue Object
   - Expected: _display_js(interp.get_object_property(buffer_id, "concat")) equals `[Function]`
   - Expected: _display_js(interp._native_node_buffer_to_string(buffer, [JsValue.String(v: "hex")])) equals `68656c6c6f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val path = interp._native_node_require([JsValue.String(v: "node:path")])
expect(_display_js(interp._dispatch_native_with_receiver(-106, JsValue.Undefined, [JsValue.String(v: "/usr"), JsValue.String(v: "local"), JsValue.String(v: ".."), JsValue.String(v: "bin")], 0))).to_equal("/usr/bin")
expect(_display_js(interp._dispatch_native_with_receiver(-102, JsValue.Undefined, [JsValue.String(v: "/tmp/demo.txt")], 0))).to_equal("demo.txt")
expect(_object_property_text(interp, path, "join")).to_equal("[Function]")

val buffer_module = interp._native_node_require([JsValue.String(v: "buffer")])
expect(_object_property_text(interp, buffer_module, "Buffer")).to_equal("[object Object]")
expect(_display_js(interp._dispatch_native_with_receiver(-110, JsValue.Undefined, [JsValue.String(v: "68656c6c6f"), JsValue.String(v: "hex")], 0))).to_equal("5")
match buffer_module:
    JsValue.Object(module_id):
        match interp.get_object_property(module_id, "Buffer"):
            JsValue.Object(buffer_id):
                expect(_display_js(interp.get_object_property(buffer_id, "concat"))).to_equal("[Function]")
            _: expect("missing Buffer").to_equal("object")
    _: expect("missing buffer module").to_equal("object")
val buffer = interp._native_node_buffer_from([JsValue.String(v: "hello"), JsValue.String(v: "utf8")])
expect(_display_js(interp._native_node_buffer_to_string(buffer, [JsValue.String(v: "hex")]))).to_equal("68656c6c6f")
```

</details>

#### loads deterministic os modules through require dispatch

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, os, "platform") equals `[Function]`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-132, JsValue.Undefined, [], 0)) equals `linux`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-133, JsValue.Undefined, [], 0)) equals `x64`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-134, JsValue.Undefined, [], 0)) equals `Linux`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-135, JsValue.Undefined, [], 0)) equals `0.0.0-simple`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-136, JsValue.Undefined, [], 0)) equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val os = interp._native_node_require([JsValue.String(v: "node:os")])
expect(_object_property_text(interp, os, "platform")).to_equal("[Function]")
expect(_display_js(interp._dispatch_native_with_receiver(-132, JsValue.Undefined, [], 0))).to_equal("linux")
expect(_display_js(interp._dispatch_native_with_receiver(-133, JsValue.Undefined, [], 0))).to_equal("x64")
expect(_display_js(interp._dispatch_native_with_receiver(-134, JsValue.Undefined, [], 0))).to_equal("Linux")
expect(_display_js(interp._dispatch_native_with_receiver(-135, JsValue.Undefined, [], 0))).to_equal("0.0.0-simple")
expect(_display_js(interp._dispatch_native_with_receiver(-136, JsValue.Undefined, [], 0))).to_equal("/")
```

</details>

#### denies host filesystem module access through require

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, fs, "readFileSync") equals `[Function]`
   - Expected: _object_property_text(interp, fs, "writeFileSync") equals `[Function]`
2. JsValue Object
   - Expected: _object_property_text(interp, denied, "status") equals `denied`
   - Expected: _object_property_text(interp, denied, "error") equals `file-denied`
   - Expected: "missing fs module" equals `object`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val fs = interp._native_node_require([JsValue.String(v: "fs")])
expect(_object_property_text(interp, fs, "readFileSync")).to_equal("[Function]")
expect(_object_property_text(interp, fs, "writeFileSync")).to_equal("[Function]")
match fs:
    JsValue.Object(fs_id):
        val denied = interp._dispatch_native_with_receiver(-151, JsValue.Object(id: fs_id), [JsValue.String(v: "/etc/passwd")], 0)
        expect(_object_property_text(interp, denied, "status")).to_equal("denied")
        expect(_object_property_text(interp, denied, "error")).to_equal("file-denied")
    _:
        expect("missing fs module").to_equal("object")
```

</details>

#### installs deterministic process argv on BrowserSession runtime globals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = BrowserRuntimeState.create("https://example.test/", "T", "", [], [], "")
val process = state.runtime.get_host_property(state.window_id, "process")
expect(_object_child_property_text(state.runtime.interpreter, process, "argv", "length")).to_equal("2")
expect(_object_child_property_text(state.runtime.interpreter, process, "argv", "0")).to_equal("simple")
expect(_object_property_text(state.runtime.interpreter, process, "exit")).to_equal("[Function]")
expect(_display_js(state.runtime.interpreter._dispatch_native_with_receiver(NATIVE_NODE_PROCESS_EXIT, JsValue.Undefined, [JsValue.Number(v: 7.0)], 0))).to_equal("7")
```

</details>

#### executes embedded process exit intent in BrowserSession runtime scripts

1. var state = BrowserRuntimeState create
2. Ok
   - Expected: _display_js(value) equals `7`
3. Err
   - Expected: err.message equals `ok`
4. Ok
   - Expected: _display_js(value) equals `7`
5. Err
   - Expected: err.message equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = BrowserRuntimeState.create("about:node-process", "Node", "", [], [], "")

match state.runtime.eval("process.exit(7)"):
    Ok(value):
        expect(_display_js(value)).to_equal("7")
    Err(err):
        expect(err.message).to_equal("ok")
match state.runtime.eval("require('process').exit(7)"):
    Ok(value):
        expect(_display_js(value)).to_equal("7")
    Err(err):
        expect(err.message).to_equal("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_node_host_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession deterministic Node host surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
