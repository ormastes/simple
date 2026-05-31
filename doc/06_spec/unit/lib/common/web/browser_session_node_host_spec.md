# Browser Session Node Host Specification

## Scenarios

### BrowserSession deterministic Node host surface

#### builds deterministic process and Buffer globals without host state

1. var interp =  new interpreter
   - Expected: _display_js(process_platform([])) equals `linux`
   - Expected: _display_js(process_versions_node([])) equals `0.0.0-simple`
   - Expected: _display_js(process_env_get([JsValue.String(v: "PATH")])) equals `undefined`
   - Expected: _display_js(interp._native_node_buffer_global()) equals `[object Object]`
   - Expected: _display_js(interp._native_node_require_function()) equals `[Function]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

expect(_display_js(process_platform([]))).to_equal("linux")
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

4.  : expect

5.  : expect
   - Expected: _display_js(interp._native_node_buffer_to_string(buffer, [JsValue.String(v: "hex")])) equals `68656c6c6f`


<details>
<summary>Executable SPipe</summary>

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

#### denies host filesystem module access through require

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, fs, "status") equals `denied`
   - Expected: _object_property_text(interp, fs, "error") equals `module-denied`
   - Expected: _object_property_text(interp, fs, "specifier") equals `fs`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val fs = interp._native_node_require([JsValue.String(v: "fs")])
expect(_object_property_text(interp, fs, "status")).to_equal("denied")
expect(_object_property_text(interp, fs, "error")).to_equal("module-denied")
expect(_object_property_text(interp, fs, "specifier")).to_equal("fs")
```

</details>

#### installs deterministic process argv on BrowserSession runtime globals

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = BrowserRuntimeState.create("https://example.test/", "T", "", [], [], "")
val process = state.runtime.get_host_property(state.window_id, "process")
expect(_object_child_property_text(state.runtime.interpreter, process, "argv", "length")).to_equal("2")
expect(_object_child_property_text(state.runtime.interpreter, process, "argv", "0")).to_equal("simple")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/web/browser_session_node_host_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession deterministic Node host surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

