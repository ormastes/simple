# Browser Session Node Host Specification

> Tests covering BrowserSession deterministic Node host surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Node Host Specification

## Scenarios

### BrowserSession deterministic Node host surface

#### builds deterministic process and Buffer globals without host state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds deterministic process and Buffer globals without host state
   - Expected: _display_js(process_platform([])) equals `linux`
   - Expected: _display_js(os_platform([])) equals `linux`
   - Expected: _display_js(process_versions_node([])) equals `0.0.0-simple`
   - Expected: _display_js(process_env_get([JsValue.String(v: "PATH")])) equals `undefined`
   - Expected: _display_js(interp._native_node_buffer_global()) equals `[object Object]`
   - Expected: _display_js(interp._native_node_require_function()) equals `[Function]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds deterministic process and Buffer globals without host state")
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

- loads deterministic path and Buffer modules through require dispatch
   - Expected: _display_js(interp._dispatch_native_with_receiver(-106, JsValue.Undefined, [JsValue.String(v: "/usr"), JsValue.String(v: "local"), JsValue.String(v: ".."), JsValue.String(v: "bin")], 0)) equals `/usr/bin`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-102, JsValue.Undefined, [JsValue.String(v: "/tmp/demo.txt")], 0)) equals `demo.txt`
   - Expected: _object_property_text(interp, path, "join") equals `[Function]`
   - Expected: _object_property_text(interp, buffer_module, "Buffer") equals `[object Object]`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-110, JsValue.Undefined, [JsValue.String(v: "68656c6c6f"), JsValue.String(v: "hex")], 0)) equals `5`
   - Expected: _display_js(interp.get_object_property(buffer_id, "concat")) equals `[Function]`
   - Expected: _display_js(interp._native_node_buffer_to_string(buffer, [JsValue.String(v: "hex")])) equals `68656c6c6f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads deterministic path and Buffer modules through require dispatch")
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

- loads deterministic os modules through require dispatch
   - Expected: _object_property_text(interp, os, "platform") equals `[Function]`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-132, JsValue.Undefined, [], 0)) equals `linux`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-133, JsValue.Undefined, [], 0)) equals `x64`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-134, JsValue.Undefined, [], 0)) equals `Linux`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-135, JsValue.Undefined, [], 0)) equals `0.0.0-simple`
   - Expected: _display_js(interp._dispatch_native_with_receiver(-136, JsValue.Undefined, [], 0)) equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads deterministic os modules through require dispatch")
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

- denies host filesystem module access through require
   - Expected: _object_property_text(interp, fs, "readFileSync") equals `[Function]`
   - Expected: _object_property_text(interp, fs, "writeFileSync") equals `[Function]`
   - Expected: _object_property_text(interp, denied, "status") equals `denied`
   - Expected: _object_property_text(interp, denied, "error") equals `file-denied`
   - Expected: "missing fs module" equals `object`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies host filesystem module access through require")
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

#### does not install Node globals on BrowserSession page runtimes

- does not install Node globals on BrowserSession page runtimes
   - Expected: _display_js(state.runtime.get_host_property(state.window_id, "require")) equals `undefined`
   - Expected: _display_js(state.runtime.get_host_property(state.window_id, "process")) equals `undefined`
   - Expected: _display_js(state.runtime.get_host_property(state.window_id, "Buffer")) equals `undefined`
   - Expected: _display_js(value) equals `undefined:undefined:undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not install Node globals on BrowserSession page runtimes")
val state = BrowserRuntimeState.create("https://example.test/", "T", "", [], [], "")
expect(_display_js(state.runtime.get_host_property(state.window_id, "require"))).to_equal("undefined")
expect(_display_js(state.runtime.get_host_property(state.window_id, "process"))).to_equal("undefined")
expect(_display_js(state.runtime.get_host_property(state.window_id, "Buffer"))).to_equal("undefined")
var runtime = state.runtime
match runtime.eval("typeof require + ':' + typeof process + ':' + typeof Buffer"):
    Ok(value):
        expect(_display_js(value)).to_equal("undefined:undefined:undefined")
    Err(e):
        fail("Expected browser Node globals to be absent: {e.message}")
```

</details>

#### keeps Node support available only through explicit JS engine APIs

- keeps Node support available only through explicit JS engine APIs
   - Expected: _display_js(interp._native_node_require_function()) equals `[Function]`
   - Expected: _object_property_text(interp, process, "exit") equals `[Function]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Node support available only through explicit JS engine APIs")
var interp = _new_interpreter()
expect(_display_js(interp._native_node_require_function())).to_equal("[Function]")
val process = interp._native_node_require([JsValue.String(v: "process")])
expect(_object_property_text(interp, process, "exit")).to_equal("[Function]")
```

</details>

#### denies direct Node host syntax in browser mode

- denies direct Node host syntax in browser mode
   - Expected: _browser_eval_is_error("process.cwd()") is true
   - Expected: _browser_eval_is_error("process.env.PATH") is true
   - Expected: _browser_eval_is_error("process.argv[0]") is true
   - Expected: _browser_eval_is_error("process.versions.node") is true
   - Expected: _browser_eval_is_error("globalThis.Buffer.byteLength('secret')") is true
   - Expected: _browser_eval_is_error("require('fs').readFileSync('/etc/passwd')") is true
   - Expected: _browser_eval_is_error("process.send('secret')") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies direct Node host syntax in browser mode")
expect(_browser_eval_is_error("process.cwd()")).to_equal(true)
expect(_browser_eval_is_error("process.env.PATH")).to_equal(true)
expect(_browser_eval_is_error("process.argv[0]")).to_equal(true)
expect(_browser_eval_is_error("process.versions.node")).to_equal(true)
expect(_browser_eval_is_error("globalThis.Buffer.byteLength('secret')")).to_equal(true)
expect(_browser_eval_is_error("require('fs').readFileSync('/etc/passwd')")).to_equal(true)
expect(_browser_eval_is_error("process.send('secret')")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_node_host_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession deterministic Node host surface.
- BrowserSession deterministic Node host surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bce247ce085d757e69f037031b126844e053a21a6153c6b967bad059949dd14c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bce247ce085d757e69f037031b126844e053a21a6153c6b967bad059949dd14c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bce247ce085d757e69f037031b126844e053a21a6153c6b967bad059949dd14c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/web/browser_session_node_host_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_node_host_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_node_host_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_node_host_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_node_host_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds deterministic process and Buffer globals without host state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_node_host_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads deterministic path and Buffer modules through require dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_node_host_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads deterministic os modules through require dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
