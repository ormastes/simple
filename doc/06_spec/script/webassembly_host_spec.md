# Webassembly Host Specification

## Scenarios

### browser JavaScript WebAssembly host

#### exposes WebAssembly beside secure WebGPU globals

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `object:function:function:available:bgra8unorm`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
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

#### validates versioned WASM inputs and rejects truncated headers

1. var session = BrowserSession new

2. session open html

3. Ok
   - Expected: _display_js(value) equals `true:false:instantiated:invalid`

4. Err
   - Expected: "unexpected js error: {err}" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/webgpu-wasm.html", "<html><body>WASM GPU</body></html>")

val result = session.eval_script("WebAssembly.validate('0061736d01000000') + ':' + WebAssembly.validate('0061736d') + ':' + WebAssembly.instantiate('0061736d01000000').status + ':' + WebAssembly.instantiate('0061736d').status")
match result:
    Ok(value):
        expect(_display_js(value)).to_equal("true:false:instantiated:invalid")
    Err(err):
        expect("unexpected js error: {err}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `examples/11_advanced/browser/test/script/webassembly_host_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser JavaScript WebAssembly host

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

