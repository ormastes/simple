# Browser Session Large Arraybuffer Specification

> <details>

<!-- sdn-diagram:id=browser_session_large_arraybuffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_large_arraybuffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_large_arraybuffer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_large_arraybuffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Large Arraybuffer Specification

## Scenarios

### BrowserSession large ArrayBuffer runtime

#### constructs large ArrayBuffer and Uint8Array views lazily

- Create a large ArrayBuffer without materializing every zero byte
- var interp =  new interpreter
- JsValue Object
   - Expected: _object_property_text(interp, buffer, "byteLength") equals `4096`
   - Expected: _display_js(interp.get_object_property(buffer_id, "0")) equals `0`
   - Expected: _display_js(interp.get_object_property(buffer_id, "4095")) equals `0`
- Create a Uint8Array view without copying zero bytes
- JsValue Object
   - Expected: _object_property_text(interp, view, "length") equals `4096`
   - Expected: _display_js(interp.get_object_property(view_id, "2048")) equals `0`
- Write one view byte and observe the normalized backing buffer byte
- interp set object property
   - Expected: _display_js(interp.get_object_property(view_id, "2048")) equals `4`
   - Expected: _display_js(interp.get_object_property(buffer_id, "2048")) equals `4`
   - Expected: "missing view" equals ``
   - Expected: "missing buffer" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a large ArrayBuffer without materializing every zero byte")
var interp = _new_interpreter()
val base_props = interp.object_store.prop_keys.len()
val buffer = interp._native_array_buffer([JsValue.Number(v: 4096.0)])
match buffer:
    JsValue.Object(buffer_id):
        val buffer_props = interp.object_store.prop_keys.len()
        expect(buffer_props - base_props).to_be_less_than(8)
        expect(_object_property_text(interp, buffer, "byteLength")).to_equal("4096")
        expect(_display_js(interp.get_object_property(buffer_id, "0"))).to_equal("0")
        expect(_display_js(interp.get_object_property(buffer_id, "4095"))).to_equal("0")

        step("Create a Uint8Array view without copying zero bytes")
        val view = interp._native_uint8_array([buffer])
        match view:
            JsValue.Object(view_id):
                val view_props = interp.object_store.prop_keys.len()
                expect(view_props - buffer_props).to_be_less_than(40)
                expect(_object_property_text(interp, view, "length")).to_equal("4096")
                expect(_display_js(interp.get_object_property(view_id, "2048"))).to_equal("0")

                step("Write one view byte and observe the normalized backing buffer byte")
                interp.set_object_property(view_id, "2048", JsValue.Number(v: 260.0))
                expect(_display_js(interp.get_object_property(view_id, "2048"))).to_equal("4")
                expect(_display_js(interp.get_object_property(buffer_id, "2048"))).to_equal("4")
            _:
                expect("missing view").to_equal("")
    _:
        expect("missing buffer").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession large ArrayBuffer runtime

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
