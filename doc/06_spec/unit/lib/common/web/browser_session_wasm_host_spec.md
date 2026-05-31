# Browser Session Wasm Host Specification

## Scenarios

### WebAssembly native host validation

#### requires WASM magic and version bytes before validation succeeds

1. var interp =  new interpreter
   - Expected: _display_js(interp._native_webassembly_validate([JsValue.String(v: "0061736d01000000")])) equals `true`
   - Expected: _display_js(interp._native_webassembly_validate([JsValue.String(v: "0061736d")])) equals `false`
   - Expected: _display_js(interp._native_webassembly_validate([JsValue.String(v: "0061736d00000000")])) equals `false`
   - Expected: _display_js(interp._native_webassembly_validate([JsValue.String(v: "not-wasm")])) equals `false`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

expect(_display_js(interp._native_webassembly_validate([JsValue.String(v: "0061736d01000000")]))).to_equal("true")
expect(_display_js(interp._native_webassembly_validate([JsValue.String(v: "0061736d")]))).to_equal("false")
expect(_display_js(interp._native_webassembly_validate([JsValue.String(v: "0061736d00000000")]))).to_equal("false")
expect(_display_js(interp._native_webassembly_validate([JsValue.String(v: "not-wasm")]))).to_equal("false")
```

</details>

#### instantiates only validated WASM byte payloads

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, valid, "status") equals `instantiated`
   - Expected: _object_property_text(interp, invalid, "status") equals `invalid`
   - Expected: _object_property_text(interp, invalid, "error") equals `invalid-wasm-header`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val valid = interp._native_webassembly_instantiate(JsValue.Undefined, [JsValue.String(v: "0061736d01000000")])
expect(_object_property_text(interp, valid, "status")).to_equal("instantiated")

val invalid = interp._native_webassembly_instantiate(JsValue.Undefined, [JsValue.String(v: "0061736d00000000")])
expect(_object_property_text(interp, invalid, "status")).to_equal("invalid")
expect(_object_property_text(interp, invalid, "error")).to_equal("invalid-wasm-header")
```

</details>

#### accepts byte-array shaped WASM inputs

1. var interp =  new interpreter

2. interp set object property

3. interp set object property

4. interp set object property

5. interp set object property

6. interp set object property

7. interp set object property

8. interp set object property

9. interp set object property

10. interp set object property

11. interp set object property

12. interp set object property

13. interp set object property

14. interp set object property

15. interp set object property

16. interp set object property

17. interp set object property

18. interp set object property

19. interp set object property
   - Expected: _display_js(interp._native_webassembly_validate([JsValue.Array(id: valid_arr_id)])) equals `true`
   - Expected: _display_js(interp._native_webassembly_validate([JsValue.Array(id: invalid_arr_id)])) equals `false`
   - Expected: _object_property_text(interp, valid, "status") equals `instantiated`
   - Expected: _object_property_text(interp, valid, "module") equals `[object Object]`
   - Expected: _object_property_text(interp, invalid, "status") equals `invalid`


<details>
<summary>Executable SPipe</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()
val valid_arr_id = interp.create_object()
interp.set_object_property(valid_arr_id, "0", JsValue.Number(v: 0.0))
interp.set_object_property(valid_arr_id, "1", JsValue.Number(v: 97.0))
interp.set_object_property(valid_arr_id, "2", JsValue.Number(v: 115.0))
interp.set_object_property(valid_arr_id, "3", JsValue.Number(v: 109.0))
interp.set_object_property(valid_arr_id, "4", JsValue.Number(v: 1.0))
interp.set_object_property(valid_arr_id, "5", JsValue.Number(v: 0.0))
interp.set_object_property(valid_arr_id, "6", JsValue.Number(v: 0.0))
interp.set_object_property(valid_arr_id, "7", JsValue.Number(v: 0.0))
interp.set_object_property(valid_arr_id, "length", JsValue.Number(v: 8.0))
val invalid_arr_id = interp.create_object()
interp.set_object_property(invalid_arr_id, "0", JsValue.Number(v: 0.0))
interp.set_object_property(invalid_arr_id, "1", JsValue.Number(v: 97.0))
interp.set_object_property(invalid_arr_id, "2", JsValue.Number(v: 115.0))
interp.set_object_property(invalid_arr_id, "3", JsValue.Number(v: 109.0))
interp.set_object_property(invalid_arr_id, "4", JsValue.Number(v: 0.0))
interp.set_object_property(invalid_arr_id, "5", JsValue.Number(v: 0.0))
interp.set_object_property(invalid_arr_id, "6", JsValue.Number(v: 0.0))
interp.set_object_property(invalid_arr_id, "7", JsValue.Number(v: 0.0))
interp.set_object_property(invalid_arr_id, "length", JsValue.Number(v: 8.0))

expect(_display_js(interp._native_webassembly_validate([JsValue.Array(id: valid_arr_id)]))).to_equal("true")
expect(_display_js(interp._native_webassembly_validate([JsValue.Array(id: invalid_arr_id)]))).to_equal("false")

val valid = interp._native_webassembly_instantiate(JsValue.Undefined, [JsValue.Array(id: valid_arr_id)])
expect(_object_property_text(interp, valid, "status")).to_equal("instantiated")
expect(_object_property_text(interp, valid, "module")).to_equal("[object Object]")

val invalid = interp._native_webassembly_instantiate(JsValue.Undefined, [JsValue.Array(id: invalid_arr_id)])
expect(_object_property_text(interp, invalid, "status")).to_equal("invalid")
```

</details>

#### accepts Uint8Array-shaped WASM inputs

1. var interp =  new interpreter

2. interp set object property

3. interp set object property

4. interp set object property

5. interp set object property

6. interp set object property

7. interp set object property

8. interp set object property

9. interp set object property

10. interp set object property
   - Expected: _object_property_text(interp, typed, "byteLength") equals `8`
   - Expected: _display_js(interp._native_webassembly_validate([typed])) equals `true`
   - Expected: _object_property_text(interp, buffer, "byteLength") equals `8`
   - Expected: _display_js(interp._native_webassembly_validate([buffer])) equals `false`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()
val bytes_id = interp.create_object()
interp.set_object_property(bytes_id, "0", JsValue.Number(v: 0.0))
interp.set_object_property(bytes_id, "1", JsValue.Number(v: 97.0))
interp.set_object_property(bytes_id, "2", JsValue.Number(v: 115.0))
interp.set_object_property(bytes_id, "3", JsValue.Number(v: 109.0))
interp.set_object_property(bytes_id, "4", JsValue.Number(v: 1.0))
interp.set_object_property(bytes_id, "5", JsValue.Number(v: 0.0))
interp.set_object_property(bytes_id, "6", JsValue.Number(v: 0.0))
interp.set_object_property(bytes_id, "7", JsValue.Number(v: 0.0))
interp.set_object_property(bytes_id, "length", JsValue.Number(v: 8.0))

val typed = interp._native_uint8_array([JsValue.Array(id: bytes_id)])
expect(_object_property_text(interp, typed, "byteLength")).to_equal("8")
expect(_display_js(interp._native_webassembly_validate([typed]))).to_equal("true")

val buffer = interp._native_array_buffer([JsValue.Number(v: 8.0)])
expect(_object_property_text(interp, buffer, "byteLength")).to_equal("8")
expect(_display_js(interp._native_webassembly_validate([buffer]))).to_equal("false")
```

</details>

#### parses bounded WASM section metadata and rejects truncated sections

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, empty, "status") equals `instantiated`
   - Expected: _object_child_property_text(interp, empty, "module", "sectionCount") equals `0`
   - Expected: _object_child_property_text(interp, empty, "module", "hasTypeSection") equals `false`
   - Expected: _object_property_text(interp, with_type, "status") equals `instantiated`
   - Expected: _object_child_property_text(interp, with_type, "module", "sectionCount") equals `1`
   - Expected: _object_child_property_text(interp, with_type, "module", "hasTypeSection") equals `true`
   - Expected: _object_child_property_text(interp, with_type, "module", "hasImportSection") equals `false`
   - Expected: _display_js(interp._native_webassembly_validate([JsValue.String(v: "0061736d010000000105")])) equals `false`
   - Expected: _object_property_text(interp, truncated, "status") equals `invalid`
   - Expected: _object_property_text(interp, truncated, "error") equals `invalid-wasm-section`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val empty = interp._native_webassembly_instantiate(JsValue.Undefined, [JsValue.String(v: "0061736d01000000")])
expect(_object_property_text(interp, empty, "status")).to_equal("instantiated")
expect(_object_child_property_text(interp, empty, "module", "sectionCount")).to_equal("0")
expect(_object_child_property_text(interp, empty, "module", "hasTypeSection")).to_equal("false")

val with_type = interp._native_webassembly_instantiate(JsValue.Undefined, [JsValue.String(v: "0061736d01000000010100")])
expect(_object_property_text(interp, with_type, "status")).to_equal("instantiated")
expect(_object_child_property_text(interp, with_type, "module", "sectionCount")).to_equal("1")
expect(_object_child_property_text(interp, with_type, "module", "hasTypeSection")).to_equal("true")
expect(_object_child_property_text(interp, with_type, "module", "hasImportSection")).to_equal("false")

val truncated = interp._native_webassembly_instantiate(JsValue.Undefined, [JsValue.String(v: "0061736d010000000105")])
expect(_display_js(interp._native_webassembly_validate([JsValue.String(v: "0061736d010000000105")]))).to_equal("false")
expect(_object_property_text(interp, truncated, "status")).to_equal("invalid")
expect(_object_property_text(interp, truncated, "error")).to_equal("invalid-wasm-section")
```

</details>

#### exposes bounded Module and Instance constructor shapes

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, module, "validated") equals `true`
   - Expected: _object_property_text(interp, module, "sectionCount") equals `1`
   - Expected: _object_property_text(interp, module, "hasTypeSection") equals `true`
   - Expected: _object_property_text(interp, instance, "status") equals `instantiated`
   - Expected: _object_property_text(interp, instance, "moduleValid") equals `true`
   - Expected: _object_property_text(interp, instance, "exports") equals `[object Object]`
   - Expected: _object_property_text(interp, invalid_module, "validated") equals `false`
   - Expected: _object_property_text(interp, invalid_module, "error") equals `invalid-wasm-section`
   - Expected: _object_property_text(interp, invalid_instance, "status") equals `invalid`
   - Expected: _object_property_text(interp, invalid_instance, "error") equals `invalid-wasm-module`


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val module = interp._native_webassembly_module([JsValue.String(v: "0061736d01000000010100")])
expect(_object_property_text(interp, module, "validated")).to_equal("true")
expect(_object_property_text(interp, module, "sectionCount")).to_equal("1")
expect(_object_property_text(interp, module, "hasTypeSection")).to_equal("true")

val instance = interp._native_webassembly_instance([module])
expect(_object_property_text(interp, instance, "status")).to_equal("instantiated")
expect(_object_property_text(interp, instance, "moduleValid")).to_equal("true")
expect(_object_property_text(interp, instance, "exports")).to_equal("[object Object]")

val invalid_module = interp._native_webassembly_module([JsValue.String(v: "0061736d010000000105")])
val invalid_instance = interp._native_webassembly_instance([invalid_module])
expect(_object_property_text(interp, invalid_module, "validated")).to_equal("false")
expect(_object_property_text(interp, invalid_module, "error")).to_equal("invalid-wasm-section")
expect(_object_property_text(interp, invalid_instance, "status")).to_equal("invalid")
expect(_object_property_text(interp, invalid_instance, "error")).to_equal("invalid-wasm-module")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/web/browser_session_wasm_host_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebAssembly native host validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

