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

#### round trips TextEncoder bytes through TextDecoder for WASM-oriented host arrays

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, encoded, "length") equals `4`
   - Expected: _object_property_text(interp, encoded, "0") equals `119`
   - Expected: _object_property_text(interp, encoded, "3") equals `109`
   - Expected: _object_property_text(interp, decoder, "encoding") equals `utf-8`
   - Expected: _display_js(interp._native_text_decoder_decode(decoder, [encoded])) equals `wasm`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()
val encoder = interp._native_text_encoder([])
val encoded = interp._native_text_encoder_encode(encoder, [JsValue.String(v: "wasm")])
expect(_object_property_text(interp, encoded, "length")).to_equal("4")
expect(_object_property_text(interp, encoded, "0")).to_equal("119")
expect(_object_property_text(interp, encoded, "3")).to_equal("109")

val decoder = interp._native_text_decoder([JsValue.String(v: "utf8")])
expect(_object_property_text(interp, decoder, "encoding")).to_equal("utf-8")
expect(_display_js(interp._native_text_decoder_decode(decoder, [encoded]))).to_equal("wasm")
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

#### exposes bounded memory export metadata and instance memory shape

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, module, "validated") equals `true`
   - Expected: _object_property_text(interp, module, "hasMemorySection") equals `true`
   - Expected: _object_property_text(interp, module, "hasExportSection") equals `true`
   - Expected: _object_property_text(interp, module, "memoryMinPages") equals `1`
   - Expected: _object_property_text(interp, module, "exportCount") equals `1`
   - Expected: _object_property_text(interp, module, "firstExportName") equals `memory`
   - Expected: _object_property_text(interp, module, "firstExportKind") equals `memory`
   - Expected: _object_child_property_text(interp, instance, "exports", "memory") equals `[object Object]`

2. JsValue Object

3. JsValue Object

4. JsValue Object
   - Expected: _display_js(interp.get_object_property(memory_id, "byteLength")) equals `65536`
   - Expected: _display_js(interp.get_object_property(memory_id, "pageSize")) equals `65536`
   - Expected: "missing memory" equals ``
   - Expected: "missing exports" equals ``
   - Expected: "missing instance" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val module = interp._native_webassembly_module([JsValue.String(v: "0061736d010000000503010001070a01066d656d6f72790200")])
expect(_object_property_text(interp, module, "validated")).to_equal("true")
expect(_object_property_text(interp, module, "hasMemorySection")).to_equal("true")
expect(_object_property_text(interp, module, "hasExportSection")).to_equal("true")
expect(_object_property_text(interp, module, "memoryMinPages")).to_equal("1")
expect(_object_property_text(interp, module, "exportCount")).to_equal("1")
expect(_object_property_text(interp, module, "firstExportName")).to_equal("memory")
expect(_object_property_text(interp, module, "firstExportKind")).to_equal("memory")

val instance = interp._native_webassembly_instance([module])
expect(_object_child_property_text(interp, instance, "exports", "memory")).to_equal("[object Object]")
match instance:
    JsValue.Object(instance_id):
        match interp.get_object_property(instance_id, "exports"):
            JsValue.Object(exports_id):
                match interp.get_object_property(exports_id, "memory"):
                    JsValue.Object(memory_id):
                        expect(_display_js(interp.get_object_property(memory_id, "byteLength"))).to_equal("65536")
                        expect(_display_js(interp.get_object_property(memory_id, "pageSize"))).to_equal("65536")
                    _:
                        expect("missing memory").to_equal("")
            _:
                expect("missing exports").to_equal("")
    _:
        expect("missing instance").to_equal("")
```

</details>

#### exposes bounded function export metadata and callable export shape

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, module, "validated") equals `true`
   - Expected: _object_property_text(interp, module, "hasTypeSection") equals `true`
   - Expected: _object_property_text(interp, module, "hasExportSection") equals `true`
   - Expected: _object_property_text(interp, module, "exportCount") equals `1`
   - Expected: _object_property_text(interp, module, "firstExportName") equals `run`
   - Expected: _object_property_text(interp, module, "firstExportKind") equals `function`
   - Expected: _object_property_text(interp, module, "functionExportName") equals `run`
   - Expected: _object_property_text(interp, module, "functionExportCount") equals `1`
   - Expected: _object_property_text(interp, module, "functionExportName0") equals `run`

2. JsValue Object

3. JsValue Object
   - Expected: _display_js(run_value) equals `[Function]`
   - Expected: _display_js(interp._native_webassembly_export_function(run_value, [])) equals `undefined`
   - Expected: "missing exports" equals ``
   - Expected: "missing instance" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val module = interp._native_webassembly_module([JsValue.String(v: "0061736d01000000010401600000030201000707010372756e00000a040102000b")])
expect(_object_property_text(interp, module, "validated")).to_equal("true")
expect(_object_property_text(interp, module, "hasTypeSection")).to_equal("true")
expect(_object_property_text(interp, module, "hasExportSection")).to_equal("true")
expect(_object_property_text(interp, module, "exportCount")).to_equal("1")
expect(_object_property_text(interp, module, "firstExportName")).to_equal("run")
expect(_object_property_text(interp, module, "firstExportKind")).to_equal("function")
expect(_object_property_text(interp, module, "functionExportName")).to_equal("run")
expect(_object_property_text(interp, module, "functionExportCount")).to_equal("1")
expect(_object_property_text(interp, module, "functionExportName0")).to_equal("run")

val instance = interp._native_webassembly_instance([module])
match instance:
    JsValue.Object(instance_id):
        match interp.get_object_property(instance_id, "exports"):
            JsValue.Object(exports_id):
                val run_value = interp.get_object_property(exports_id, "run")
                expect(_display_js(run_value)).to_equal("[Function]")
                expect(_display_js(interp._native_webassembly_export_function(run_value, []))).to_equal("undefined")
            _:
                expect("missing exports").to_equal("")
    _:
        expect("missing instance").to_equal("")
```

</details>

#### synthesizes all bounded function exports on an instance

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, module, "validated") equals `true`
   - Expected: _object_property_text(interp, module, "exportCount") equals `2`
   - Expected: _object_property_text(interp, module, "functionExportCount") equals `2`
   - Expected: _object_property_text(interp, module, "functionExportName0") equals `init`
   - Expected: _object_property_text(interp, module, "functionExportName1") equals `render`

2. JsValue Object

3. JsValue Object
   - Expected: _display_js(init_value) equals `[Function]`
   - Expected: _display_js(render_value) equals `[Function]`
   - Expected: _display_js(interp._native_webassembly_export_function(init_value, [])) equals `undefined`
   - Expected: _display_js(interp._native_webassembly_export_function(render_value, [])) equals `undefined`
   - Expected: "missing exports" equals ``
   - Expected: "missing instance" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val module = interp._native_webassembly_module([JsValue.String(v: "0061736d01000000010401600000030302000007110204696e697400000672656e64657200010a070202000b02000b")])
expect(_object_property_text(interp, module, "validated")).to_equal("true")
expect(_object_property_text(interp, module, "exportCount")).to_equal("2")
expect(_object_property_text(interp, module, "functionExportCount")).to_equal("2")
expect(_object_property_text(interp, module, "functionExportName0")).to_equal("init")
expect(_object_property_text(interp, module, "functionExportName1")).to_equal("render")

val instance = interp._native_webassembly_instance([module])
match instance:
    JsValue.Object(instance_id):
        match interp.get_object_property(instance_id, "exports"):
            JsValue.Object(exports_id):
                val init_value = interp.get_object_property(exports_id, "init")
                val render_value = interp.get_object_property(exports_id, "render")
                expect(_display_js(init_value)).to_equal("[Function]")
                expect(_display_js(render_value)).to_equal("[Function]")
                expect(_display_js(interp._native_webassembly_export_function(init_value, []))).to_equal("undefined")
                expect(_display_js(interp._native_webassembly_export_function(render_value, []))).to_equal("undefined")
            _:
                expect("missing exports").to_equal("")
    _:
        expect("missing instance").to_equal("")
```

</details>

#### synthesizes bounded table and global export placeholders

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, module, "validated") equals `true`
   - Expected: _object_property_text(interp, module, "hasTableSection") equals `true`
   - Expected: _object_property_text(interp, module, "hasGlobalSection") equals `true`
   - Expected: _object_property_text(interp, module, "exportCount") equals `2`
   - Expected: _object_property_text(interp, module, "firstExportName") equals `tbl`
   - Expected: _object_property_text(interp, module, "firstExportKind") equals `table`
   - Expected: _object_property_text(interp, module, "tableExportName") equals `tbl`
   - Expected: _object_property_text(interp, module, "tableExportCount") equals `1`
   - Expected: _object_property_text(interp, module, "tableMinElements") equals `1`
   - Expected: _object_property_text(interp, module, "globalExportName") equals `answer`
   - Expected: _object_property_text(interp, module, "globalExportCount") equals `1`
   - Expected: _object_property_text(interp, module, "globalValue") equals `42`
   - Expected: _object_child_property_text(interp, instance, "exports", "tbl") equals `[object Object]`
   - Expected: _object_child_property_text(interp, instance, "exports", "answer") equals `[object Object]`

2. JsValue Object

3. JsValue Object

4. JsValue Object
   - Expected: _display_js(interp.get_object_property(table_id, "kind")) equals `table`
   - Expected: _display_js(interp.get_object_property(table_id, "length")) equals `1`
   - Expected: "missing table" equals ``

5. JsValue Object
   - Expected: _display_js(interp.get_object_property(global_id, "kind")) equals `global`
   - Expected: _display_js(interp.get_object_property(global_id, "value")) equals `42`
   - Expected: "missing global" equals ``
   - Expected: "missing exports" equals ``
   - Expected: "missing instance" equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val module = interp._native_webassembly_module([JsValue.String(v: "0061736d010000000404017000010606017f00412a0b0710020374626c010006616e737765720300")])
expect(_object_property_text(interp, module, "validated")).to_equal("true")
expect(_object_property_text(interp, module, "hasTableSection")).to_equal("true")
expect(_object_property_text(interp, module, "hasGlobalSection")).to_equal("true")
expect(_object_property_text(interp, module, "exportCount")).to_equal("2")
expect(_object_property_text(interp, module, "firstExportName")).to_equal("tbl")
expect(_object_property_text(interp, module, "firstExportKind")).to_equal("table")
expect(_object_property_text(interp, module, "tableExportName")).to_equal("tbl")
expect(_object_property_text(interp, module, "tableExportCount")).to_equal("1")
expect(_object_property_text(interp, module, "tableMinElements")).to_equal("1")
expect(_object_property_text(interp, module, "globalExportName")).to_equal("answer")
expect(_object_property_text(interp, module, "globalExportCount")).to_equal("1")
expect(_object_property_text(interp, module, "globalValue")).to_equal("42")

val instance = interp._native_webassembly_instance([module])
expect(_object_child_property_text(interp, instance, "exports", "tbl")).to_equal("[object Object]")
expect(_object_child_property_text(interp, instance, "exports", "answer")).to_equal("[object Object]")
match instance:
    JsValue.Object(instance_id):
        match interp.get_object_property(instance_id, "exports"):
            JsValue.Object(exports_id):
                match interp.get_object_property(exports_id, "tbl"):
                    JsValue.Object(table_id):
                        expect(_display_js(interp.get_object_property(table_id, "kind"))).to_equal("table")
                        expect(_display_js(interp.get_object_property(table_id, "length"))).to_equal("1")
                    _:
                        expect("missing table").to_equal("")
                match interp.get_object_property(exports_id, "answer"):
                    JsValue.Object(global_id):
                        expect(_display_js(interp.get_object_property(global_id, "kind"))).to_equal("global")
                        expect(_display_js(interp.get_object_property(global_id, "value"))).to_equal("42")
                    _:
                        expect("missing global").to_equal("")
            _:
                expect("missing exports").to_equal("")
    _:
        expect("missing instance").to_equal("")
```

</details>

#### fails closed when valid modules require unsupported imports

1. var interp =  new interpreter
   - Expected: _object_property_text(interp, imported, "validated") equals `true`
   - Expected: _object_property_text(interp, imported, "hasTypeSection") equals `true`
   - Expected: _object_property_text(interp, imported, "hasImportSection") equals `true`
   - Expected: _object_property_text(interp, instance, "status") equals `invalid`
   - Expected: _object_property_text(interp, instance, "moduleValid") equals `true`
   - Expected: _object_property_text(interp, instance, "error") equals `unsupported-wasm-imports`
   - Expected: _object_property_text(interp, result, "status") equals `invalid`
   - Expected: _object_property_text(interp, result, "error") equals `unsupported-wasm-imports`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()

val imported = interp._native_webassembly_module([JsValue.String(v: "0061736d01000000010401600000020b0103656e7603666f6f0000")])
expect(_object_property_text(interp, imported, "validated")).to_equal("true")
expect(_object_property_text(interp, imported, "hasTypeSection")).to_equal("true")
expect(_object_property_text(interp, imported, "hasImportSection")).to_equal("true")

val instance = interp._native_webassembly_instance([imported])
expect(_object_property_text(interp, instance, "status")).to_equal("invalid")
expect(_object_property_text(interp, instance, "moduleValid")).to_equal("true")
expect(_object_property_text(interp, instance, "error")).to_equal("unsupported-wasm-imports")

val result = interp._native_webassembly_instantiate(JsValue.Undefined, [JsValue.String(v: "0061736d01000000010401600000020b0103656e7603666f6f0000")])
expect(_object_property_text(interp, result, "status")).to_equal("invalid")
expect(_object_property_text(interp, result, "error")).to_equal("unsupported-wasm-imports")
```

</details>

#### constructs bounded WebAssembly.Memory values and grows within maximum

1. var interp =  new interpreter

2. interp set object property

3. interp set object property
   - Expected: _object_property_text(interp, memory, "pages") equals `1`
   - Expected: _object_property_text(interp, memory, "byteLength") equals `65536`
   - Expected: _object_child_property_text(interp, memory, "buffer", "byteLength") equals `65536`
   - Expected: _display_js(interp._native_webassembly_memory_grow(memory, [JsValue.Number(v: 1.0)])) equals `1`
   - Expected: _object_property_text(interp, memory, "pages") equals `2`
   - Expected: _object_child_property_text(interp, memory, "buffer", "byteLength") equals `131072`
   - Expected: _display_js(interp._native_webassembly_memory_grow(memory, [JsValue.Number(v: 1.0)])) equals `-1`
   - Expected: _object_property_text(interp, memory, "pages") equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = _new_interpreter()
val options_id = interp.create_object()
interp.set_object_property(options_id, "initial", JsValue.Number(v: 1.0))
interp.set_object_property(options_id, "maximum", JsValue.Number(v: 2.0))

val memory = interp._native_webassembly_memory([JsValue.Object(id: options_id)])
expect(_object_property_text(interp, memory, "pages")).to_equal("1")
expect(_object_property_text(interp, memory, "byteLength")).to_equal("65536")
expect(_object_child_property_text(interp, memory, "buffer", "byteLength")).to_equal("65536")

expect(_display_js(interp._native_webassembly_memory_grow(memory, [JsValue.Number(v: 1.0)]))).to_equal("1")
expect(_object_property_text(interp, memory, "pages")).to_equal("2")
expect(_object_child_property_text(interp, memory, "buffer", "byteLength")).to_equal("131072")
expect(_display_js(interp._native_webassembly_memory_grow(memory, [JsValue.Number(v: 1.0)]))).to_equal("-1")
expect(_object_property_text(interp, memory, "pages")).to_equal("2")
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
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

