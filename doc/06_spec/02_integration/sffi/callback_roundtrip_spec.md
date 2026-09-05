# SFFI Callback Round-Trip Proof

> Tests callback (function pointer) passing across the SFFI boundary:

<!-- sdn-diagram:id=callback_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=callback_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

callback_roundtrip_spec -> std
callback_roundtrip_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=callback_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFFI Callback Round-Trip Proof

Tests callback (function pointer) passing across the SFFI boundary:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR-WS7 |
| Category | Compiler Integration / SFFI |
| Status | End-to-End Proof |
| Source | `test/02_integration/sffi/callback_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests callback (function pointer) passing across the SFFI boundary:

1. **Type classification** -- `is_callback_type` distinguishes stateless function
   pointers (`Fn<(A) -> B>`) from closures with captures.
2. **Typedef generation** -- `build_callback_typedef` + `emit_callback_typedef`
   produce correct C `typedef` declarations.
3. **Trampoline generation** -- `emit_callback_trampoline` wraps a C function
   pointer so Simple can invoke it through a stable ABI trampoline.
4. **C header integration** -- Generated headers include callback typedefs
   before the function declarations that reference them.
5. **End-to-end** -- A Simple library exports a function accepting a callback.
   A C test program calls it with a C function pointer. The callback is
   invoked and its result is verified.

Requires: gcc (or cc) on the host system. Tests skip gracefully if unavailable.

## Scenarios

### SFFI Callback Round-Trip

### type classification

#### recognizes stateless Fn types as callbacks

1. assert ok
2. assert ok
3. assert ok
   - Expected: extract_callback_params("Fn<(i64, f64) -> bool>").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_ok(is_callback_type("Fn<(i64) -> i64>"), "single-param callback type not recognized")
assert_ok(is_callback_type("Fn<(i64, f64) -> bool>"), "multi-param callback type not recognized")
assert_ok(is_callback_type("Fn<() -> void>"), "no-arg callback type not recognized")
expect(extract_callback_params("Fn<(i64, f64) -> bool>").len()).to_equal(2)
```

</details>

#### rejects closures with captures

1. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_callback_type("Fn<(i64) -> i64>[x, y]"):
    expect("closure with captures must not be treated as callback").to_equal("")
assert_ok(is_closure_with_captures("Fn<(i64) -> i64>[x, y]"), "closure capture marker not detected")
expect("Fn<(i64) -> i64>[x, y]").to_contain("[x, y]")
```

</details>

#### rejects non-function types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_callback_type("i64") or is_callback_type("text") or is_callback_type("Calculator"):
    expect("non-function types must not be treated as callbacks").to_equal("")
expect("Calculator").to_equal("Calculator")
```

</details>

### callback parameter extraction

#### extracts parameter types from single-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = extract_callback_params("Fn<(i64) -> i64>")
expect(params.len()).to_equal(1)
expect(params[0]).to_equal("i64")
```

</details>

#### extracts parameter types from multi-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = extract_callback_params("Fn<(i64, f64) -> bool>")
expect(params.len()).to_equal(2)
expect(params[0]).to_equal("i64")
expect(params[1]).to_equal("f64")
```

</details>

#### extracts empty params from no-arg callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = extract_callback_params("Fn<() -> void>")
expect(params.len()).to_equal(0)
```

</details>

#### extracts return type from callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(extract_callback_return("Fn<(i64) -> i64>")).to_equal("i64")
expect(extract_callback_return("Fn<(i64, f64) -> bool>")).to_equal("bool")
expect(extract_callback_return("Fn<() -> void>")).to_equal("void")
```

</details>

### typedef generation

#### generates stable typedef name from signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = callback_typedef_name(["i64"], "i64")
if name.len() == 0:
    expect("callback typedef name should not be empty").to_equal("")
expect(name).to_contain("callback")
```

</details>

#### builds CallbackTypedef from type string

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = build_callback_typedef("Fn<(i64) -> i64>")
if cb.name.len() == 0:
    expect("callback typedef name should not be empty").to_equal("")
expect(cb.param_types.len()).to_equal(1)
if cb.return_type.len() == 0:
    expect("callback typedef return type should not be empty").to_equal("")
expect(cb.return_type).to_equal("i64")
```

</details>

#### emits valid C typedef for single-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = build_callback_typedef("Fn<(i64) -> i64>")
val typedef_text = emit_callback_typedef(cb)
expect(typedef_text).to_contain("typedef")
expect(typedef_text).to_contain("(*")
expect(typedef_text).to_contain("int64_t")
```

</details>

#### emits valid C typedef for multi-param callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = build_callback_typedef("Fn<(i64, f64) -> bool>")
val typedef_text = emit_callback_typedef(cb)
expect(typedef_text).to_contain("typedef")
expect(typedef_text).to_contain("int64_t")
expect(typedef_text).to_contain("double")
```

</details>

### trampoline generation

#### generates a trampoline function wrapping the callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = build_callback_typedef("Fn<(i64) -> i64>")
val trampoline = emit_callback_trampoline("apply_callback", cb)
# Trampoline should contain the function pointer invocation
if trampoline.len() == 0:
    expect("callback trampoline should not be empty").to_equal("")
expect(trampoline).to_contain("apply_callback")
```

</details>

### C header integration

#### includes callback typedefs in generated header when export uses Fn types

1. symbol: SymbolId
2. params: [make mir i64
3. return type: make mir i64
4. entry block: BlockId entry
5. span: empty span


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a MIR module with a function that takes a callback param
val fn_with_callback = MirFunction(
    symbol: SymbolId(id: 50),
    name: "__simple_apply_transform",
    signature: MirSignature(
        params: [make_mir_i64(), make_mir_fn_ptr([make_mir_i64()], make_mir_i64())],
        return_type: make_mir_i64(),
        is_variadic: false
    ),
    locals: [],
    blocks: [],
    entry_block: BlockId.entry(),
    span: empty_span(),
    generic_params: [],
    is_generic_template: false,
    specialization_of: nil,
    type_bindings: {},
    layout_phase: nil,
    is_kernel: false,
    is_export_c: true,
    export_name: "",
    driver_manifest_attr: nil
)

var funcs: Dict<SymbolId, MirFunction> = {}
funcs[fn_with_callback.symbol] = fn_with_callback
val module = MirModule(
    name: "test.callback",
    functions: funcs,
    statics: {},
    constants: {},
    types: {}
)

val header = emit_c_header("callback_test", [fn_with_callback], [], module)
# Header should contain the callback typedef before the function decl
expect(header).to_contain("typedef")
expect(header).to_contain("spl_apply_transform")
```

</details>

### end-to-end callback compilation

#### creates Simple source that exports a function accepting a callback

1. "fn apply transform
2. "    transform
3. "@export
4. "fn apply binary
5. "    op
6. assert ok
7. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spl_source = TEST_DIR + "/callback_lib.spl"
val spl_code = "@export(\"C\")" + NL +
    "fn apply_transform(value: i64, transform: Fn<(i64) -> i64>) -> i64:" + NL +
    "    transform(value)" + NL +
    NL +
    "@export(\"C\")" + NL +
    "fn apply_binary(a: i64, b: i64, op: Fn<(i64, i64) -> i64>) -> i64:" + NL +
    "    op(a, b)" + NL

assert_ok(write_source(spl_source, spl_code), "failed to write callback library source")
assert_ok(rt_file_exists(spl_source), "callback library source missing")
expect(spl_source).to_end_with(".spl")
```

</details>

#### compiles callback library to shared object

1. assert ok
2. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spl_source = TEST_DIR + "/callback_lib.spl"
if not rt_file_exists(spl_source):
    return "skip: source not created"

val output_path = TEST_DIR + "/libcallback.so"
val result = aot_shared_library(spl_source, output_path)
assert_ok(result.is_success(), "callback library build failed")
assert_ok(rt_file_exists(output_path), "callback library output missing")
```

</details>

#### generates header with callback typedefs

1. assert ok
2. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spl_source = TEST_DIR + "/callback_lib.spl"
if not rt_file_exists(spl_source):
    return "skip: source not created"

val result = generate_headers(spl_source, TEST_DIR, "callback_lib", true, false)
assert_ok(result.is_success(), "callback header generation failed")

val header_path = TEST_DIR + "/callback_lib.h"
assert_ok(rt_file_exists(header_path), "callback header missing")

val header = rt_file_read_text(header_path) ?? ""
expect(header).to_contain("typedef")
expect(header).to_contain("spl_apply_transform")
expect(header).to_contain("spl_apply_binary")
```

</details>

#### creates C test program that passes function pointers

1. "static int64 t my square
2. "static int64 t my negate
3. "static int64 t my add
4. "static int64 t my multiply
5. "int main
6. "    spl library init
7. "    assert
8. "    assert
9. "    assert
10. "    assert
11. "    assert
12. "    assert
13. "    spl library shutdown
14. "    printf
15. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_source = TEST_DIR + "/test_callback.c"
val c_code = "#include <stdio.h>" + NL +
    "#include <assert.h>" + NL +
    "#include \"callback_lib.h\"" + NL +
    NL +
    "static int64_t my_square(int64_t x) {" + NL +
    "    return x * x;" + NL +
    "}" + NL +
    NL +
    "static int64_t my_negate(int64_t x) {" + NL +
    "    return -x;" + NL +
    "}" + NL +
    NL +
    "static int64_t my_add(int64_t a, int64_t b) {" + NL +
    "    return a + b;" + NL +
    "}" + NL +
    NL +
    "static int64_t my_multiply(int64_t a, int64_t b) {" + NL +
    "    return a * b;" + NL +
    "}" + NL +
    NL +
    "int main(void) {" + NL +
    "    spl_library_init();" + NL +
    NL +
    "    /* Test apply_transform with different callbacks */" + NL +
    "    assert(spl_apply_transform(5, my_square) == 25);" + NL +
    "    assert(spl_apply_transform(7, my_negate) == -7);" + NL +
    "    assert(spl_apply_transform(0, my_square) == 0);" + NL +
    NL +
    "    /* Test apply_binary with different callbacks */" + NL +
    "    assert(spl_apply_binary(3, 4, my_add) == 7);" + NL +
    "    assert(spl_apply_binary(6, 7, my_multiply) == 42);" + NL +
    "    assert(spl_apply_binary(-1, 1, my_add) == 0);" + NL +
    NL +
    "    spl_library_shutdown();" + NL +
    "    printf(\"PASS: all callback round-trip tests passed\\n\");" + NL +
    "    return 0;" + NL +
    "}" + NL

assert_ok(write_source(c_source, c_code), "failed to write callback C test")
expect(c_source).to_end_with(".c")
```

</details>

#### compiles and executes C callback test program

1. print
2. print
   - Expected: ccode equals `0`
3. print
4. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available (gcc/cc)"

val so_path = TEST_DIR + "/libcallback.so"
val header_path = TEST_DIR + "/callback_lib.h"
if not rt_file_exists(so_path) or not rt_file_exists(header_path):
    return "skip: shared library or header not built"

val cc = c_compiler()
val c_source = TEST_DIR + "/test_callback.c"
val output_bin = TEST_DIR + "/test_callback"

val (cout, cerr, ccode) = rt_process_run(cc, [
    "-o", output_bin,
    "-I" + TEST_DIR,
    "-L" + TEST_DIR,
    "-lcallback",
    "-Wl,-rpath," + TEST_DIR,
    c_source
])

if ccode != 0:
    print("compile stdout: " + cout)
    print("compile stderr: " + cerr)
expect(ccode).to_equal(0)

if not rt_file_exists(output_bin):
    return "skip: test binary not built"

val env_cmd = "LD_LIBRARY_PATH=" + TEST_DIR + " " + output_bin
val (out, err, code) = rt_process_run("/bin/sh", ["-c", env_cmd])

if code != 0:
    print("test stdout: " + out)
    print("test stderr: " + err)
expect(code).to_equal(0)
expect(out).to_contain("PASS")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
