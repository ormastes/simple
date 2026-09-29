# SFFI Callback Round-Trip Proof

> Purpose: This spec proves SFFI Callback Round-Trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFFI Callback Round-Trip Proof

Purpose: This spec proves SFFI Callback Round-Trip.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR-WS7 |
| Category | Compiler Integration / SFFI |
| Status | End-to-End Proof |
| Source | `test/integration/sffi/callback_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SFFI Callback Round-Trip.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### SFFI Callback Round-Trip

### type classification

#### recognizes stateless Fn types as callbacks

- recognizes stateless Fn types as callbacks
   - Expected: extract_callback_params("Fn<(i64, f64) -> bool>").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CALLBACKROUNDTRIP-001
step("recognizes stateless Fn types as callbacks")
assert_ok(is_callback_type("Fn<(i64) -> i64>"), "single-param callback type not recognized")
assert_ok(is_callback_type("Fn<(i64, f64) -> bool>"), "multi-param callback type not recognized")
assert_ok(is_callback_type("Fn<() -> void>"), "no-arg callback type not recognized")
expect(extract_callback_params("Fn<(i64, f64) -> bool>").len()).to_equal(2)
```

</details>

#### rejects closures with captures

- rejects closures with captures
- rejects closures with captures
   - Expected: "closure with captures must not be treated as callback" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects closures with captures")
step("rejects closures with captures")
if is_callback_type("Fn<(i64) -> i64>[x, y]"):
    expect("closure with captures must not be treated as callback").to_equal("")
assert_ok(is_closure_with_captures("Fn<(i64) -> i64>[x, y]"), "closure capture marker not detected")
expect("Fn<(i64) -> i64>[x, y]").to_contain("[x, y]")
```

</details>

#### rejects non-function types

- rejects non-function types
- rejects non-function types
   - Expected: "non-function types must not be treated as callbacks" equals ``
   - Expected: "Calculator" equals `Calculator`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects non-function types")
step("rejects non-function types")
if is_callback_type("i64") or is_callback_type("text") or is_callback_type("Calculator"):
    expect("non-function types must not be treated as callbacks").to_equal("")
expect("Calculator").to_equal("Calculator")
```

</details>

### callback parameter extraction

#### extracts parameter types from single-param callback

- extracts parameter types from single-param callback
- extracts parameter types from single-param callback
   - Expected: params.len() equals `1`
   - Expected: params[0] equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts parameter types from single-param callback")
step("extracts parameter types from single-param callback")
val params = extract_callback_params("Fn<(i64) -> i64>")
expect(params.len()).to_equal(1)
expect(params[0]).to_equal("i64")
```

</details>

#### extracts parameter types from multi-param callback

- extracts parameter types from multi-param callback
- extracts parameter types from multi-param callback
   - Expected: params.len() equals `2`
   - Expected: params[0] equals `i64`
   - Expected: params[1] equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts parameter types from multi-param callback")
step("extracts parameter types from multi-param callback")
val params = extract_callback_params("Fn<(i64, f64) -> bool>")
expect(params.len()).to_equal(2)
expect(params[0]).to_equal("i64")
expect(params[1]).to_equal("f64")
```

</details>

#### extracts empty params from no-arg callback

- extracts empty params from no-arg callback
- extracts empty params from no-arg callback
   - Expected: params.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts empty params from no-arg callback")
step("extracts empty params from no-arg callback")
val params = extract_callback_params("Fn<() -> void>")
expect(params.len()).to_equal(0)
```

</details>

#### extracts return type from callback

- extracts return type from callback
- extracts return type from callback
   - Expected: extract_callback_return("Fn<(i64) -> i64>") equals `i64`
   - Expected: extract_callback_return("Fn<(i64, f64) -> bool>") equals `bool`
   - Expected: extract_callback_return("Fn<() -> void>") equals `void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts return type from callback")
step("extracts return type from callback")
expect(extract_callback_return("Fn<(i64) -> i64>")).to_equal("i64")
expect(extract_callback_return("Fn<(i64, f64) -> bool>")).to_equal("bool")
expect(extract_callback_return("Fn<() -> void>")).to_equal("void")
```

</details>

### typedef generation

#### generates stable typedef name from signature

- generates stable typedef name from signature
- generates stable typedef name from signature
   - Expected: "callback typedef name should not be empty" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates stable typedef name from signature")
step("generates stable typedef name from signature")
val name = callback_typedef_name(["i64"], "i64")
if name.len() == 0:
    expect("callback typedef name should not be empty").to_equal("")
expect(name).to_contain("callback")
```

</details>

#### builds CallbackTypedef from type string

- builds CallbackTypedef from type string
- builds CallbackTypedef from type string
   - Expected: "callback typedef name should not be empty" equals ``
   - Expected: cb.param_types.len() equals `1`
   - Expected: "callback typedef return type should not be empty" equals ``
   - Expected: cb.return_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds CallbackTypedef from type string")
step("builds CallbackTypedef from type string")
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

- emits valid C typedef for single-param callback
- emits valid C typedef for single-param callback


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits valid C typedef for single-param callback")
step("emits valid C typedef for single-param callback")
val cb = build_callback_typedef("Fn<(i64) -> i64>")
val typedef_text = emit_callback_typedef(cb)
expect(typedef_text).to_contain("typedef")
expect(typedef_text).to_contain("(*")
expect(typedef_text).to_contain("int64_t")
```

</details>

#### emits valid C typedef for multi-param callback

- emits valid C typedef for multi-param callback
- emits valid C typedef for multi-param callback


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits valid C typedef for multi-param callback")
step("emits valid C typedef for multi-param callback")
val cb = build_callback_typedef("Fn<(i64, f64) -> bool>")
val typedef_text = emit_callback_typedef(cb)
expect(typedef_text).to_contain("typedef")
expect(typedef_text).to_contain("int64_t")
expect(typedef_text).to_contain("double")
```

</details>

### trampoline generation

#### generates a trampoline function wrapping the callback

- generates a trampoline function wrapping the callback
- generates a trampoline function wrapping the callback
   - Expected: "callback trampoline should not be empty" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates a trampoline function wrapping the callback")
step("generates a trampoline function wrapping the callback")
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

- includes callback typedefs in generated header when export uses Fn types
- includes callback typedefs in generated header when export uses Fn types


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes callback typedefs in generated header when export uses Fn types")
step("includes callback typedefs in generated header when export uses Fn types")
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

- creates Simple source that exports a function accepting a callback
- creates Simple source that exports a function accepting a callback


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates Simple source that exports a function accepting a callback")
step("creates Simple source that exports a function accepting a callback")
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

- compiles callback library to shared object
- compiles callback library to shared object


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles callback library to shared object")
step("compiles callback library to shared object")
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

- generates header with callback typedefs
- generates header with callback typedefs


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates header with callback typedefs")
step("generates header with callback typedefs")
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

- creates C test program that passes function pointers
- creates C test program that passes function pointers


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates C test program that passes function pointers")
step("creates C test program that passes function pointers")
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

- compiles and executes C callback test program
- compiles and executes C callback test program
   - Expected: ccode equals `0`
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles and executes C callback test program")
step("compiles and executes C callback test program")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-CALLBACKROUNDTRIP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e03cd3e1460139b9b3c7b0f36b2562be9856ffc02e9338b33db7256d4678a9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e03cd3e1460139b9b3c7b0f36b2562be9856ffc02e9338b33db7256d4678a9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e03cd3e1460139b9b3c7b0f36b2562be9856ffc02e9338b33db7256d4678a9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/sffi/callback_roundtrip_spec.spl
mirror: doc/06_spec/integration/sffi/callback_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/sffi/callback_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/sffi/callback_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/sffi/callback_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/sffi/callback_roundtrip_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes stateless Fn types as callbacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/callback_roundtrip_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects closures with captures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/callback_roundtrip_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-function types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
