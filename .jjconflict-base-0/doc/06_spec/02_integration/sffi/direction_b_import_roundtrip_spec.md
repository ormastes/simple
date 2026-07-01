# Direction B: C -> Simple Import Round-Trip Proof

> Full pipeline verification for Direction B (C -> Simple): 1. Create a minimal C shared library with known functions 2. Compile it to a .so 3. Write a manifest.sdn pointing to the library 4. Simple code uses `extern fn` to call the C functions via SFFI 5. Verify correct results through the interpreter / compiled path

<!-- sdn-diagram:id=direction_b_import_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=direction_b_import_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

direction_b_import_roundtrip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=direction_b_import_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direction B: C -> Simple Import Round-Trip Proof

Full pipeline verification for Direction B (C -> Simple): 1. Create a minimal C shared library with known functions 2. Compile it to a .so 3. Write a manifest.sdn pointing to the library 4. Simple code uses `extern fn` to call the C functions via SFFI 5. Verify correct results through the interpreter / compiled path

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR-WS7 |
| Category | Compiler Integration / SFFI |
| Status | End-to-End Proof |
| Source | `test/02_integration/sffi/direction_b_import_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Full pipeline verification for Direction B (C -> Simple):
1. Create a minimal C shared library with known functions
2. Compile it to a .so
3. Write a manifest.sdn pointing to the library
4. Simple code uses `extern fn` to call the C functions via SFFI
5. Verify correct results through the interpreter / compiled path

Requires: gcc (or cc) on the host system. Tests skip gracefully if unavailable.

## Scenarios

### Direction B: C -> Simple import round-trip

### C library creation

#### creates a minimal C library with arithmetic functions

1. "int64 t mathlib add
2. "int64 t mathlib multiply
3. "int64 t mathlib negate
4. assert ok
5. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_source = TEST_DIR + "/mathlib.c"
val c_code = "#include <stdint.h>" + NL +
    NL +
    "int64_t mathlib_add(int64_t a, int64_t b) {" + NL +
    "    return a + b;" + NL +
    "}" + NL +
    NL +
    "int64_t mathlib_multiply(int64_t a, int64_t b) {" + NL +
    "    return a * b;" + NL +
    "}" + NL +
    NL +
    "int64_t mathlib_negate(int64_t x) {" + NL +
    "    return -x;" + NL +
    "}" + NL

assert_ok(write_source(c_source, c_code), "failed to write C source")
assert_ok(rt_file_exists(c_source), "C source missing")
expect(c_source).to_end_with(".c")
```

</details>

#### compiles C library to shared object

1. print
2. print
   - Expected: code equals `0`
3. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

val cc = c_compiler()
val c_source = TEST_DIR + "/mathlib.c"
val so_path = TEST_DIR + "/libmathlib.so"

val (out, err, code) = rt_process_run(cc, [
    "-shared", "-fPIC",
    "-o", so_path,
    c_source
])

if code != 0:
    print("compile stdout: " + out)
    print("compile stderr: " + err)
expect(code).to_equal(0)
assert_ok(rt_file_exists(so_path), "shared object missing")
expect(so_path).to_end_with(".so")
```

</details>

### Simple extern fn import

#### creates Simple source that imports the C functions via extern fn

1. "extern fn mathlib add
2. "extern fn mathlib multiply
3. "extern fn mathlib negate
4. "val sum = mathlib add
5. "val product = mathlib multiply
6. "val neg = mathlib negate
7. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spl_source = TEST_DIR + "/test_import.spl"
val spl_code = "# Test: import C functions via extern fn" + NL +
    "extern fn mathlib_add(a: i64, b: i64) -> i64" + NL +
    "extern fn mathlib_multiply(a: i64, b: i64) -> i64" + NL +
    "extern fn mathlib_negate(x: i64) -> i64" + NL +
    NL +
    "val sum = mathlib_add(10, 20)" + NL +
    "val product = mathlib_multiply(6, 7)" + NL +
    "val neg = mathlib_negate(42)" + NL +
    NL +
    "assert sum == 30" + NL +
    "assert product == 42" + NL +
    "assert neg == -42" + NL +
    NL +
    "print \"PASS: Direction B import round-trip\"" + NL

assert_ok(write_source(spl_source, spl_code), "failed to write Simple source")
expect(spl_source).to_end_with(".spl")
```

</details>

#### executes Simple source linked against C library

1. print
2. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

val so_path = TEST_DIR + "/libmathlib.so"
if not rt_file_exists(so_path):
    return "skip: C library not built"

val spl_source = TEST_DIR + "/test_import.spl"
val env_cmd = "LD_LIBRARY_PATH=" + TEST_DIR + " bin/simple run " + spl_source + " --link " + so_path
val (out, err, code) = rt_process_run("/bin/sh", ["-c", env_cmd])

if code != 0:
    print("simple stdout: " + out)
    print("simple stderr: " + err)
expect(code).to_equal(0)
expect(out).to_contain("PASS")
```

</details>

### manifest-based import

#### creates SDN manifest pointing to library

1. assert ok
2. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest_path = TEST_DIR + "/mathlib.sdn"
val manifest = "library {" + NL +
    "  name: \"mathlib\"" + NL +
    "  path: \"" + TEST_DIR + "/libmathlib.so\"" + NL +
    "  language: \"C\"" + NL +
    "  functions {" + NL +
    "    mathlib_add { params: [\"i64\", \"i64\"], return: \"i64\" }" + NL +
    "    mathlib_multiply { params: [\"i64\", \"i64\"], return: \"i64\" }" + NL +
    "    mathlib_negate { params: [\"i64\"], return: \"i64\" }" + NL +
    "  }" + NL +
    "}" + NL

assert_ok(write_source(manifest_path, manifest), "failed to write manifest")
assert_ok(rt_file_exists(manifest_path), "manifest missing")
expect(manifest_path).to_end_with(".sdn")
```

</details>

#### verifies manifest describes the correct function signatures

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest_path = TEST_DIR + "/mathlib.sdn"
if not rt_file_exists(manifest_path):
    return "skip: manifest not created"

val content = rt_file_read_text(manifest_path) ?? ""
expect(content).to_contain("mathlib_add")
expect(content).to_contain("mathlib_multiply")
expect(content).to_contain("mathlib_negate")
expect(content).to_contain("language: \"C\"")
```

</details>

### error handling for missing symbols

#### creates C library with subset of expected functions

1. "int64 t partial add
2. assert ok
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

val c_source = TEST_DIR + "/partial.c"
val c_code = "#include <stdint.h>" + NL +
    "int64_t partial_add(int64_t a, int64_t b) { return a + b; }" + NL

assert_ok(write_source(c_source, c_code), "failed to write partial C source")

val cc = c_compiler()
val (out, err, code) = rt_process_run(cc, [
    "-shared", "-fPIC",
    "-o", TEST_DIR + "/libpartial.so",
    c_source
])
expect(code).to_equal(0)
```

</details>

#### reports missing symbol when extern fn is not found in library

1. "val result = partial missing
2. assert ok
   - Expected: "missing symbol link should fail" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

val so_path = TEST_DIR + "/libpartial.so"
if not rt_file_exists(so_path):
    return "skip: partial library not built"

val spl_source = TEST_DIR + "/test_missing.spl"
val spl_code = "extern fn partial_missing(x: i64) -> i64" + NL +
    "val result = partial_missing(1)" + NL

assert_ok(write_source(spl_source, spl_code), "failed to write missing-symbol fixture")

# Attempting to link against library missing the symbol should fail
val env_cmd = "LD_LIBRARY_PATH=" + TEST_DIR + " bin/simple run " + spl_source + " --link " + so_path + " 2>&1"
val (out, _err, code) = rt_process_run("/bin/sh", ["-c", env_cmd])

# Should fail -- symbol not found
if code == 0:
    expect("missing symbol link should fail").to_equal("")
expect(out).to_contain("partial_missing")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
