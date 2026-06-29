# Direction A: Simple -> C++ Round-Trip Proof

> Full pipeline verification for Direction A (Simple -> C++): 1. Compile Simple source to shared library (.so) 2. Generate C and C++ headers from exported types/functions 3. Compile C++ consumer against the generated headers 4. Link C++ consumer against the shared library 5. Execute and verify RAII lifecycle, move semantics, noexcept default API, and opt-in exception facade

<!-- sdn-diagram:id=direction_a_cpp_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=direction_a_cpp_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

direction_a_cpp_roundtrip_spec -> std
direction_a_cpp_roundtrip_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=direction_a_cpp_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direction A: Simple -> C++ Round-Trip Proof

Full pipeline verification for Direction A (Simple -> C++): 1. Compile Simple source to shared library (.so) 2. Generate C and C++ headers from exported types/functions 3. Compile C++ consumer against the generated headers 4. Link C++ consumer against the shared library 5. Execute and verify RAII lifecycle, move semantics, noexcept default API, and opt-in exception facade

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR-WS7 |
| Category | Compiler Integration / SFFI |
| Status | End-to-End Proof |
| Source | `test/02_integration/sffi/direction_a_cpp_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Full pipeline verification for Direction A (Simple -> C++):
1. Compile Simple source to shared library (.so)
2. Generate C and C++ headers from exported types/functions
3. Compile C++ consumer against the generated headers
4. Link C++ consumer against the shared library
5. Execute and verify RAII lifecycle, move semantics, noexcept default API,
   and opt-in exception facade

Requires: g++ (or c++) on the host system. Tests skip gracefully if unavailable.

## Scenarios

### Direction A: Simple -> C++ round-trip

### shared library and header generation

#### compiles Simple library to shared object

1. setup test dir
2. assert ok
3. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_test_dir()
val source_path = FIXTURE_DIR + "/calculator.spl"
val output_path = TEST_DIR + "/libcalculator.so"

val result = aot_shared_library(source_path, output_path)
assert_ok(result.is_success(), "shared library build failed")
assert_ok(rt_file_exists(output_path), "shared library output missing")
expect(output_path).to_end_with(".so")
```

</details>

#### generates both C and C++ headers

1. setup test dir
2. assert ok
3. assert ok
4. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_test_dir()
val source_path = FIXTURE_DIR + "/calculator.spl"

val result = generate_headers(source_path, TEST_DIR, "calculator", true, true)
assert_ok(result.is_success(), "header generation failed")

val h_path = TEST_DIR + "/calculator.h"
val hpp_path = TEST_DIR + "/calculator.hpp"
assert_ok(rt_file_exists(h_path), "generated C header missing")
assert_ok(rt_file_exists(hpp_path), "generated C++ header missing")
expect(hpp_path).to_end_with(".hpp")
```

</details>

### C++ header content

#### wraps types in spl namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("namespace spl")
expect(header).to_contain("class Calculator")
```

</details>

#### includes RAII Library class

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("class Library")
expect(header).to_contain("Library() { spl_library_init(); }")
expect(header).to_contain("~Library() { spl_library_shutdown(); }")
```

</details>

#### declares move-only semantics for Calculator

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("Calculator(const Calculator&) = delete;")
expect(header).to_contain("Calculator(Calculator&& other) noexcept")
expect(header).to_contain("~Calculator()")
```

</details>

#### emits noexcept result wrapper by default and gates throwing facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("bool calculator_checked_divide(")
expect(header).to_contain("std::string* out_error = nullptr")
expect(header).to_contain("#ifdef SIMPLE_SFFI_ENABLE_CPP_EXCEPTIONS")
expect(header).to_contain("calculator_checked_divide_or_throw")
```

</details>

#### includes static_assert for layout verification

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("static_assert")
```

</details>

#### includes underlying C header

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("#include \"calculator.h\"")
```

</details>

### C++ consumer compilation and execution

#### compiles default C++ test program against generated headers with exceptions disabled

1. setup test dir
2. print
3. print
   - Expected: code equals `0`
4. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_cpp_compiler():
    return "skip: no C++ compiler available (g++/c++)"
setup_test_dir()

val cxx = cpp_compiler()
val cpp_source = FIXTURE_DIR + "/test_calculator.cpp"
val output_bin = TEST_DIR + "/test_calculator_cpp"

val (out, err, code) = rt_process_run(cxx, [
    "-std=c++14",
    "-fno-exceptions",
    "-o", output_bin,
    "-I" + TEST_DIR,
    cpp_source,
    "-L" + TEST_DIR,
    "-lcalculator",
    "-Wl,-rpath," + TEST_DIR
])

if code != 0:
    print("g++ stdout: " + out)
    print("g++ stderr: " + err)
expect(code).to_equal(0)
assert_ok(rt_file_exists(output_bin), "C++ output binary missing")
```

</details>

#### compiles optional throwing facade when explicitly enabled

1. setup test dir
2. print
3. print
   - Expected: code equals `0`
4. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_cpp_compiler():
    return "skip: no C++ compiler available (g++/c++)"
setup_test_dir()

val cxx = cpp_compiler()
val cpp_source = FIXTURE_DIR + "/test_calculator_throwing.cpp"
val output_bin = TEST_DIR + "/test_calculator_cpp_throwing"

val (out, err, code) = rt_process_run(cxx, [
    "-std=c++14",
    "-o", output_bin,
    "-I" + TEST_DIR,
    cpp_source,
    "-L" + TEST_DIR,
    "-lcalculator",
    "-Wl,-rpath," + TEST_DIR
])

if code != 0:
    print("g++ stdout: " + out)
    print("g++ stderr: " + err)
expect(code).to_equal(0)
assert_ok(rt_file_exists(output_bin), "throwing C++ output binary missing")
```

</details>

#### executes C++ test program and verifies PASS output

1. print
2. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_cpp_compiler():
    return "skip: no C++ compiler available (g++/c++)"

val output_bin = TEST_DIR + "/test_calculator_cpp"
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

#### executes optional throwing facade test program

1. print
2. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_cpp_compiler():
    return "skip: no C++ compiler available (g++/c++)"

val output_bin = TEST_DIR + "/test_calculator_cpp_throwing"
if not rt_file_exists(output_bin):
    return "skip: throwing test binary not built"

val env_cmd = "LD_LIBRARY_PATH=" + TEST_DIR + " " + output_bin
val (out, err, code) = rt_process_run("/bin/sh", ["-c", env_cmd])

if code != 0:
    print("test stdout: " + out)
    print("test stderr: " + err)
expect(code).to_equal(0)
expect(out).to_contain("PASS")
```

</details>

### RAII and move safety

#### verifies destructor does not double-free after move

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is verified by the C++ test program above:
# calc1 is moved into calc2, then only calc2's destructor fires.
# If double-free occurred, the test program would segfault.
if not has_cpp_compiler():
    return "skip: no C++ compiler available"

val output_bin = TEST_DIR + "/test_calculator_cpp"
if not rt_file_exists(output_bin):
    return "skip: test binary not built"

val env_cmd = "LD_LIBRARY_PATH=" + TEST_DIR + " " + output_bin
val (_out, _err, code) = rt_process_run("/bin/sh", ["-c", env_cmd])
# Non-zero exit means segfault or double-free
expect(code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
