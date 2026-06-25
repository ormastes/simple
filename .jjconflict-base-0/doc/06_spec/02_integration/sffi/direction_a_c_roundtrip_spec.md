# Direction A: Simple -> C Round-Trip Proof

> Full pipeline verification for Direction A (Simple -> C): 1. Compile Simple source to shared library (.so) 2. Generate C header from exported types/functions 3. Compile C consumer against the generated header 4. Link C consumer against the shared library 5. Execute and verify correct results

<!-- sdn-diagram:id=direction_a_c_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=direction_a_c_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

direction_a_c_roundtrip_spec -> std
direction_a_c_roundtrip_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=direction_a_c_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direction A: Simple -> C Round-Trip Proof

Full pipeline verification for Direction A (Simple -> C): 1. Compile Simple source to shared library (.so) 2. Generate C header from exported types/functions 3. Compile C consumer against the generated header 4. Link C consumer against the shared library 5. Execute and verify correct results

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR-WS7 |
| Category | Compiler Integration / SFFI |
| Status | End-to-End Proof |
| Source | `test/02_integration/sffi/direction_a_c_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Full pipeline verification for Direction A (Simple -> C):
1. Compile Simple source to shared library (.so)
2. Generate C header from exported types/functions
3. Compile C consumer against the generated header
4. Link C consumer against the shared library
5. Execute and verify correct results

Requires: gcc (or cc) on the host system. Tests skip gracefully if unavailable.

## Scenarios

### Direction A: Simple -> C round-trip

### shared library compilation

#### compiles a Simple library to shared object

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

#### generates C header for exported types

1. setup test dir
2. assert ok
3. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_test_dir()
val source_path = FIXTURE_DIR + "/calculator.spl"

val result = generate_headers(source_path, TEST_DIR, "calculator", true, false)
assert_ok(result.is_success(), "header generation failed")

val header_path = TEST_DIR + "/calculator.h"
assert_ok(rt_file_exists(header_path), "generated header missing")

val header = rt_file_read_text(header_path) ?? ""
expect(header).to_contain("spl_Calculator_create")
expect(header).to_contain("spl_Calculator_destroy")
expect(header).to_contain("spl_Calculator_add")
expect(header).to_contain("spl_Calculator_multiply")
expect(header).to_contain("spl_Calculator_get_accumulator")
expect(header).to_contain("calculator_square")
expect(header).to_contain("calculator_add")
expect(header).to_contain("spl_library_init")
expect(header).to_contain("spl_library_shutdown")
```

</details>

### C consumer compilation and execution

#### compiles C test program against generated header and shared library

1. setup test dir
2. print
3. print
   - Expected: code equals `0`
4. assert ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available (gcc/cc)"
setup_test_dir()

val cc = c_compiler()
val c_source = FIXTURE_DIR + "/test_calculator.c"
val output_bin = TEST_DIR + "/test_calculator"

val (out, err, code) = rt_process_run(cc, [
    "-o", output_bin,
    "-I" + TEST_DIR,
    c_source,
    "-L" + TEST_DIR,
    "-lcalculator",
    "-Wl,-rpath," + TEST_DIR
])

if code != 0:
    print("gcc stdout: " + out)
    print("gcc stderr: " + err)
expect(code).to_equal(0)
assert_ok(rt_file_exists(output_bin), "C output binary missing")
```

</details>

#### executes C test program and verifies PASS output

1. print
2. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available (gcc/cc)"

val output_bin = TEST_DIR + "/test_calculator"
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

### header content correctness

#### includes include guard and standard types

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header_path = TEST_DIR + "/calculator.h"
if not rt_file_exists(header_path):
    return "skip: header not generated"

val header = rt_file_read_text(header_path) ?? ""
expect(header).to_contain("#ifndef")
expect(header).to_contain("#define")
expect(header).to_contain("#endif")
expect(header).to_contain("int64_t")
```

</details>

#### declares opaque handle type for Calculator

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header_path = TEST_DIR + "/calculator.h"
if not rt_file_exists(header_path):
    return "skip: header not generated"

val header = rt_file_read_text(header_path) ?? ""
expect(header).to_contain("typedef struct spl_Calculator")
expect(header).to_contain("spl_Calculator_t")
```

</details>

#### includes _Static_assert for layout verification

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header_path = TEST_DIR + "/calculator.h"
if not rt_file_exists(header_path):
    return "skip: header not generated"

val header = rt_file_read_text(header_path) ?? ""
expect(header).to_contain("_Static_assert")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
