# Direction A: Simple -> C Round-Trip Proof

> Full pipeline verification for Direction A (Simple -> C): 1. Compile Simple source to shared library (.so) 2. Generate C header from exported types/functions 3. Compile C consumer against the generated header 4. Link C consumer against the shared library 5. Execute and verify correct results

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
| Source | `test/integration/sffi/direction_a_c_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
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

- compiles a Simple library to shared object


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles a Simple library to shared object")
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

- generates C header for exported types


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates C header for exported types")
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

- compiles C test program against generated header and shared library
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles C test program against generated header and shared library")
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

- executes C test program and verifies PASS output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes C test program and verifies PASS output")
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

- includes include guard and standard types


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes include guard and standard types")
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

- declares opaque handle type for Calculator


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares opaque handle type for Calculator")
val header_path = TEST_DIR + "/calculator.h"
if not rt_file_exists(header_path):
    return "skip: header not generated"

val header = rt_file_read_text(header_path) ?? ""
expect(header).to_contain("typedef struct spl_Calculator")
expect(header).to_contain("spl_Calculator_t")
```

</details>

#### includes _Static_assert for layout verification

- includes _Static_assert for layout verification


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes _Static_assert for layout verification")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2966b9b6dd7b9401d96f9a76c95c8b9746f60504d3ad725e9358e63afbfb1df4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2966b9b6dd7b9401d96f9a76c95c8b9746f60504d3ad725e9358e63afbfb1df4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2966b9b6dd7b9401d96f9a76c95c8b9746f60504d3ad725e9358e63afbfb1df4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/sffi/direction_a_c_roundtrip_spec.spl
mirror: doc/06_spec/integration/sffi/direction_a_c_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/sffi/direction_a_c_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/sffi/direction_a_c_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/sffi/direction_a_c_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/sffi/direction_a_c_roundtrip_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles a Simple library to shared object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/direction_a_c_roundtrip_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates C header for exported types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/direction_a_c_roundtrip_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles C test program against generated header and shared library' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
