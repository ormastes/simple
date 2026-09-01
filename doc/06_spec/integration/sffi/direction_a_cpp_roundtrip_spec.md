# Direction A: Simple -> C++ Round-Trip Proof

> Purpose: This spec proves Direction A: Simple -> C++ round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direction A: Simple -> C++ Round-Trip Proof

Purpose: This spec proves Direction A: Simple -> C++ round-trip.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR-WS7 |
| Category | Compiler Integration / SFFI |
| Status | End-to-End Proof |
| Source | `test/integration/sffi/direction_a_cpp_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Direction A: Simple -> C++ round-trip.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Direction A: Simple -> C++ round-trip

### shared library and header generation

#### compiles Simple library to shared object

- compiles Simple library to shared object


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DIRECTIONACPPROUNDTRIP-001
step("compiles Simple library to shared object")
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

- generates both C and C++ headers
- generates both C and C++ headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates both C and C++ headers")
step("generates both C and C++ headers")
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

- wraps types in spl namespace
- wraps types in spl namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wraps types in spl namespace")
step("wraps types in spl namespace")
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("namespace spl")
expect(header).to_contain("class Calculator")
```

</details>

#### includes RAII Library class

- includes RAII Library class
- includes RAII Library class


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes RAII Library class")
step("includes RAII Library class")
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

- declares move-only semantics for Calculator
- declares move-only semantics for Calculator


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares move-only semantics for Calculator")
step("declares move-only semantics for Calculator")
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

- emits noexcept result wrapper by default and gates throwing facade
- emits noexcept result wrapper by default and gates throwing facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits noexcept result wrapper by default and gates throwing facade")
step("emits noexcept result wrapper by default and gates throwing facade")
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

- includes static_assert for layout verification
- includes static_assert for layout verification


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes static_assert for layout verification")
step("includes static_assert for layout verification")
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("static_assert")
```

</details>

#### includes underlying C header

- includes underlying C header
- includes underlying C header


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes underlying C header")
step("includes underlying C header")
val hpp_path = TEST_DIR + "/calculator.hpp"
if not rt_file_exists(hpp_path):
    return "skip: C++ header not generated"

val header = rt_file_read_text(hpp_path) ?? ""
expect(header).to_contain("#include \"calculator.h\"")
```

</details>

### C++ consumer compilation and execution

#### compiles default C++ test program against generated headers with exceptions disabled

- compiles default C++ test program against generated headers with exceptions disabled
- compiles default C++ test program against generated headers with excepti
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles default C++ test program against generated headers with exceptions disabled")
step("compiles default C++ test program against generated headers with excepti")
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

- compiles optional throwing facade when explicitly enabled
- compiles optional throwing facade when explicitly enabled
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles optional throwing facade when explicitly enabled")
step("compiles optional throwing facade when explicitly enabled")
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

- executes C++ test program and verifies PASS output
- executes C++ test program and verifies PASS output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes C++ test program and verifies PASS output")
step("executes C++ test program and verifies PASS output")
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

- executes optional throwing facade test program
- executes optional throwing facade test program
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes optional throwing facade test program")
step("executes optional throwing facade test program")
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

- verifies destructor does not double-free after move
- verifies destructor does not double-free after move
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verifies destructor does not double-free after move")
step("verifies destructor does not double-free after move")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-DIRECTIONACPPROUNDTRIP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de611835127ce4981057ccf74e7c9e6e7b51042dc988979e261048e304346856`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de611835127ce4981057ccf74e7c9e6e7b51042dc988979e261048e304346856`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de611835127ce4981057ccf74e7c9e6e7b51042dc988979e261048e304346856`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/sffi/direction_a_cpp_roundtrip_spec.spl
mirror: doc/06_spec/integration/sffi/direction_a_cpp_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/sffi/direction_a_cpp_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/sffi/direction_a_cpp_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/sffi/direction_a_cpp_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/sffi/direction_a_cpp_roundtrip_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles Simple library to shared object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/direction_a_cpp_roundtrip_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates both C and C++ headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/direction_a_cpp_roundtrip_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps types in spl namespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
