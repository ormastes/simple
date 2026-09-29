# Direction B: C -> Simple Import Round-Trip Proof

> Purpose: This spec proves Direction B: C -> Simple import round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direction B: C -> Simple Import Round-Trip Proof

Purpose: This spec proves Direction B: C -> Simple import round-trip.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR-WS7 |
| Category | Compiler Integration / SFFI |
| Status | End-to-End Proof |
| Source | `test/integration/sffi/direction_b_import_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Direction B: C -> Simple import round-trip.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Direction B: C -> Simple import round-trip

### C library creation

#### creates a minimal C library with arithmetic functions

- creates a minimal C library with arithmetic functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-DIRECTIONBIMPORTROUNDTRI-001
step("creates a minimal C library with arithmetic functions")
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

- compiles C library to shared object
- compiles C library to shared object
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles C library to shared object")
step("compiles C library to shared object")
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

- creates Simple source that imports the C functions via extern fn
- creates Simple source that imports the C functions via extern fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates Simple source that imports the C functions via extern fn")
step("creates Simple source that imports the C functions via extern fn")
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

- executes Simple source linked against C library
- executes Simple source linked against C library
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes Simple source linked against C library")
step("executes Simple source linked against C library")
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

- creates SDN manifest pointing to library
- creates SDN manifest pointing to library


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates SDN manifest pointing to library")
step("creates SDN manifest pointing to library")
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

- verifies manifest describes the correct function signatures
- verifies manifest describes the correct function signatures


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verifies manifest describes the correct function signatures")
step("verifies manifest describes the correct function signatures")
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

- creates C library with subset of expected functions
- creates C library with subset of expected functions
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates C library with subset of expected functions")
step("creates C library with subset of expected functions")
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

- reports missing symbol when extern fn is not found in library
- reports missing symbol when extern fn is not found in library
   - Expected: "missing symbol link should fail" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports missing symbol when extern fn is not found in library")
step("reports missing symbol when extern fn is not found in library")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-DIRECTIONBIMPORTROUNDTRI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b3067cac7b0a02e82c27d34b9ebb4613e88f10cbcc25bd0423d8b3a56c0b7ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b3067cac7b0a02e82c27d34b9ebb4613e88f10cbcc25bd0423d8b3a56c0b7ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b3067cac7b0a02e82c27d34b9ebb4613e88f10cbcc25bd0423d8b3a56c0b7ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/sffi/direction_b_import_roundtrip_spec.spl
mirror: doc/06_spec/integration/sffi/direction_b_import_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/sffi/direction_b_import_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/sffi/direction_b_import_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/sffi/direction_b_import_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/sffi/direction_b_import_roundtrip_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a minimal C library with arithmetic functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/direction_b_import_roundtrip_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles C library to shared object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/sffi/direction_b_import_roundtrip_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates Simple source that imports the C functions via extern fn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
