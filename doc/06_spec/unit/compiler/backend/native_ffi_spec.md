# native_ffi_spec

> Purpose: Prove that Native FFI File Operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_ffi_spec

Purpose: Prove that Native FFI File Operations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/native_ffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Native FFI File Operations.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Native FFI File Operations

#### file_delete

#### returns boolean

- returns boolean
- Verify: returns boolean
   - Expected: result == true or result == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns boolean")
step("Verify: returns boolean")
# @req: REQ-COMP-NATIVE-FFI-FILE-OPERATIONS-001
val result = file_delete("/tmp/nonexistent_file_xyz")
expect(result == true or result == false).to_equal(true)
```

</details>

#### returns false for non-existent file

- returns false for non-existent file
- Verify: returns false for non-existent file
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-existent file")
step("Verify: returns false for non-existent file")
val result = file_delete("/tmp/nonexistent_file_12345_xyz")
expect(result).to_equal(false)
```

</details>

#### successfully deletes existing file

- successfully deletes existing file
- Verify: successfully deletes existing file
   - Expected: file_exists(temp_path) is true
   - Expected: result is true
   - Expected: file_exists(temp_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("successfully deletes existing file")
step("Verify: successfully deletes existing file")
val temp_path = "/tmp/test_delete_12345.tmp"
file_write(temp_path, "test content")
expect(file_exists(temp_path)).to_equal(true)

val result = file_delete(temp_path)
expect(result).to_equal(true)
expect(file_exists(temp_path)).to_equal(false)
```

</details>

#### handles deletion of already deleted file

- handles deletion of already deleted file
- Verify: handles deletion of already deleted file
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles deletion of already deleted file")
step("Verify: handles deletion of already deleted file")
val temp_path = "/tmp/test_delete_twice_12345.tmp"
file_write(temp_path, "test")
file_delete(temp_path)

val result = file_delete(temp_path)
expect(result).to_equal(false)
```

</details>

#### handles empty path

- handles empty path
- Verify: handles empty path
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty path")
step("Verify: handles empty path")
val result = file_delete("")
expect(result).to_equal(false)
```

</details>

#### handles path with special characters

- handles path with special characters
- Verify: handles path with special characters
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles path with special characters")
step("Verify: handles path with special characters")
val temp_path = "/tmp/test file with spaces.tmp"
file_write(temp_path, "test")

val result = file_delete(temp_path)
expect(result).to_equal(true)
```

</details>

#### write and read round-trip

#### writes then reads back same content

- writes then reads back same content
- Verify: writes then reads back same content
   - Expected: read_back equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes then reads back same content")
step("Verify: writes then reads back same content")
val temp_path = "/tmp/test_roundtrip_ffi.tmp"
val content = "Hello, FFI round-trip test!"
file_write(temp_path, content)

val read_back = file_read(temp_path)
expect(read_back).to_equal(content)

file_delete(temp_path)
```

</details>

#### handles large content

- handles large content
- Verify: handles large content
   - Expected: file_exists(temp_path) is true
   - Expected: result is true
   - Expected: file_exists(temp_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large content")
step("Verify: handles large content")
val temp_path = "/tmp/test_large_ffi.tmp"
var content = ""
var idx = 0
while idx < 100:
    content = content + "Line: This is test content for large file write.\n"
    idx = idx + 1

file_write(temp_path, content)
expect(file_exists(temp_path)).to_equal(true)

val result = file_delete(temp_path)
expect(result).to_equal(true)
expect(file_exists(temp_path)).to_equal(false)
```

</details>

#### sequential file operations

#### handles multiple sequential creates and deletes

- handles multiple sequential creates and deletes
- Verify: handles multiple sequential creates and deletes
   - Expected: file_exists(temp1) is true
   - Expected: file_exists(temp2) is true
   - Expected: file_delete(temp1) is true
   - Expected: file_delete(temp2) is true
   - Expected: file_exists(temp1) is false
   - Expected: file_exists(temp2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple sequential creates and deletes")
step("Verify: handles multiple sequential creates and deletes")
val temp1 = "/tmp/test_seq_1.tmp"
val temp2 = "/tmp/test_seq_2.tmp"

file_write(temp1, "content1")
file_write(temp2, "content2")

expect(file_exists(temp1)).to_equal(true)
expect(file_exists(temp2)).to_equal(true)

expect(file_delete(temp1)).to_equal(true)
expect(file_delete(temp2)).to_equal(true)

expect(file_exists(temp1)).to_equal(false)
expect(file_exists(temp2)).to_equal(false)
```

</details>

#### handles create-delete-recreate cycle

- handles create-delete-recreate cycle
- Verify: handles create-delete-recreate cycle
   - Expected: file_exists(temp_path) is true
   - Expected: file_exists(temp_path) is false
   - Expected: file_exists(temp_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles create-delete-recreate cycle")
step("Verify: handles create-delete-recreate cycle")
val temp_path = "/tmp/test_cycle_ffi.tmp"

file_write(temp_path, "first")
expect(file_exists(temp_path)).to_equal(true)

file_delete(temp_path)
expect(file_exists(temp_path)).to_equal(false)

file_write(temp_path, "second")
expect(file_exists(temp_path)).to_equal(true)

file_delete(temp_path)
```

</details>

### Native FFI Compilation

#### returns false for non-existent source file

- returns false for non-existent source file
- Verify: returns false for non-existent source file
   - Expected: success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-existent source file")
step("Verify: returns false for non-existent source file")
val _result = rt_compile_to_native("/nonexistent/file.spl", "out")
val success = _result[0]
expect(success).to_equal(false)
```

</details>

#### handles empty paths gracefully

- handles empty paths gracefully
- Verify: handles empty paths gracefully
   - Expected: success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty paths gracefully")
step("Verify: handles empty paths gracefully")
val _result = rt_compile_to_native("", "")
val success = _result[0]
expect(success).to_equal(false)
```

</details>

#### returns error for invalid source path

- returns error for invalid source path
- Verify: returns error for invalid source path
   - Expected: success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for invalid source path")
step("Verify: returns error for invalid source path")
val _result = rt_compile_to_native("/invalid/path/file.spl", "output")
val success = _result[0]
expect(success).to_equal(false)
```

</details>

### Native FFI Execution

#### returns tuple with stdout, stderr, and exit code

- returns tuple with stdout, stderr, and exit code
- Verify: returns tuple with stdout, stderr, and exit code
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns tuple with stdout, stderr, and exit code")
step("Verify: returns tuple with stdout, stderr, and exit code")
val _result = rt_execute_native("/bin/echo", ["hello"], 5000)
val stdout = _result[0]
val code = _result[2]
expect(stdout).to_contain("hello")
expect(code).to_equal(0)
```

</details>

#### returns error for non-existent binary

- returns error for non-existent binary
- Verify: returns error for non-existent binary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for non-existent binary")
step("Verify: returns error for non-existent binary")
val _result = rt_execute_native("/nonexistent/binary", [], 5000)
val code = _result[2]
expect(code).to_be_greater_than(0)
```

</details>

#### respects timeout

- respects timeout
- Verify: respects timeout
   - Expected: code equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects timeout")
step("Verify: respects timeout")
val _result = rt_execute_native("/bin/sleep", ["10"], 100)
val code = _result[2]
expect(code).to_equal(124)
```

</details>

#### passes arguments correctly

- passes arguments correctly
- Verify: passes arguments correctly
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes arguments correctly")
step("Verify: passes arguments correctly")
val _result = rt_execute_native("/bin/echo", ["arg1", "arg2"], 5000)
val stdout = _result[0]
val code = _result[2]
expect(stdout).to_contain("arg1")
expect(stdout).to_contain("arg2")
expect(code).to_equal(0)
```

</details>

#### captures stderr separately

- captures stderr separately
- Verify: captures stderr separately
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures stderr separately")
step("Verify: captures stderr separately")
val _result = rt_execute_native("/bin/sh", ["-c", "echo error >&2"], 5000)
val code = _result[2]
expect(code).to_equal(0)
```

</details>

#### handles empty argument list

- handles empty argument list
- Verify: handles empty argument list
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty argument list")
step("Verify: handles empty argument list")
val _result = rt_execute_native("/bin/true", [], 5000)
val code = _result[2]
expect(code).to_equal(0)
```

</details>

### Native Execution Error Handling

#### handles zero timeout

- handles zero timeout
- Verify: handles zero timeout
   - Expected: code equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero timeout")
step("Verify: handles zero timeout")
val _result = rt_execute_native("/bin/sleep", ["10"], 0)
val code = _result[2]
expect(code).to_equal(124)
```

</details>

#### handles negative timeout

- handles negative timeout
- Verify: handles negative timeout
   - Expected: code == 0 or code == 124 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles negative timeout")
step("Verify: handles negative timeout")
val _result = rt_execute_native("/bin/true", [], -1)
val code = _result[2]
expect(code == 0 or code == 124).to_equal(true)
```

</details>

### Performance Characteristics

<details>
<summary>Advanced: executes simple binary quickly</summary>

#### executes simple binary quickly _(slow)_

- executes simple binary quickly
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes simple binary quickly")
val start_us = rt_time_now_unix_micros()
val _result = rt_execute_native("/bin/true", [], 5000)
val end_us = rt_time_now_unix_micros()
val duration_ms = (end_us - start_us) / 1000
val code = _result[2]

expect(code).to_equal(0)
expect(duration_ms).to_be_less_than(500)
```

</details>


</details>

<details>
<summary>Advanced: handles sequential executions</summary>

#### handles sequential executions _(slow)_

- handles sequential executions
   - Expected: all_succeeded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles sequential executions")
var all_succeeded = true
var idx = 0
while idx < 5:
    val _result = rt_execute_native("/bin/echo", ["test"], 5000)
    val code = _result[2]
    if code != 0:
        all_succeeded = false
    idx = idx + 1

expect(all_succeeded).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-NATIVE-FFI-FILE-OPERATIONS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `66d75042a442bc117d9998afcbf6d74dd26b84e3d33ef6f55ef8b62bc1d9050a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66d75042a442bc117d9998afcbf6d74dd26b84e3d33ef6f55ef8b62bc1d9050a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66d75042a442bc117d9998afcbf6d74dd26b84e3d33ef6f55ef8b62bc1d9050a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/native_ffi_spec.spl
mirror: doc/06_spec/unit/compiler/backend/native_ffi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/native_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/native_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/native_ffi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/native_ffi_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns boolean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/native_ffi_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for non-existent file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/native_ffi_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'successfully deletes existing file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
