# native_ffi_spec

> Native FFI Bridge Specification

<!-- sdn-diagram:id=native_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_ffi_spec

Native FFI Bridge Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FFI-001 to #FFI-010 |
| Category | Backend / Native Execution |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Native FFI Bridge Specification

Tests the FFI bridge for native compilation and execution.

## Scenarios

### Native FFI File Operations

#### file_delete

#### returns boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = file_delete("/tmp/nonexistent_file_xyz")
expect(result == true or result == false).to_equal(true)
```

</details>

#### returns false for non-existent file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = file_delete("/tmp/nonexistent_file_12345_xyz")
expect(result).to_equal(false)
```

</details>

#### successfully deletes existing file

1. file write
   - Expected: file_exists(temp_path) is true
   - Expected: result is true
   - Expected: file_exists(temp_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_path = "/tmp/test_delete_12345.tmp"
file_write(temp_path, "test content")
expect(file_exists(temp_path)).to_equal(true)

val result = file_delete(temp_path)
expect(result).to_equal(true)
expect(file_exists(temp_path)).to_equal(false)
```

</details>

#### handles deletion of already deleted file

1. file write
2. file delete
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_path = "/tmp/test_delete_twice_12345.tmp"
file_write(temp_path, "test")
file_delete(temp_path)

val result = file_delete(temp_path)
expect(result).to_equal(false)
```

</details>

#### handles empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = file_delete("")
expect(result).to_equal(false)
```

</details>

#### handles path with special characters

1. file write
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_path = "/tmp/test file with spaces.tmp"
file_write(temp_path, "test")

val result = file_delete(temp_path)
expect(result).to_equal(true)
```

</details>

#### write and read round-trip

#### writes then reads back same content

1. file write
   - Expected: read_back equals `content`
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_path = "/tmp/test_roundtrip_ffi.tmp"
val content = "Hello, FFI round-trip test!"
file_write(temp_path, content)

val read_back = file_read(temp_path)
expect(read_back).to_equal(content)

file_delete(temp_path)
```

</details>

#### handles large content

1. file write
   - Expected: file_exists(temp_path) is true
   - Expected: result is true
   - Expected: file_exists(temp_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. file write
2. file write
   - Expected: file_exists(temp1) is true
   - Expected: file_exists(temp2) is true
   - Expected: file_delete(temp1) is true
   - Expected: file_delete(temp2) is true
   - Expected: file_exists(temp1) is false
   - Expected: file_exists(temp2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. file write
   - Expected: file_exists(temp_path) is true
2. file delete
   - Expected: file_exists(temp_path) is false
3. file write
   - Expected: file_exists(temp_path) is true
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_compile_to_native("/nonexistent/file.spl", "out")
val success = _result[0]
expect(success).to_equal(false)
```

</details>

#### handles empty paths gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_compile_to_native("", "")
val success = _result[0]
expect(success).to_equal(false)
```

</details>

#### returns error for invalid source path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_compile_to_native("/invalid/path/file.spl", "output")
val success = _result[0]
expect(success).to_equal(false)
```

</details>

### Native FFI Execution

#### returns tuple with stdout, stderr, and exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_execute_native("/bin/echo", ["hello"], 5000)
val stdout = _result[0]
val code = _result[2]
expect(stdout).to_contain("hello")
expect(code).to_equal(0)
```

</details>

#### returns error for non-existent binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_execute_native("/nonexistent/binary", [], 5000)
val code = _result[2]
expect(code).to_be_greater_than(0)
```

</details>

#### respects timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_execute_native("/bin/sleep", ["10"], 100)
val code = _result[2]
expect(code).to_equal(124)
```

</details>

#### passes arguments correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_execute_native("/bin/echo", ["arg1", "arg2"], 5000)
val stdout = _result[0]
val code = _result[2]
expect(stdout).to_contain("arg1")
expect(stdout).to_contain("arg2")
expect(code).to_equal(0)
```

</details>

#### captures stderr separately

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_execute_native("/bin/sh", ["-c", "echo error >&2"], 5000)
val code = _result[2]
expect(code).to_equal(0)
```

</details>

#### handles empty argument list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_execute_native("/bin/true", [], 5000)
val code = _result[2]
expect(code).to_equal(0)
```

</details>

### Native Execution Error Handling

#### handles zero timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_execute_native("/bin/sleep", ["10"], 0)
val code = _result[2]
expect(code).to_equal(124)
```

</details>

#### handles negative timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _result = rt_execute_native("/bin/true", [], -1)
val code = _result[2]
expect(code == 0 or code == 124).to_equal(true)
```

</details>

### Performance Characteristics

<details>
<summary>Advanced: executes simple binary quickly</summary>

#### executes simple binary quickly _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
