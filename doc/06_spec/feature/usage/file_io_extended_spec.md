# Extended File I/O Specification

> Extended File I/O operations including line-based reading, append operations,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extended File I/O Specification

Extended File I/O operations including line-based reading, append operations,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #700-715 |
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/feature/usage/file_io_extended_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Extended File I/O operations including line-based reading, append operations,
binary I/O, file moving, recursive directory operations, and path utilities.

Self-contained: all I/O functions defined inline via extern fn declarations.

## Scenarios

### read_lines

#### reads multiple lines correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads multiple lines correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reads multiple lines correctly")
val test_path = "/tmp/simple_test_multiline.txt"
val content = "line1\nline2\nline3"
write_file(test_path, content)

val result = read_lines(test_path)
expect result.is_ok() == true

match result:
    Ok(lines):
        expect lines[0] == "line1"
        expect lines.len() == 3
        expect lines[1] == "line2"
        expect lines[2] == "line3"
    Err(_):
        fail("Should have read lines successfully")

remove_file(test_path)
```

</details>

#### reads empty file as empty list

- reads empty file as empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reads empty file as empty list")
val test_path = "/tmp/simple_test_empty_lines.txt"
write_file(test_path, "")

val result = read_lines(test_path)
expect result.is_ok() == true

match result:
    Ok(lines):
        expect lines.len() == 0
    Err(_):
        fail("Should have read empty file")

remove_file(test_path)
```

</details>

### append_file

#### appends to existing file

- appends to existing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("appends to existing file")
val test_path = "/tmp/simple_test_append.txt"
write_file(test_path, "Hello")

val result = append_file(test_path, ", World!")
expect result.is_ok() == true

val content = read_file(test_path)
match content:
    Ok(text):
        expect text == "Hello, World!"
    Err(_):
        fail("Should have read appended file")

remove_file(test_path)
```

</details>

#### creates file if not exists

- creates file if not exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates file if not exists")
val test_path = "/tmp/simple_test_append_new.txt"

if file_exist(test_path):
    remove_file(test_path)

val result = append_file(test_path, "New content")
expect result.is_ok() == true
expect file_exist(test_path) == true

val content = read_file(test_path)
match content:
    Ok(text):
        expect text == "New content"
    Err(_):
        fail("Should have read new file")

remove_file(test_path)
```

</details>

### binary I/O

#### preserves binary data exactly

- preserves binary data exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves binary data exactly")
val test_path = "/tmp/simple_test_binary.bin"
val data = [0, 127, 255, 1, 128]

val write_result = write_bytes(test_path, data)
expect write_result.is_ok() == true

val read_result = read_bytes(test_path)
expect read_result.is_ok() == true

match read_result:
    Ok(bytes):
        expect bytes[0] == 0
        expect bytes.len() == 5
        expect bytes[1] == 127
        expect bytes[2] == 255
        expect bytes[3] == 1
        expect bytes[4] == 128
    Err(_):
        fail("Should have read bytes")

remove_file(test_path)
```

</details>

### move_file

#### moves file to new location

- moves file to new location


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("moves file to new location")
val src_path = "/tmp/simple_test_move_src.txt"
val dest_path = "/tmp/simple_test_move_dest.txt"
write_file(src_path, "content to move")

if file_exist(dest_path):
    remove_file(dest_path)

val result = move_file(src_path, dest_path)
expect result.is_ok() == true
expect file_exist(src_path) == false
expect file_exist(dest_path) == true

val content = read_file(dest_path)
match content:
    Ok(text):
        expect text == "content to move"
    Err(_):
        fail("Should read moved file")

remove_file(dest_path)
```

</details>

### create_dir_all

#### creates nested directories

- creates nested directories


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates nested directories")
val nested_path = "/tmp/simple_test_nested/a/b/c"

val result = create_dir_all(nested_path)
expect result.is_ok() == true
expect file_exist(nested_path) == true

# Cleanup
remove_dir("/tmp/simple_test_nested/a/b/c")
remove_dir("/tmp/simple_test_nested/a/b")
remove_dir("/tmp/simple_test_nested/a")
remove_dir("/tmp/simple_test_nested")
```

</details>

### walk_dir

#### returns all files recursively

- returns all files recursively


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns all files recursively")
val base = "/tmp/simple_test_walk"
create_dir_all(base)
write_file(base + "/file1.txt", "1")
create_dir(base + "/sub")
write_file(base + "/sub/file2.txt", "2")

val result = walk_dir(base)
expect result.is_ok() == true

match result:
    Ok(entries):
        expect entries.len() >= 3
    Err(_):
        fail("Should walk directory")

# Cleanup
remove_file(base + "/sub/file2.txt")
remove_dir(base + "/sub")
remove_file(base + "/file1.txt")
remove_dir(base)
```

</details>

### current_dir and set_current_dir

#### gets absolute path

- gets absolute path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("gets absolute path")
val cwd = current_dir()
expect cwd.len() > 0
expect cwd.starts_with("/") == true
```

</details>

### remove_dir_all

#### removes directory and contents

- removes directory and contents


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("removes directory and contents")
val base = "/tmp/simple_test_rmall"
create_dir_all(base + "/sub/deep")
write_file(base + "/file.txt", "content")
write_file(base + "/sub/file2.txt", "content2")

val result = remove_dir_all(base)
expect result.is_ok() == true
expect file_exist(base) == false
```

</details>

### stem

#### extracts filename without extension

- extracts filename without extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("extracts filename without extension")
expect stem("file.txt") == "file"
```

</details>

#### handles multiple dots

- handles multiple dots


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles multiple dots")
expect stem("archive.tar.gz") == "archive.tar"
```

</details>

#### handles no extension

- handles no extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles no extension")
expect stem("README") == "README"
```

</details>

### relative_path

#### computes relative path

- computes relative path


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes relative path")
expect relative_path("/a/b/c/file.txt", "/a/b") == "c/file.txt"
```

</details>

#### handles same path

- handles same path


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles same path")
expect relative_path("/a/b", "/a/b") == ""
```

</details>

### path_join

#### joins two paths

- joins two paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins two paths")
expect path_join("/home/user", "file.txt") == "/home/user/file.txt"
```

</details>

### Error Handling

#### read_lines fails for non-existent file

- read_lines fails for non-existent file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("read_lines fails for non-existent file")
val result = read_lines("/tmp/nonexistent_file_12345.txt")
expect result.is_err() == true
```

</details>

#### read_bytes fails for non-existent file

- read_bytes fails for non-existent file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("read_bytes fails for non-existent file")
val result = read_bytes("/tmp/nonexistent_file_12345.bin")
expect result.is_err() == true
```

</details>

#### move_file fails for non-existent source

- move_file fails for non-existent source


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("move_file fails for non-existent source")
val result = move_file("/tmp/nonexistent_12345.txt", "/tmp/dest.txt")
expect result.is_err() == true
```

</details>

#### walk_dir fails for non-existent directory

- walk_dir fails for non-existent directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("walk_dir fails for non-existent directory")
val result = walk_dir("/tmp/nonexistent_dir_12345")
expect result.is_err() == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca296bb184cefe3953d733c37ef87398411710ec45f17760cc672c4fe1e345ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca296bb184cefe3953d733c37ef87398411710ec45f17760cc672c4fe1e345ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca296bb184cefe3953d733c37ef87398411710ec45f17760cc672c4fe1e345ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/file_io_extended_spec.spl
mirror: doc/06_spec/feature/usage/file_io_extended_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/file_io_extended_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/file_io_extended_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/file_io_extended_spec.spl:229:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads multiple lines correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/file_io_extended_spec.spl:250:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads empty file as empty list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/file_io_extended_spec.spl:276:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends to existing file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
