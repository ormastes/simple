# Extended File I/O Specification

> Extended File I/O operations including line-based reading, append operations,

<!-- sdn-diagram:id=file_io_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_io_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_io_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_io_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/file_io_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Extended File I/O operations including line-based reading, append operations,
binary I/O, file moving, recursive directory operations, and path utilities.

Self-contained: all I/O functions defined inline via extern fn declarations.

## Scenarios

### read_lines

#### reads multiple lines correctly

1. write file
2. expect result is ok
3. Ok
4. expect lines len
5. Err
6. fail
7. remove file


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. write file
2. expect result is ok
3. Ok
4. expect lines len
5. Err
6. fail
7. remove file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. write file
2. expect result is ok
3. Ok
4. Err
5. fail
6. remove file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. remove file
2. expect result is ok
3. expect file exist
4. Ok
5. Err
6. fail
7. remove file


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect write result is ok
2. expect read result is ok
3. Ok
4. expect bytes len
5. Err
6. fail
7. remove file


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. write file
2. remove file
3. expect result is ok
4. expect file exist
5. expect file exist
6. Ok
7. Err
8. fail
9. remove file


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect result is ok
2. expect file exist
3. remove dir
4. remove dir
5. remove dir
6. remove dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. create dir all
2. write file
3. create dir
4. write file
5. expect result is ok
6. Ok
7. expect entries len
8. Err
9. fail
10. remove file
11. remove dir
12. remove file
13. remove dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect cwd len
2. expect cwd starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cwd = current_dir()
expect cwd.len() > 0
expect cwd.starts_with("/") == true
```

</details>

### remove_dir_all

#### removes directory and contents

1. create dir all
2. write file
3. write file
4. expect result is ok
5. expect file exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect stem


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect stem("file.txt") == "file"
```

</details>

#### handles multiple dots

1. expect stem


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect stem("archive.tar.gz") == "archive.tar"
```

</details>

#### handles no extension

1. expect stem


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect stem("README") == "README"
```

</details>

### relative_path

#### computes relative path

1. expect relative path


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect relative_path("/a/b/c/file.txt", "/a/b") == "c/file.txt"
```

</details>

#### handles same path

1. expect relative path


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect relative_path("/a/b", "/a/b") == ""
```

</details>

### path_join

#### joins two paths

1. expect path join


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect path_join("/home/user", "file.txt") == "/home/user/file.txt"
```

</details>

### Error Handling

#### read_lines fails for non-existent file

1. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_lines("/tmp/nonexistent_file_12345.txt")
expect result.is_err() == true
```

</details>

#### read_bytes fails for non-existent file

1. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = read_bytes("/tmp/nonexistent_file_12345.bin")
expect result.is_err() == true
```

</details>

#### move_file fails for non-existent source

1. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = move_file("/tmp/nonexistent_12345.txt", "/tmp/dest.txt")
expect result.is_err() == true
```

</details>

#### walk_dir fails for non-existent directory

1. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
