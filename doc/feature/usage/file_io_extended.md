# Extended File I/O Specification
*Source:* `test/feature/usage/file_io_extended_spec.spl`
**Feature IDs:** #700-715  |  **Category:** Infrastructure  |  **Status:** Implemented

## Overview



Extended File I/O operations including line-based reading, append operations,
binary I/O, file moving, recursive directory operations, and path utilities.

## Feature: read_lines

Verifies line-based file reading that returns content as a list of strings,
    splitting on newline characters. Handles both multi-line content and empty
    files (returning an empty list).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | reads multiple lines correctly | pass |
| 2 | reads empty file as empty list | pass |

**Example:** reads multiple lines correctly
    Given val test_path = "/tmp/simple_test_multiline.txt"
    Given val content = "line1{NL}line2{NL}line3"
    Given val result = read_lines(test_path)
    Then  expect result.is_ok() == true
    Then  expect lines.len() == 3
    Then  expect lines[0] == "line1"
    Then  expect lines[1] == "line2"
    Then  expect lines[2] == "line3"

**Example:** reads empty file as empty list
    Given val test_path = "/tmp/simple_test_empty_lines.txt"
    Given val result = read_lines(test_path)
    Then  expect result.is_ok() == true
    Then  expect lines.len() == 0

## Feature: append_file

Verifies file append operations that add content to the end of existing
    files or create new files if they don't exist. This enables log-style
    writing and incremental file building.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | appends to existing file | pass |
| 2 | creates file if not exists | pass |

**Example:** appends to existing file
    Given val test_path = "/tmp/simple_test_append.txt"
    Given val result = append_file(test_path, ", World!")
    Then  expect result.is_ok() == true
    Given val content = read_file(test_path)
    Then  expect text == "Hello, World!"

**Example:** creates file if not exists
    Given val test_path = "/tmp/simple_test_append_new.txt"
    Given val result = append_file(test_path, "New content")
    Then  expect result.is_ok() == true
    Then  expect file_exist(test_path) == true
    Given val content = read_file(test_path)
    Then  expect text == "New content"

## Feature: binary I/O

Verifies binary file I/O operations (read_bytes and write_bytes) that
    handle raw byte arrays without text encoding/decoding. Critical for
    working with non-text files like images, executables, and data files.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | preserves binary data exactly | pass |

**Example:** preserves binary data exactly
    Given val test_path = "/tmp/simple_test_binary.bin"
    Given val data = [0, 127, 255, 1, 128]
    Given val write_result = write_bytes(test_path, data)
    Then  expect write_result.is_ok() == true
    Given val read_result = read_bytes(test_path)
    Then  expect read_result.is_ok() == true
    Then  expect bytes.len() == 5
    Then  expect bytes[0] == 0
    Then  expect bytes[1] == 127
    Then  expect bytes[2] == 255
    Then  expect bytes[3] == 1
    Then  expect bytes[4] == 128

## Feature: move_file

Verifies file move operations that atomically relocate a file from source
    to destination path. The source file is removed after successful move.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | moves file to new location | pass |

**Example:** moves file to new location
    Given val src_path = "/tmp/simple_test_move_src.txt"
    Given val dest_path = "/tmp/simple_test_move_dest.txt"
    Given val result = move_file(src_path, dest_path)
    Then  expect result.is_ok() == true
    Then  expect file_exist(src_path) == false
    Then  expect file_exist(dest_path) == true
    Given val content = read_file(dest_path)
    Then  expect text == "content to move"

## Feature: create_dir_all

Verifies recursive directory creation that creates all missing parent
    directories in a path. Similar to `mkdir -p` in shell.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates nested directories | pass |

**Example:** creates nested directories
    Given val nested_path = "/tmp/simple_test_nested/a/b/c"
    Given val result = create_dir_all(nested_path)
    Then  expect result.is_ok() == true
    Then  expect file_exist(nested_path) == true

## Feature: walk_dir

Verifies recursive directory traversal that returns all files and
    subdirectories under a given path. Useful for file discovery and
    batch operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns all files recursively | pass |

**Example:** returns all files recursively
    Given val base = "/tmp/simple_test_walk"
    Given val result = walk_dir(base)
    Then  expect result.is_ok() == true
    Then  expect entries.len() >= 3

## Feature: current_dir and set_current_dir

Verifies working directory operations that get and set the current
    working directory. Returns absolute paths for reliable path resolution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | gets absolute path | pass |

**Example:** gets absolute path
    Given val cwd = current_dir()
    Then  expect cwd.len() > 0
    Then  expect cwd.starts_with("/") == true

## Feature: remove_dir_all

Verifies recursive directory removal that deletes a directory and all
    its contents (files and subdirectories). Similar to `rm -rf` in shell.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | removes directory and contents | pass |

**Example:** removes directory and contents
    Given val base = "/tmp/simple_test_rmall"
    Given val result = remove_dir_all(base)
    Then  expect result.is_ok() == true
    Then  expect file_exist(base) == false

## Feature: stem

Verifies path stem extraction that returns the filename without its
    extension. Handles multiple dots and files without extensions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | extracts filename without extension | pass |
| 2 | handles multiple dots | pass |
| 3 | handles no extension | pass |

**Example:** extracts filename without extension
    Then  expect stem("file.txt") == "file"

**Example:** handles multiple dots
    Then  expect stem("archive.tar.gz") == "archive.tar"

**Example:** handles no extension
    Then  expect stem("README") == "README"

## Feature: relative_path

Verifies relative path computation that calculates the path from a base
    directory to a target path. Returns empty string when paths are identical.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | computes relative path | pass |
| 2 | handles same path | pass |

**Example:** computes relative path
    Then  expect relative_path("/a/b/c/file.txt", "/a/b") == "c/file.txt"

**Example:** handles same path
    Then  expect relative_path("/a/b", "/a/b") == ""

## Feature: path_join

Verifies path joining that combines directory and file components into
    a complete path, handling separator insertion correctly.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | joins two paths | pass |

**Example:** joins two paths
    Then  expect path_join("/home/user", "file.txt") == "/home/user/file.txt"

## Feature: Error Handling

Verifies proper error propagation for file I/O operations when files
    or directories don't exist. All operations return Result types that
    indicate failure with meaningful error information.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | read_lines fails for non-existent file | pass |
| 2 | read_bytes fails for non-existent file | pass |
| 3 | move_file fails for non-existent source | pass |
| 4 | walk_dir fails for non-existent directory | pass |

**Example:** read_lines fails for non-existent file
    Given val result = read_lines("/tmp/nonexistent_file_12345.txt")
    Then  expect result.is_err() == true

**Example:** read_bytes fails for non-existent file
    Given val result = read_bytes("/tmp/nonexistent_file_12345.bin")
    Then  expect result.is_err() == true

**Example:** move_file fails for non-existent source
    Given val result = move_file("/tmp/nonexistent_12345.txt", "/tmp/dest.txt")
    Then  expect result.is_err() == true

**Example:** walk_dir fails for non-existent directory
    Given val result = walk_dir("/tmp/nonexistent_dir_12345")
    Then  expect result.is_err() == true


