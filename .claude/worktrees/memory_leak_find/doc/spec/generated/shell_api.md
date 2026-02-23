# Shell API Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/shell_api_spec.spl`
> **Generated:** 2026-01-10 04:47:40
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/shell_api_spec.spl
> ```

**Status:** Implementing
**Feature IDs:** #900-905
**Keywords:** shell, process, filesystem, io, scripting
**Topics:** stdlib, scripting

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (8 tests)
- [Source Code](#source-code)

## Overview

Shell API provides access to system operations commonly used in shell scripts:
- Process execution with output capture
- File system operations (read, write, list, delete)
- Path manipulation
- Environment variables
- Exit codes and error handling

This API enables writing shell scripts in Simple language, replacing Python and Bash scripts.

## Related Specifications

- **File I/O** - File operations
- **Process Management** - Process control
- **Error Handling** - Result types

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `All` | [3](#list_directory) |
| `Append` | [2](#read_file_contents) |
| `Can` | [6](#command_failure_result) |
| `Capture` | [1](#execute_command_basic) |
| `Chain` | [7](#pipe_commands) |
| `Check` | [2](#read_file_contents) |
| `Command` | [1](#execute_command_basic), [6](#command_failure_result) |
| `CommandFailureResult` | [6](#command_failure_result) |
| `Commands` | [7](#pipe_commands) |
| `Contents` | [2](#read_file_contents) |
| `Convert` | [4](#join_paths) |
| `Copy` | [8](#find_files_recursive) |
| `Create` | [3](#list_directory) |
| `Directory` | [3](#list_directory) |
| `Environment` | [5](#get_environment_variable) |
| `Error` | [6](#command_failure_result) |
| `Execute` | [1](#execute_command_basic) |
| `ExecuteCommand` | [1](#execute_command_basic) |
| `Extract` | [4](#join_paths) |
| `Failed` | [6](#command_failure_result) |
| `Failure` | [6](#command_failure_result) |
| `File` | [2](#read_file_contents), [6](#command_failure_result) |
| `Files` | [8](#find_files_recursive) |
| `Find` | [8](#find_files_recursive) |
| `FindFilesRecursive` | [8](#find_files_recursive) |
| `Get` | [5](#get_environment_variable) |
| `GetEnvironmentVariable` | [5](#get_environment_variable) |
| `HOME` | [5](#get_environment_variable) |
| `Join` | [4](#join_paths) |
| `JoinPaths` | [4](#join_paths) |
| `List` | [3](#list_directory) |
| `ListDirectory` | [3](#list_directory) |
| `Move` | [8](#find_files_recursive) |
| `Paths` | [4](#join_paths) |
| `Pipe` | [7](#pipe_commands) |
| `PipeCommands` | [7](#pipe_commands) |
| `Read` | [2](#read_file_contents), [5](#get_environment_variable) |
| `ReadFileContents` | [2](#read_file_contents) |
| `Recursive` | [8](#find_files_recursive) |
| `Remove` | [3](#list_directory) |
| `Result` | [6](#command_failure_result) |
| `Returns` | [3](#list_directory) |
| `Set` | [5](#get_environment_variable) |
| `This` | [6](#command_failure_result) |
| `Variable` | [5](#get_environment_variable) |
| `Write` | [2](#read_file_contents) |
| `absolute` | [4](#join_paths) |
| `all` | [3](#list_directory), [8](#find_files_recursive) |
| `append_text` | [2](#read_file_contents) |
| `basename` | [4](#join_paths) |
| `command` | [1](#execute_command_basic), [6](#command_failure_result) |
| `command_failure_result` | [6](#command_failure_result) |
| `commands` | [7](#pipe_commands) |
| `contains` | [1](#execute_command_basic), [2](#read_file_contents) |
| `contents` | [2](#read_file_contents) |
| `copy` | [8](#find_files_recursive) |
| `create` | [3](#list_directory) |
| `directory` | [3](#list_directory) |
| `dirname` | [4](#join_paths) |
| `ends_with` | [3](#list_directory), [8](#find_files_recursive) |
| `environment` | [5](#get_environment_variable) |
| `execute` | [1](#execute_command_basic) |
| `execute_command` | [1](#execute_command_basic) |
| `exists` | [2](#read_file_contents), [3](#list_directory), [8](#find_files_recursive) |
| `ext` | [4](#join_paths) |
| `failure` | [6](#command_failure_result) |
| `file` | [2](#read_file_contents) |
| `files` | [8](#find_files_recursive) |
| `filter` | [7](#pipe_commands) |
| `find` | [8](#find_files_recursive) |
| `find_files_recursive` | [8](#find_files_recursive) |
| `get` | [5](#get_environment_variable) |
| `get_environment_variable` | [5](#get_environment_variable) |
| `glob` | [3](#list_directory) |
| `is_err` | [6](#command_failure_result) |
| `join` | [4](#join_paths) |
| `join_paths` | [4](#join_paths) |
| `len` | [2](#read_file_contents), [3](#list_directory), [5](#get_environment_variable), [7](#pipe_commands) |
| `list` | [3](#list_directory) |
| `list_directory` | [3](#list_directory) |
| `move` | [8](#find_files_recursive) |
| `paths` | [4](#join_paths) |
| `pipe` | [7](#pipe_commands) |
| `pipe_commands` | [7](#pipe_commands) |
| `read` | [2](#read_file_contents) |
| `read_file_contents` | [2](#read_file_contents) |
| `read_text` | [2](#read_file_contents), [6](#command_failure_result), [7](#pipe_commands), [8](#find_files_recursive) |
| `recursive` | [8](#find_files_recursive) |
| `remove` | [3](#list_directory) |
| `result` | [6](#command_failure_result) |
| `run` | [1](#execute_command_basic), [5](#get_environment_variable), [6](#command_failure_result) |
| `safely` | [1](#execute_command_basic) |
| `set` | [5](#get_environment_variable) |
| `split` | [7](#pipe_commands) |
| `starts_with` | [4](#join_paths) |
| `trim` | [5](#get_environment_variable), [7](#pipe_commands) |
| `variable` | [5](#get_environment_variable) |
| `write_text` | [2](#read_file_contents), [7](#pipe_commands), [8](#find_files_recursive) |

---

## Test Cases (8 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [execute_command_basic](#execute_command_basic) | Process Execution | `execute_command`, `command`, `Execute` +7 |
| 2 | [read_file_contents](#read_file_contents) | File Operations | `read_file_contents`, `file`, `contents` +14 |
| 3 | [list_directory](#list_directory) | Directory Operations | `directory`, `list`, `list_directory` +14 |
| 4 | [join_paths](#join_paths) | Path Operations | `JoinPaths`, `Join`, `join` +10 |
| 5 | [get_environment_variable](#get_environment_variable) | Environment Variables | `variable`, `get`, `Variable` +12 |
| 6 | [command_failure_result](#command_failure_result) | Error Handling | `command`, `failure`, `command_failure_result` +13 |
| 7 | [pipe_commands](#pipe_commands) | Piping and Chaining | `pipe_commands`, `pipe`, `PipeCommands` +10 |
| 8 | [find_files_recursive](#find_files_recursive) | Script Utilities | `find_files_recursive`, `recursive`, `FindFilesRecursive` +14 |

---

### Test 1: Process Execution {#execute_command_basic}

**Test name:** `execute_command_basic`

**Description:**

### Scenario: Execute command and capture output

Shell scripts frequently need to run commands and capture their output.
The API should make this simple and handle errors gracefully.

**Linked Symbols:**
- `execute_command`
- `command`
- `Execute`
- `ExecuteCommand`
- `Command`
- `execute`
- `contains`
- `Capture`
- `safely`
- `run`

**Code:**

```simple
test "execute_command_basic":
    """
    Execute a simple command and get output as string.
    """
    let result = shell.run("echo hello")
    assert result.ok()
    assert result.stdout == "hello\n"
    assert result.exit_code == 0

test "execute_command_with_args":
    """
    Execute command with arguments safely (no shell injection).
    """
    let result = shell.run("ls", ["-la", "/tmp"])
    assert result.ok()
    assert result.stdout.contains("total")

test "execute_command_capture_stderr":
    """
    Capture both stdout and stderr separately.
    """
    let result = shell.run("ls /nonexistent")
    assert not result.ok()
    assert result.stderr.contains("No such file")
    assert result.exit_code != 0
```

### Test 2: File Operations {#read_file_contents}

**Test name:** `read_file_contents`

**Description:**

### Scenario: Read and write files

Common file operations needed by scripts.

**Linked Symbols:**
- `read_file_contents`
- `file`
- `contents`
- `Read`
- `read`
- `ReadFileContents`
- `Contents`
- `File`
- `len`
- `exists`
- ... and 7 more

**Code:**

```simple
test "read_file_contents":
    """
    Read entire file as string.
    """
    let content = file.read_text("/etc/hostname")
    assert content.len() > 0
    assert not content.contains("\0")

test "write_file_contents":
    """
    Write string to file, creating if needed.
    """
    file.write_text("/tmp/test.txt", "hello world")
    let content = file.read_text("/tmp/test.txt")
    assert content == "hello world"

test "append_to_file":
    """
    Append to existing file.
    """
    file.write_text("/tmp/test.txt", "line 1\n")
    file.append_text("/tmp/test.txt", "line 2\n")
    let content = file.read_text("/tmp/test.txt")
    assert content == "line 1\nline 2\n"

test "check_file_exists":
    """
    Check if file or directory exists.
    """
    assert file.exists("/etc/hostname")
    assert not file.exists("/nonexistent/file.txt")
```

### Test 3: Directory Operations {#list_directory}

**Test name:** `list_directory`

**Description:**

### Scenario: List and manipulate directories

Scripts often need to traverse directories and find files.

**Linked Symbols:**
- `directory`
- `list`
- `list_directory`
- `List`
- `ListDirectory`
- `Directory`
- `All`
- `glob`
- `len`
- `exists`
- ... and 7 more

**Code:**

```simple
test "list_directory":
    """
    List all entries in a directory.
    """
    let entries = dir.list("/tmp")
    assert entries.len() > 0
    # Returns list of names
    assert entries.all(fn(e): e is str)

test "list_directory_with_pattern":
    """
    List files matching a glob pattern.
    """
    let txt_files = dir.glob("/tmp", "*.txt")
    # All entries should end with .txt
    assert txt_files.all(fn(f): f.ends_with(".txt"))

test "create_directory":
    """
    Create directory with parents.
    """
    dir.create("/tmp/test/nested/path", recursive: true)
    assert dir.exists("/tmp/test/nested/path")

test "remove_directory":
    """
    Remove directory and contents.
    """
    dir.remove("/tmp/test", recursive: true)
    assert not dir.exists("/tmp/test")
```

### Test 4: Path Operations {#join_paths}

**Test name:** `join_paths`

**Description:**

### Scenario: Manipulate file paths

Path operations are common in scripts for building file paths.

**Linked Symbols:**
- `JoinPaths`
- `Join`
- `join`
- `Paths`
- `join_paths`
- `paths`
- `Extract`
- `dirname`
- `ext`
- `basename`
- ... and 3 more

**Code:**

```simple
test "join_paths":
    """
    Join path components safely.
    """
    let path = path.join("/home", "user", "file.txt")
    assert path == "/home/user/file.txt"

test "get_basename":
    """
    Extract filename from path.
    """
    assert path.basename("/home/user/file.txt") == "file.txt"
    assert path.basename("/home/user/") == "user"

test "get_dirname":
    """
    Extract directory from path.
    """
    assert path.dirname("/home/user/file.txt") == "/home/user"

test "get_extension":
    """
    Extract file extension.
    """
    assert path.ext("/home/user/file.txt") == ".txt"
    assert path.ext("/home/user/archive.tar.gz") == ".gz"

test "absolute_path":
    """
    Convert relative path to absolute.
    """
    let abs = path.absolute("../file.txt")
    assert abs.starts_with("/")
```

### Test 5: Environment Variables {#get_environment_variable}

**Test name:** `get_environment_variable`

**Description:**

### Scenario: Access environment variables

Scripts need to read and set environment variables.

**Linked Symbols:**
- `variable`
- `get`
- `Variable`
- `Get`
- `GetEnvironmentVariable`
- `Environment`
- `environment`
- `get_environment_variable`
- `len`
- `Read`
- ... and 5 more

**Code:**

```simple
test "get_environment_variable":
    """
    Read environment variable with default.
    """
    let home = env.get("HOME", default: "/tmp")
    assert home.len() > 0
    
    let missing = env.get("NONEXISTENT_VAR", default: "default")
    assert missing == "default"

test "set_environment_variable":
    """
    Set environment variable for child processes.
    """
    env.set("MY_VAR", "value")
    let result = shell.run("echo $MY_VAR")
    assert result.stdout.trim() == "value"
```

### Test 6: Error Handling {#command_failure_result}

**Test name:** `command_failure_result`

**Description:**

### Scenario: Handle errors gracefully

Scripts need robust error handling.

**Linked Symbols:**
- `command`
- `failure`
- `command_failure_result`
- `CommandFailureResult`
- `Result`
- `Command`
- `result`
- `Failure`
- `Failed`
- `Error`
- ... and 6 more

**Code:**

```simple
test "command_failure_result":
    """
    Failed commands return Result with error info.
    """
    let result = shell.run("false")
    assert not result.ok()
    assert result.exit_code == 1

test "file_not_found_error":
    """
    File operations return Result types.
    """
    # This should return Result<str, Error>
    # Can use ? operator or check explicitly
    let result = try file.read_text("/nonexistent")
    assert result.is_err()
```

### Test 7: Piping and Chaining {#pipe_commands}

**Test name:** `pipe_commands`

**Description:**

### Scenario: Chain commands like shell pipes

Enable composable operations.

**Linked Symbols:**
- `pipe_commands`
- `pipe`
- `PipeCommands`
- `Commands`
- `commands`
- `Pipe`
- `split`
- `len`
- `Chain`
- `write_text`
- ... and 3 more

**Code:**

```simple
test "pipe_commands":
    """
    Pipe output of one command to another.
    """
    let result = shell.pipe([
        ["echo", "hello world"],
        ["grep", "world"],
        ["wc", "-l"]
    ])
    assert result.stdout.trim() == "1"

test "chain_operations":
    """
    Chain multiple file operations.
    """
    file.write_text("/tmp/input.txt", "line1\nline2\nline3")
    
    let lines = file.read_text("/tmp/input.txt")
        .split("\n")
        .filter(fn(l): l.len() > 0)
    
    assert lines.len() == 3
```

### Test 8: Script Utilities {#find_files_recursive}

**Test name:** `find_files_recursive`

**Description:**

### Scenario: Common script utilities

Helper functions for common script patterns.

**Linked Symbols:**
- `find_files_recursive`
- `recursive`
- `FindFilesRecursive`
- `files`
- `find`
- `Recursive`
- `Files`
- `Find`
- `copy`
- `Move`
- ... and 7 more

**Code:**

```simple
test "find_files_recursive":
    """
    Find all files matching pattern recursively.
    """
    let files = file.find("/tmp", pattern: "*.txt", recursive: true)
    assert files.all(fn(f): f.ends_with(".txt"))

test "copy_file":
    """
    Copy file from source to destination.
    """
    file.write_text("/tmp/source.txt", "content")
    file.copy("/tmp/source.txt", "/tmp/dest.txt")
    assert file.read_text("/tmp/dest.txt") == "content"

test "move_file":
    """
    Move/rename file.
    """
    file.write_text("/tmp/old.txt", "content")
    file.move("/tmp/old.txt", "/tmp/new.txt")
    assert file.exists("/tmp/new.txt")
    assert not file.exists("/tmp/old.txt")
```

---

## Source Code

**View full specification:** [shell_api_spec.spl](../../tests/specs/shell_api_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/shell_api_spec.spl`*
