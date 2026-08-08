# Shell API

> Tests the shell API for process execution, filesystem operations, and I/O scripting. Verifies that shell commands can be spawned, piped, and that exit codes, stdout, and stderr are correctly captured and forwarded.

<!-- sdn-diagram:id=shell_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_api_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell API

Tests the shell API for process execution, filesystem operations, and I/O scripting. Verifies that shell commands can be spawned, piped, and that exit codes, stdout, and stderr are correctly captured and forwarded.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/shell_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the shell API for process execution, filesystem operations, and I/O
scripting. Verifies that shell commands can be spawned, piped, and that exit
codes, stdout, and stderr are correctly captured and forwarded.

## Scenarios

#### execute_command_basic

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell.run("echo hello")
check(result.ok())
check(result.stdout == "hello\n")
check(result.exit_code == 0)
```

</details>

#### execute_command_with_args

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell.run("ls -la {tmp}")
check(result.ok())
check(result.stdout.contains("total"))
```

</details>

#### execute_command_capture_stderr

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell.run("ls /nonexistent_path_xyz 2>&1")
check(result.stdout.contains("No such file") or result.exit_code != 0)
```

</details>

#### read_file_contents

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# /etc/hostname exists on Linux; macOS uses /etc/hosts instead
val path_to_read = if file.exists("/etc/hostname"): "/etc/hostname" else: "/etc/hosts"
val content = file.read_text(path_to_read)
check(content.len() > 0)
```

</details>

#### write_file_contents

1. file write text
2. check
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
file.write_text("{tmp}/simple_test_shell_api.txt", "hello world")
val content = file.read_text("{tmp}/simple_test_shell_api.txt")
check(content == "hello world")
file.delete("{tmp}/simple_test_shell_api.txt")
```

</details>

#### append_to_file

1. file write text
2. file append text
3. check
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
file.write_text("{tmp}/simple_test_append.txt", "line 1\n")
file.append_text("{tmp}/simple_test_append.txt", "line 2\n")
val content = file.read_text("{tmp}/simple_test_append.txt")
check(content == "line 1\nline 2\n")
file.delete("{tmp}/simple_test_append.txt")
```

</details>

#### check_file_exists

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# /etc/hostname on Linux, /etc/hosts on macOS — both always exist
check(file.exists("/etc/hostname") or file.exists("/etc/hosts"))
check(not file.exists("/nonexistent/file.txt"))
```

</details>

#### list_directory

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = dir.list(tmp)
check(entries.len() > 0)
```

</details>

#### list_directory_with_pattern

1. file write text
2. check
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
file.write_text("{tmp}/simple_glob_test.txt", "test")
val txt_files = dir.glob_files(tmp, "simple_glob_test.txt")
check(txt_files.len() > 0)
file.delete("{tmp}/simple_glob_test.txt")
```

</details>

#### create_directory

1. dir create
2. check
3. dir remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir.create("{tmp}/simple_test_nested/a/b")
check(dir.exists("{tmp}/simple_test_nested/a/b"))
dir.remove("{tmp}/simple_test_nested")
```

</details>

#### remove_directory

1. dir create
2. dir remove
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir.create("{tmp}/simple_test_rmdir/sub")
dir.remove("{tmp}/simple_test_rmdir")
check(not dir.exists("{tmp}/simple_test_rmdir"))
```

</details>

#### join_paths

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path.join_parts("/home", "user", "file.txt")
check(result == "/home/user/file.txt")
```

</details>

#### get_basename

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(path.basename("/home/user/file.txt") == "file.txt")
check(path.basename("/home/user/") == "user")
```

</details>

#### get_dirname

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(path.dirname("/home/user/file.txt") == "/home/user")
```

</details>

#### get_extension

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(path.ext("/home/user/file.txt") == ".txt")
check(path.ext("/home/user/archive.tar.gz") == ".gz")
```

</details>

#### absolute_path

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use a path relative to cwd to avoid realpath -m issues on macOS
val abs = path.absolute(".")
check(abs.starts_with("/"))
```

</details>

#### get_environment_variable

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = env.get_with_default("HOME", tmp)
check(home.len() > 0)

val missing = env.get_with_default("NONEXISTENT_SIMPLE_VAR_XYZ", "default")
check(missing == "default")
```

</details>

#### set_environment_variable

1. env set
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
env.set("SIMPLE_TEST_VAR", "test_value")
val result = shell.run("echo $SIMPLE_TEST_VAR")
check(result.stdout.trim() == "test_value")
```

</details>

#### command_failure_result

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell.run("false")
check(not result.ok())
check(result.exit_code != 0)
```

</details>

#### file_not_found_error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = file.read_text("/nonexistent_xyz_path")
check(content == "")
```

</details>

#### pipe_commands

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell.pipe([
    ["echo", "hello world"],
    ["grep", "world"],
    ["wc", "-l"]
])
check(result.stdout.trim() == "1")
```

</details>

#### chain_operations

1. file write text
2. check
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
file.write_text("{tmp}/simple_chain_test.txt", "line1\nline2\nline3")
val content = file.read_text("{tmp}/simple_chain_test.txt")
val lines = content.split("\n")
var count = 0
for l in lines:
    if l.len() > 0:
        count = count + 1
check(count == 3)
file.delete("{tmp}/simple_chain_test.txt")
```

</details>

#### find_files_recursive

1. file write text
2. check
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
file.write_text("{tmp}/simple_find_test.txt", "test")
val files = file.find_files(tmp, "simple_find_test.txt")
check(files.len() > 0)
file.delete("{tmp}/simple_find_test.txt")
```

</details>

#### copy_file

1. file write text
2. file copy
3. check
4. file delete
5. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
file.write_text("{tmp}/simple_copy_src.txt", "content")
file.copy("{tmp}/simple_copy_src.txt", "{tmp}/simple_copy_dst.txt")
check(file.read_text("{tmp}/simple_copy_dst.txt") == "content")
file.delete("{tmp}/simple_copy_src.txt")
file.delete("{tmp}/simple_copy_dst.txt")
```

</details>

#### move_file

1. file write text
2. rt file rename
3. check
4. check
5. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
file.write_text("{tmp}/simple_move_old.txt", "content")
rt_file_rename("{tmp}/simple_move_old.txt", "{tmp}/simple_move_new.txt")
check(file.exists("{tmp}/simple_move_new.txt"))
check(not file.exists("{tmp}/simple_move_old.txt"))
file.delete("{tmp}/simple_move_new.txt")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
