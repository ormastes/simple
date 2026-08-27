# Shell API

> Tests the shell API for process execution, filesystem operations, and I/O scripting. Verifies that shell commands can be spawned, piped, and that exit codes, stdout, and stderr are correctly captured and forwarded.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the shell API for process execution, filesystem operations, and I/O
scripting. Verifies that shell commands can be spawned, piped, and that exit
codes, stdout, and stderr are correctly captured and forwarded.

## Scenarios

#### execute_command_basic

- execute_command_basic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execute_command_basic")
val result = shell.run("echo hello")
check(result.ok())
check(result.stdout == "hello\n")
check(result.exit_code == 0)
```

</details>

#### execute_command_with_args

- execute_command_with_args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execute_command_with_args")
val result = shell.run("ls -la {tmp}")
check(result.ok())
check(result.stdout.contains("total"))
```

</details>

#### execute_command_capture_stderr

- execute_command_capture_stderr


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execute_command_capture_stderr")
val result = shell.run("ls /nonexistent_path_xyz 2>&1")
check(result.stdout.contains("No such file") or result.exit_code != 0)
```

</details>

#### read_file_contents

- read_file_contents


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read_file_contents")
# /etc/hostname exists on Linux; macOS uses /etc/hosts instead
val path_to_read = if file.exists("/etc/hostname"): "/etc/hostname" else: "/etc/hosts"
val content = file.read_text(path_to_read)
check(content.len() > 0)
```

</details>

#### write_file_contents

- write_file_contents


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("write_file_contents")
file.write_text("{tmp}/simple_test_shell_api.txt", "hello world")
val content = file.read_text("{tmp}/simple_test_shell_api.txt")
check(content == "hello world")
file.delete("{tmp}/simple_test_shell_api.txt")
```

</details>

#### append_to_file

- append_to_file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("append_to_file")
file.write_text("{tmp}/simple_test_append.txt", "line 1\n")
file.append_text("{tmp}/simple_test_append.txt", "line 2\n")
val content = file.read_text("{tmp}/simple_test_append.txt")
check(content == "line 1\nline 2\n")
file.delete("{tmp}/simple_test_append.txt")
```

</details>

#### check_file_exists

- check_file_exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check_file_exists")
# /etc/hostname on Linux, /etc/hosts on macOS — both always exist
check(file.exists("/etc/hostname") or file.exists("/etc/hosts"))
check(not file.exists("/nonexistent/file.txt"))
```

</details>

#### list_directory

- list_directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("list_directory")
val entries = dir.list(tmp)
check(entries.len() > 0)
```

</details>

#### list_directory_with_pattern

- list_directory_with_pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("list_directory_with_pattern")
file.write_text("{tmp}/simple_glob_test.txt", "test")
val txt_files = dir.glob_files(tmp, "simple_glob_test.txt")
check(txt_files.len() > 0)
file.delete("{tmp}/simple_glob_test.txt")
```

</details>

#### create_directory

- create_directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("create_directory")
dir.create("{tmp}/simple_test_nested/a/b")
check(dir.exists("{tmp}/simple_test_nested/a/b"))
dir.remove("{tmp}/simple_test_nested")
```

</details>

#### remove_directory

- remove_directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("remove_directory")
dir.create("{tmp}/simple_test_rmdir/sub")
dir.remove("{tmp}/simple_test_rmdir")
check(not dir.exists("{tmp}/simple_test_rmdir"))
```

</details>

#### join_paths

- join_paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("join_paths")
val result = path.join_parts("/home", "user", "file.txt")
check(result == "/home/user/file.txt")
```

</details>

#### get_basename

- get_basename


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_basename")
check(path.basename("/home/user/file.txt") == "file.txt")
check(path.basename("/home/user/") == "user")
```

</details>

#### get_dirname

- get_dirname


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_dirname")
check(path.dirname("/home/user/file.txt") == "/home/user")
```

</details>

#### get_extension

- get_extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_extension")
check(path.ext("/home/user/file.txt") == ".txt")
check(path.ext("/home/user/archive.tar.gz") == ".gz")
```

</details>

#### absolute_path

- absolute_path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("absolute_path")
# Use a path relative to cwd to avoid realpath -m issues on macOS
val abs = path.absolute(".")
check(abs.starts_with("/"))
```

</details>

#### get_environment_variable

- get_environment_variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("get_environment_variable")
val home = env.get_with_default("HOME", tmp)
check(home.len() > 0)

val missing = env.get_with_default("NONEXISTENT_SIMPLE_VAR_XYZ", "default")
check(missing == "default")
```

</details>

#### set_environment_variable

- set_environment_variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("set_environment_variable")
env.set("SIMPLE_TEST_VAR", "test_value")
val result = shell.run("echo $SIMPLE_TEST_VAR")
check(result.stdout.trim() == "test_value")
```

</details>

#### command_failure_result

- command_failure_result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("command_failure_result")
val result = shell.run("false")
check(not result.ok())
check(result.exit_code != 0)
```

</details>

#### file_not_found_error

- file_not_found_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("file_not_found_error")
val content = file.read_text("/nonexistent_xyz_path")
check(content == "")
```

</details>

#### pipe_commands

- pipe_commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pipe_commands")
val result = shell.pipe([
    ["echo", "hello world"],
    ["grep", "world"],
    ["wc", "-l"]
])
check(result.stdout.trim() == "1")
```

</details>

#### chain_operations

- chain_operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chain_operations")
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

- find_files_recursive


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("find_files_recursive")
file.write_text("{tmp}/simple_find_test.txt", "test")
val files = file.find_files(tmp, "simple_find_test.txt")
check(files.len() > 0)
file.delete("{tmp}/simple_find_test.txt")
```

</details>

#### copy_file

- copy_file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("copy_file")
file.write_text("{tmp}/simple_copy_src.txt", "content")
file.copy("{tmp}/simple_copy_src.txt", "{tmp}/simple_copy_dst.txt")
check(file.read_text("{tmp}/simple_copy_dst.txt") == "content")
file.delete("{tmp}/simple_copy_src.txt")
file.delete("{tmp}/simple_copy_dst.txt")
```

</details>

#### move_file

- move_file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("move_file")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e1c87d1ef09ffe2997ccc77e30678f8edec334ecfff04289031ff14bfaca726`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e1c87d1ef09ffe2997ccc77e30678f8edec334ecfff04289031ff14bfaca726`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e1c87d1ef09ffe2997ccc77e30678f8edec334ecfff04289031ff14bfaca726`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/app/shell_api_spec.spl
mirror: doc/06_spec/03_system/feature/app/shell_api_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/shell_api_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/feature/app/shell_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/shell_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/shell_api_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/03_system/feature/app/shell_api_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'execute_command_basic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/shell_api_spec.spl:220:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'execute_command_with_args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/shell_api_spec.spl:236:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read_file_contents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
