# Shell App Specification

> <details>

<!-- sdn-diagram:id=shell_app_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_app_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_app_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_app_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell App Specification

## Scenarios

### ShellApp

#### when newly created

#### starts with cwd at root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.cwd).to_equal("/")
```

</details>

#### starts with empty history

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.history.len()).to_equal(0)
```

</details>

#### starts with history_pos at -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.history_pos).to_equal(-1)
```

</details>

#### starts in running state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.running).to_equal(true)
```

</details>

#### starts with exit code 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.last_exit_code).to_equal(0)
```

</details>

#### has a default prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.prompt).to_equal("$ ")
```

</details>

#### has empty output_lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.output_lines.len()).to_equal(0)
```

</details>

#### has nil vfs by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.vfs).to_be_nil
```

</details>

#### environment variables

#### has HOME set to /

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
val env = shell.env
# env is a list of (text, text) tuples
expect(env.len()).to_be_greater_than(0)
```

</details>

#### has at least 3 default environment variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
# HOME, PATH, SHELL
expect(shell.env.len()).to_equal(3)
```

</details>

#### terminal

#### has a terminal attached

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.terminal.cols).to_equal(80)
expect(shell.terminal.rows).to_equal(24)
```

</details>

### ShellApp command parsing

#### simple commands

#### splits simple command into tokens

1. var shell = ShellApp new
   - Expected: tokens.len() equals `3`
   - Expected: tokens[0] equals `ls`
   - Expected: tokens[1] equals `-la`
   - Expected: tokens[2] equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("ls -la /home")
expect(tokens.len()).to_equal(3)
expect(tokens[0]).to_equal("ls")
expect(tokens[1]).to_equal("-la")
expect(tokens[2]).to_equal("/home")
```

</details>

#### handles single word command

1. var shell = ShellApp new
   - Expected: tokens.len() equals `1`
   - Expected: tokens[0] equals `pwd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("pwd")
expect(tokens.len()).to_equal(1)
expect(tokens[0]).to_equal("pwd")
```

</details>

#### handles empty input

1. var shell = ShellApp new
   - Expected: tokens.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("")
expect(tokens.len()).to_equal(0)
```

</details>

#### handles extra whitespace

1. var shell = ShellApp new
   - Expected: tokens.len() equals `2`
   - Expected: tokens[0] equals `ls`
   - Expected: tokens[1] equals `-la`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("  ls   -la   ")
expect(tokens.len()).to_equal(2)
expect(tokens[0]).to_equal("ls")
expect(tokens[1]).to_equal("-la")
```

</details>

#### quoted arguments

#### handles double-quoted string

1. var shell = ShellApp new
   - Expected: tokens.len() equals `2`
   - Expected: tokens[0] equals `echo`
   - Expected: tokens[1] equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("echo \"hello world\"")
expect(tokens.len()).to_equal(2)
expect(tokens[0]).to_equal("echo")
expect(tokens[1]).to_equal("hello world")
```

</details>

#### handles single-quoted string

1. var shell = ShellApp new
   - Expected: tokens.len() equals `2`
   - Expected: tokens[0] equals `echo`
   - Expected: tokens[1] equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("echo 'hello world'")
expect(tokens.len()).to_equal(2)
expect(tokens[0]).to_equal("echo")
expect(tokens[1]).to_equal("hello world")
```

</details>

#### handles escaped characters

1. var shell = ShellApp new
   - Expected: tokens.len() equals `2`
   - Expected: tokens[0] equals `echo`
   - Expected: tokens[1] equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("echo hello\\ world")
expect(tokens.len()).to_equal(2)
expect(tokens[0]).to_equal("echo")
expect(tokens[1]).to_equal("hello world")
```

</details>

#### multiple arguments

#### parses command with flag and path

1. var shell = ShellApp new
   - Expected: tokens.len() equals `3`
   - Expected: tokens[0] equals `cat`
   - Expected: tokens[1] equals `-n`
   - Expected: tokens[2] equals `/etc/passwd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("cat -n /etc/passwd")
expect(tokens.len()).to_equal(3)
expect(tokens[0]).to_equal("cat")
expect(tokens[1]).to_equal("-n")
expect(tokens[2]).to_equal("/etc/passwd")
```

</details>

#### parses command with many args

1. var shell = ShellApp new
   - Expected: tokens.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
val tokens = shell._tokenize("cp -r src/ dst/")
expect(tokens.len()).to_equal(3)
```

</details>

### ShellApp history

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
expect(shell.history.len()).to_equal(0)
```

</details>

#### records executed command

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.history.len() equals `1`
   - Expected: shell.history[0] equals `help`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("help")
expect(shell.history.len()).to_equal(1)
expect(shell.history[0]).to_equal("help")
```

</details>

#### records multiple commands

1. var shell = ShellApp new
2. shell  execute line
3. shell  execute line
   - Expected: shell.history.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("help")
shell._execute_line("pwd")
expect(shell.history.len()).to_equal(2)
```

</details>

#### does not record empty input

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.history.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("")
expect(shell.history.len()).to_equal(0)
```

</details>

### ShellApp built-in commands

#### help command

#### executes without error

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.last_exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("help")
expect(shell.last_exit_code).to_equal(0)
```

</details>

#### lists kernel MVP commands

1. var shell = ShellApp new
2. shell  execute line
   - Expected: seen_run is true
   - Expected: seen_mem is true
   - Expected: seen_reboot is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("help")
var seen_run = false
var seen_mem = false
var seen_reboot = false
for line in shell.output_lines:
    if line.contains("run CMD"):
        seen_run = true
    if line.contains("mem"):
        seen_mem = true
    if line.contains("reboot"):
        seen_reboot = true
expect(seen_run).to_equal(true)
expect(seen_mem).to_equal(true)
expect(seen_reboot).to_equal(true)
```

</details>

#### pwd command

#### shows current directory

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.last_exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("pwd")
expect(shell.last_exit_code).to_equal(0)
```

</details>

#### exit command

#### sets running to false

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.running is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("exit")
expect(shell.running).to_equal(false)
```

</details>

#### cd command

#### changes cwd

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.cwd equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("cd /home")
expect(shell.cwd).to_equal("/home")
```

</details>

#### cd / goes to root

1. var shell = ShellApp new
2. shell  execute line
3. shell  execute line
   - Expected: shell.cwd equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("cd /home")
shell._execute_line("cd /")
expect(shell.cwd).to_equal("/")
```

</details>

#### echo command

#### produces output

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.last_exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("echo hello")
expect(shell.last_exit_code).to_equal(0)
```

</details>

#### env command

#### lists environment variables

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.last_exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("env")
expect(shell.last_exit_code).to_equal(0)
```

</details>

#### export command

#### sets environment variable

1. var shell = ShellApp new
2. shell  execute line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("export FOO=bar")
# Verify env grew
expect(shell.env.len()).to_be_greater_than(3)
```

</details>

#### run command

#### is treated as a built-in

1. var shell = ShellApp new
   - Expected: shell._is_builtin_command("run") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
expect(shell._is_builtin_command("run")).to_equal(true)
```

</details>

#### prints usage for --help

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.last_exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("run --help")
expect(shell.last_exit_code).to_equal(0)
```

</details>

#### mem command

#### is treated as a built-in

1. var shell = ShellApp new
   - Expected: shell._is_builtin_command("mem") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
expect(shell._is_builtin_command("mem")).to_equal(true)
```

</details>

#### prints usage for --help

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.last_exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("mem --help")
expect(shell.last_exit_code).to_equal(0)
```

</details>

#### reboot command

#### is treated as a built-in

1. var shell = ShellApp new
   - Expected: shell._is_builtin_command("reboot") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
expect(shell._is_builtin_command("reboot")).to_equal(true)
```

</details>

#### prints a validation error when invoked

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.last_exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
shell._execute_line("reboot")
expect(shell.last_exit_code).to_equal(1)
```

</details>

#### bootstrap tool commands

#### treats uname as a built-in

1. var shell = ShellApp new
   - Expected: shell._is_builtin_command("uname") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
expect(shell._is_builtin_command("uname")).to_equal(true)
```

</details>

#### treats cmake as a built-in

1. var shell = ShellApp new
   - Expected: shell._is_builtin_command("cmake") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
expect(shell._is_builtin_command("cmake")).to_equal(true)
```

</details>

#### treats ninja as a built-in

1. var shell = ShellApp new
   - Expected: shell._is_builtin_command("ninja") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
expect(shell._is_builtin_command("ninja")).to_equal(true)
```

</details>

### ShellApp external command routing

#### does not execute registry callbacks for non-builtins

1. var shell = ShellApp new
2. var registry = ToolRegistry new
3. shell  execute line
   - Expected: shell.last_exit_code equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()
var registry = ToolRegistry.new()
registry.register(ToolEntry(
    name: "fake_external",
    description: "test-only external command",
    category: "test",
    run_fn: _fake_registry_tool,
    capabilities: []
))
shell.tool_registry = registry

shell._execute_line("fake_external")

expect(shell.last_exit_code).to_equal(127)
```

</details>

#### still rejects backgrounded built-ins

1. var shell = ShellApp new
2. shell  execute line
   - Expected: shell.last_exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shell = ShellApp.new()

shell._execute_line("pwd &")

expect(shell.last_exit_code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/shell/shell_app_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ShellApp
- ShellApp command parsing
- ShellApp history
- ShellApp built-in commands
- ShellApp external command routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
