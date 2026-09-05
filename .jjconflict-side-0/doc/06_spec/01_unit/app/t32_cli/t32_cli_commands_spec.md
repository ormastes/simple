# T32 Cli Commands Specification

> <details>

<!-- sdn-diagram:id=t32_cli_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cli_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cli_commands_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cli_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Commands Specification

## Scenarios

### T32 CLI Commands — all_cli_commands

#### returns exactly 36 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = all_cli_commands()
expect(cmds.len()).to_equal(36)
```

</details>

#### every command has non-empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = all_cli_commands()
for cmd in cmds:
    expect(cmd.name.len() > 0).to_equal(true)
```

</details>

#### every command has non-empty mcp_tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = all_cli_commands()
for cmd in cmds:
    expect(cmd.mcp_tool.len() > 0).to_equal(true)
```

</details>

#### every command has non-empty usage text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = all_cli_commands()
for cmd in cmds:
    expect(cmd.usage.len() > 0).to_equal(true)
```

</details>

### T32 CLI Commands — all_mcp_tool_names

#### returns 36 unique names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_mcp_tool_names()
expect(names.len()).to_equal(36)
```

</details>

#### contains t32_cmd_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_mcp_tool_names()
expect(names).to_contain("t32_cmd_run")
```

</details>

#### contains t32_sessions_list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_mcp_tool_names()
expect(names).to_contain("t32_sessions_list")
```

</details>

### T32 CLI Commands — find_cli_command

#### finds cmd/run

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_cli_command("cmd", "run")
var tool = ""
if val cmd = result:
    tool = cmd.mcp_tool
expect(tool).to_equal("t32_cmd_run")
```

</details>

#### finds sessions/open

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_cli_command("sessions", "open")
var tool = ""
if val cmd = result:
    tool = cmd.mcp_tool
expect(tool).to_equal("t32_session_open")
```

</details>

#### finds sessions with no subcmd

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_cli_command("sessions", "")
var tool = ""
if val cmd = result:
    tool = cmd.mcp_tool
expect(tool).to_equal("t32_sessions_list")
```

</details>

#### finds eval with no subcmd

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_cli_command("eval", "")
var tool = ""
if val cmd = result:
    tool = cmd.mcp_tool
expect(tool).to_equal("t32_eval")
```

</details>

#### finds jobs/list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_cli_command("jobs", "list")
var tool = ""
if val cmd = result:
    tool = cmd.mcp_tool
expect(tool).to_equal("t32_job_list")
```

</details>

#### finds dialog/parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_cli_command("dialog", "parse")
var tool = ""
if val cmd = result:
    tool = cmd.mcp_tool
expect(tool).to_equal("t32_dialog_parse")
```

</details>

#### returns nil for unknown command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_cli_command("nonexistent", "")
var found = false
if val cmd = result:
    found = true
expect(found).to_equal(false)
```

</details>

#### falls back to top-level for unknown subcmd

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_cli_command("sessions", "nonexistent")
var tool = ""
if val cmd = result:
    tool = cmd.mcp_tool
expect(tool).to_equal("t32_sessions_list")
```

</details>

### T32 CLI Commands — all_top_level_names

#### includes sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_top_level_names()
expect(names).to_contain("sessions")
```

</details>

#### includes cores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_top_level_names()
expect(names).to_contain("cores")
```

</details>

#### includes cmd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_top_level_names()
expect(names).to_contain("cmd")
```

</details>

#### includes eval

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_top_level_names()
expect(names).to_contain("eval")
```

</details>

#### includes jobs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_top_level_names()
expect(names).to_contain("jobs")
```

</details>

#### includes dialog

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_top_level_names()
expect(names).to_contain("dialog")
```

</details>

#### includes windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_top_level_names()
expect(names).to_contain("windows")
```

</details>

#### includes status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = all_top_level_names()
expect(names).to_contain("status")
```

</details>

### T32 CLI Commands — subcmds_for

#### sessions has open close use info

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subs = subcmds_for("sessions")
expect(subs).to_contain("open")
expect(subs).to_contain("close")
expect(subs).to_contain("use")
expect(subs).to_contain("info")
expect(subs.len()).to_equal(4)
```

</details>

#### jobs has list get cancel result

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subs = subcmds_for("jobs")
expect(subs).to_contain("list")
expect(subs).to_contain("get")
expect(subs).to_contain("cancel")
expect(subs).to_contain("result")
expect(subs.len()).to_equal(4)
```

</details>

#### dialog has parse get set click

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subs = subcmds_for("dialog")
expect(subs).to_contain("parse")
expect(subs).to_contain("get")
expect(subs).to_contain("set")
expect(subs).to_contain("click")
expect(subs.len()).to_equal(4)
```

</details>

#### cores has select

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subs = subcmds_for("cores")
expect(subs).to_contain("select")
expect(subs.len()).to_equal(1)
```

</details>

#### eval has no subcommands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subs = subcmds_for("eval")
expect(subs.len()).to_equal(0)
```

</details>

### T32 CLI Commands — all_shell_verbs

#### includes quit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = all_shell_verbs()
expect(verbs).to_contain("quit")
```

</details>

#### includes exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = all_shell_verbs()
expect(verbs).to_contain("exit")
```

</details>

#### includes help

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = all_shell_verbs()
expect(verbs).to_contain("help")
```

</details>

#### includes sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = all_shell_verbs()
expect(verbs).to_contain("sessions")
```

</details>

#### includes use

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = all_shell_verbs()
expect(verbs).to_contain("use")
```

</details>

#### includes cmd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = all_shell_verbs()
expect(verbs).to_contain("cmd")
```

</details>

#### includes eval

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = all_shell_verbs()
expect(verbs).to_contain("eval")
```

</details>

#### includes status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = all_shell_verbs()
expect(verbs).to_contain("status")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/t32_cli_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 CLI Commands — all_cli_commands
- T32 CLI Commands — all_mcp_tool_names
- T32 CLI Commands — find_cli_command
- T32 CLI Commands — all_top_level_names
- T32 CLI Commands — subcmds_for
- T32 CLI Commands — all_shell_verbs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
