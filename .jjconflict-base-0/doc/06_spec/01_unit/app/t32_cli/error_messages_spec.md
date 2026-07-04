# Error Messages Specification

> <details>

<!-- sdn-diagram:id=error_messages_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_messages_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_messages_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_messages_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Messages Specification

## Scenarios

### T32 Error Messages — CLI dispatch

#### unknown command shows did-you-mean for typo

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_unknown_cmd("winows")
expect(msg).to_contain("T4001")
expect(msg).to_contain("Did you mean: windows?")
```

</details>

#### unknown command lists all valid commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_unknown_cmd("xyz")
expect(msg).to_contain("sessions")
expect(msg).to_contain("cores")
expect(msg).to_contain("windows")
expect(msg).to_contain("shell")
expect(msg).to_contain("help")
```

</details>

#### unknown subcommand shows suggestion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_unknown_subcmd("sessions", "opn", cli_sessions_subcmds())
expect(msg).to_contain("T4002")
expect(msg).to_contain("Did you mean: open?")
```

</details>

### T32 Error Messages — shell dispatch

#### unknown shell command shows available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_unknown_shell_cmd("winow")
expect(msg).to_contain("T4001")
expect(msg).to_contain("windows")
expect(msg).to_contain("show")
```

</details>

### T32 Error Messages — not-found with available items

#### window not found lists available windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = ["register", "data_list", "data_dump", "var_local", "break_list"]
val msg = t32_err_window_not_found("registr", available)
expect(msg).to_contain("T4030")
expect(msg).to_contain("registr")
expect(msg).to_contain("register")
expect(msg).to_contain("Available:")
```

</details>

#### field not found lists available fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = ["symbol", "address", "access_class", "display_format"]
val msg = t32_err_field_not_found("symbl", available)
expect(msg).to_contain("T4040")
expect(msg).to_contain("symbol")
```

</details>

#### action not found lists available actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = ["refresh", "set_break", "delete_break"]
val msg = t32_err_action_not_found("refesh", available)
expect(msg).to_contain("T4050")
expect(msg).to_contain("refresh")
```

</details>

#### core not found lists available cores

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = ["core0", "core1", "core2"]
val msg = t32_err_core_not_found("core9", available)
expect(msg).to_contain("T4020")
expect(msg).to_contain("core0")
```

</details>

#### session not found lists available sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = ["s1", "s2", "s3"]
val msg = t32_err_session_not_found("s99", available)
expect(msg).to_contain("T4010")
expect(msg).to_contain("s1")
```

</details>

### T32 Error Messages — MCP specific

#### no session MCP references t32_session_open tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_no_session_mcp()
expect(msg).to_contain("T4013")
expect(msg).to_contain("t32_session_open")
```

</details>

#### cmd failed includes exit code and output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_cmd_failed("Command", "1", "error text")
expect(msg).to_contain("T4071")
expect(msg).to_contain("exit 1")
expect(msg).to_contain("error text")
```

</details>

#### not found with empty available skips Available line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = t32_err_not_found("T4010", "session", "s99", [])
expect(msg).to_contain("T4010")
expect(msg).to_contain("s99")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/error_messages_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Error Messages — CLI dispatch
- T32 Error Messages — shell dispatch
- T32 Error Messages — not-found with available items
- T32 Error Messages — MCP specific

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
