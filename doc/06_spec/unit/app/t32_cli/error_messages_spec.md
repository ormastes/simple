# Error Messages Specification

> Tests covering T32 Error Messages — CLI dispatch, T32 Error Messages — shell dispatch, T32 Error Messages — not-found with available items, T32 Error Messages — MCP specific.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Messages Specification

## Scenarios

### T32 Error Messages — CLI dispatch

#### unknown command shows did-you-mean for typo

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- unknown command shows did-you-mean for typo


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown command shows did-you-mean for typo")
val msg = t32_err_unknown_cmd("winows")
expect(msg).to_contain("T4001")
expect(msg).to_contain("Did you mean: windows?")
```

</details>

#### unknown command lists all valid commands

- unknown command lists all valid commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown command lists all valid commands")
val msg = t32_err_unknown_cmd("xyz")
expect(msg).to_contain("sessions")
expect(msg).to_contain("cores")
expect(msg).to_contain("windows")
expect(msg).to_contain("shell")
expect(msg).to_contain("help")
```

</details>

#### unknown subcommand shows suggestion

- unknown subcommand shows suggestion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown subcommand shows suggestion")
val msg = t32_err_unknown_subcmd("sessions", "opn", cli_sessions_subcmds())
expect(msg).to_contain("T4002")
expect(msg).to_contain("Did you mean: open?")
```

</details>

### T32 Error Messages — shell dispatch

#### unknown shell command shows available

- unknown shell command shows available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown shell command shows available")
val msg = t32_err_unknown_shell_cmd("winow")
expect(msg).to_contain("T4001")
expect(msg).to_contain("windows")
expect(msg).to_contain("show")
```

</details>

### T32 Error Messages — not-found with available items

#### window not found lists available windows

- window not found lists available windows


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("window not found lists available windows")
val available = ["register", "data_list", "data_dump", "var_local", "break_list"]
val msg = t32_err_window_not_found("registr", available)
expect(msg).to_contain("T4030")
expect(msg).to_contain("registr")
expect(msg).to_contain("register")
expect(msg).to_contain("Available:")
```

</details>

#### field not found lists available fields

- field not found lists available fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("field not found lists available fields")
val available = ["symbol", "address", "access_class", "display_format"]
val msg = t32_err_field_not_found("symbl", available)
expect(msg).to_contain("T4040")
expect(msg).to_contain("symbol")
```

</details>

#### action not found lists available actions

- action not found lists available actions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("action not found lists available actions")
val available = ["refresh", "set_break", "delete_break"]
val msg = t32_err_action_not_found("refesh", available)
expect(msg).to_contain("T4050")
expect(msg).to_contain("refresh")
```

</details>

#### core not found lists available cores

- core not found lists available cores


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("core not found lists available cores")
val available = ["core0", "core1", "core2"]
val msg = t32_err_core_not_found("core9", available)
expect(msg).to_contain("T4020")
expect(msg).to_contain("core0")
```

</details>

#### session not found lists available sessions

- session not found lists available sessions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session not found lists available sessions")
val available = ["s1", "s2", "s3"]
val msg = t32_err_session_not_found("s99", available)
expect(msg).to_contain("T4010")
expect(msg).to_contain("s1")
```

</details>

### T32 Error Messages — MCP specific

#### no session MCP references t32_session_open tool

- no session MCP references t32_session_open tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no session MCP references t32_session_open tool")
val msg = t32_err_no_session_mcp()
expect(msg).to_contain("T4013")
expect(msg).to_contain("t32_session_open")
```

</details>

#### cmd failed includes exit code and output

- cmd failed includes exit code and output


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cmd failed includes exit code and output")
val msg = t32_err_cmd_failed("Command", "1", "error text")
expect(msg).to_contain("T4071")
expect(msg).to_contain("exit 1")
expect(msg).to_contain("error text")
```

</details>

#### not found with empty available skips Available line

- not found with empty available skips Available line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not found with empty available skips Available line")
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
| Source | `test/unit/app/t32_cli/error_messages_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Error Messages — CLI dispatch, T32 Error Messages — shell dispatch, T32 Error Messages — not-found with available items, T32 Error Messages — MCP specific.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `274ecf33fe481e937d42a17d3169607b99a340c0321399125e12e5c53d397a94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `274ecf33fe481e937d42a17d3169607b99a340c0321399125e12e5c53d397a94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `274ecf33fe481e937d42a17d3169607b99a340c0321399125e12e5c53d397a94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/t32_cli/error_messages_spec.spl
mirror: doc/06_spec/unit/app/t32_cli/error_messages_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/t32_cli/error_messages_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/t32_cli/error_messages_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/t32_cli/error_messages_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unknown command shows did-you-mean for typo' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/error_messages_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unknown command lists all valid commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/error_messages_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unknown subcommand shows suggestion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
