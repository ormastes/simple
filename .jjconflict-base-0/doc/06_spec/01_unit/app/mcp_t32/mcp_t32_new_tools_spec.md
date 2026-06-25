# Mcp T32 New Tools Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_new_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_new_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_new_tools_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_new_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 New Tools Specification

## Scenarios

### T32 MCP New Tools — CLI-MCP Gap Closure

#### t32_session_info

#### returns session details for valid id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = session_info_lookup("sess_001")
expect(info.session_id).to_equal("sess_001")
expect(info.host).to_equal("localhost")
```

</details>

#### returns error for unknown session id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = session_info_error("nonexistent_session")
expect(err).to_start_with("T4200")
expect(err).to_contain("nonexistent_session")
expect(err).to_contain("t32_sessions_list")
```

</details>

#### includes host and port fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = session_info_lookup("sess_001")
expect(info.host).to_equal("localhost")
expect(info.port).to_equal(20000)
```

</details>

#### includes architecture field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = session_info_lookup("sess_002")
expect(info.architecture).to_equal("RISCV")
```

</details>

#### includes connection state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = session_info_lookup("sess_disconnected")
expect(info.connected).to_equal(false)
val info_ok = session_info_lookup("sess_001")
expect(info_ok.connected).to_equal(true)
```

</details>

#### includes core count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = session_info_lookup("sess_001")
expect(info.core_count).to_equal(4)
val info2 = session_info_lookup("sess_002")
expect(info2.core_count).to_equal(2)
```

</details>

#### includes current core id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = session_info_lookup("sess_001")
expect(info.current_core_id).to_equal(0)
val info2 = session_info_lookup("sess_002")
expect(info2.current_core_id).to_equal(1)
```

</details>

#### disconnected session has zero core count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = session_info_lookup("sess_disconnected")
expect(info.core_count).to_equal(0)
expect(info.current_core_id).to_equal(-1)
```

</details>

#### t32_action_list

#### lists all actions for register window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = action_list_lookup("register")
expect(actions.len()).to_equal(3)
```

</details>

#### lists all actions for source window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = action_list_lookup("source")
expect(actions.len()).to_equal(4)
```

</details>

#### returns empty list for window with no actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = action_list_lookup("area")
expect(actions.len()).to_equal(0)
```

</details>

#### returns error for unknown window

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = action_list_lookup("nonexistent_window")
expect(action_list_is_error(actions)).to_equal(true)
val err = action_list_error("nonexistent_window")
expect(err).to_start_with("T4201")
expect(err).to_contain("nonexistent_window")
```

</details>

#### action entries have key, label, type fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = action_list_lookup("register")
val first = actions[0]
expect(first.key).to_equal("reg.copy")
expect(first.label).to_equal("Copy Register Value")
expect(first.action_type).to_equal("read")
```

</details>

#### filters by action type read

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = action_list_lookup("source")
val read_actions = action_list_filter_by_type(actions, "read")
expect(read_actions.len()).to_equal(2)
expect(read_actions[0].key).to_equal("src.find")
```

</details>

#### filters by action type write

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = action_list_lookup("source")
val write_actions = action_list_filter_by_type(actions, "write")
expect(write_actions.len()).to_equal(1)
expect(write_actions[0].key).to_equal("src.bp")
```

</details>

#### returns all actions when no filter applied

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = action_list_lookup("register")
val all_types = action_list_filter_by_type(actions, "")
# Empty filter returns nothing — use unfiltered list for "all"
expect(all_types.len()).to_equal(0)
expect(actions.len()).to_equal(3)
```

</details>

#### t32_status_snapshot

#### returns run_state running

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_test_status("running", "system up", "sess_001", 0, "", true)
expect(snap.run_state).to_equal("running")
```

</details>

#### returns run_state stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_test_status("stopped", "break at main", "sess_001", 0, "Break at 0x08001234", true)
expect(snap.run_state).to_equal("stopped")
```

</details>

#### returns system state text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_test_status("stopped", "power debug ready", "sess_001", 0, "", true)
expect(snap.system_state).to_equal("power debug ready")
```

</details>

#### returns session context with id and core

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_test_status("running", "up", "sess_002", 1, "", true)
expect(snap.session_id).to_equal("sess_002")
expect(snap.core_id).to_equal(1)
```

</details>

#### returns message line if available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_test_status("stopped", "break", "sess_001", 0, "Break at main+0x10", true)
expect(snap.message_line).to_equal("Break at main+0x10")
```

</details>

#### returns connected=false when disconnected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_test_status("unknown", "disconnected", "sess_003", -1, "", false)
expect(snap.connected).to_equal(false)
expect(snap.run_state).to_equal("unknown")
```

</details>

#### t32_cmm_validate mode=check

#### detects DIALOG.OK as BLOCK

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("DIALOG.OK \"Flash done\"", "check")
expect(result.classification).to_equal("needs_manual_rewrite")
expect(result.findings.len()).to_equal(1)
expect(result.findings[0].command).to_equal("DIALOG.OK")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects DIALOG.YESNO as BLOCK

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("DIALOG.YESNO \"Erase flash?\"", "check")
expect(result.classification).to_equal("needs_manual_rewrite")
expect(result.findings[0].command).to_equal("DIALOG.YESNO")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects DIALOG.FILE as BLOCK

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("DIALOG.FILE \"*.elf\"", "check")
expect(result.findings[0].command).to_equal("DIALOG.FILE")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects INKEY as BLOCK

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("INKEY &pressed", "check")
expect(result.findings[0].command).to_equal("INKEY")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects ENTER as BLOCK

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("ENTER &value", "check")
expect(result.findings[0].command).to_equal("ENTER")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects PAUSE as BLOCK

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("PAUSE", "check")
expect(result.findings[0].command).to_equal("PAUSE")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects STOP as BLOCK

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("STOP", "check")
expect(result.findings[0].command).to_equal("STOP")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects SCREEN.WAIT as WARN

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("SCREEN.WAIT", "check")
expect(result.classification).to_equal("has_warnings")
expect(result.findings[0].command).to_equal("SCREEN.WAIT")
expect(result.findings[0].severity).to_equal("WARN")
```

</details>

#### safe script returns classification=safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("ENTRY &addr\nData.dump &addr\nENDDO", "check")
expect(result.classification).to_equal("safe")
expect(result.findings.len()).to_equal(0)
```

</details>

#### t32_cmm_validate mode=report

#### report includes line numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("ENTRY &addr\nDIALOG.OK \"Done\"\nENDDO", "report")
expect(result.findings.len()).to_equal(1)
expect(result.findings[0].line).to_equal(2)
```

</details>

#### report classifies severity BLOCK

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("DIALOG.YESNO \"Sure?\"", "report")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### report classifies severity WARN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("SCREEN.WAIT", "report")
expect(result.findings[0].severity).to_equal("WARN")
```

</details>

#### multiple findings in one script

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "DIALOG.OK \"Start\"\nENTRY &addr\nPAUSE\nDIALOG.YESNO \"Continue?\"\nENDDO"
val result = cmm_validate(source, "report")
expect(result.findings.len()).to_equal(3)
expect(result.findings[0].command).to_equal("DIALOG.OK")
expect(result.findings[1].command).to_equal("PAUSE")
expect(result.findings[2].command).to_equal("DIALOG.YESNO")
```

</details>

#### nested patterns detected — DIALOG inside IF context

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "IF TRUE()\n(\n  DIALOG.OK \"inside if\"\n)\nENDDO"
val result = cmm_validate(source, "report")
expect(result.findings.len()).to_equal(1)
expect(result.findings[0].command).to_equal("DIALOG.OK")
expect(result.findings[0].line).to_equal(3)
```

</details>

#### empty script returns safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("", "report")
expect(result.classification).to_equal("safe")
expect(result.findings.len()).to_equal(0)
```

</details>

#### report includes command name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("STOP", "report")
expect(result.findings[0].command).to_equal("STOP")
expect(result.findings[0].message).to_contain("PRACTICE")
```

</details>

#### t32_cmm_validate mode=suggest

#### DIALOG.YESNO suggests ENTRY &confirm pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("DIALOG.YESNO \"Erase?\"", "suggest")
expect(result.findings[0].suggestion).to_contain("ENTRY")
expect(result.findings[0].suggestion).to_contain("confirm")
```

</details>

#### DIALOG.FILE suggests tool argument path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("DIALOG.FILE \"*.elf\"", "suggest")
expect(result.findings[0].suggestion).to_contain("tool argument")
```

</details>

#### ENTER suggests ENTRY &var pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("ENTER &value", "suggest")
expect(result.findings[0].suggestion).to_contain("ENTRY")
expect(result.findings[0].suggestion).to_contain("var")
```

</details>

#### PAUSE suggests PRINT checkpoint pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("PAUSE", "suggest")
expect(result.findings[0].suggestion).to_contain("PRINT")
expect(result.findings[0].suggestion).to_contain("checkpoint")
```

</details>

#### unbounded WAIT suggests timeout pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("WAIT !STATE.RUN()", "suggest")
expect(result.findings.len()).to_equal(1)
expect(result.findings[0].severity).to_equal("WARN")
expect(result.findings[0].suggestion).to_contain("timeout")
```

</details>

#### safe script has no suggestions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cmm_validate("ENTRY &addr\nData.dump &addr", "suggest")
expect(result.findings.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_new_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP New Tools — CLI-MCP Gap Closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
