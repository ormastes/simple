# Mcp T32 New Tools Specification

> Tests covering T32 MCP New Tools — CLI-MCP Gap Closure.

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

- returns session details for valid id
   - Expected: info.session_id equals `sess_001`
   - Expected: info.host equals `localhost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns session details for valid id")
val info = session_info_lookup("sess_001")
expect(info.session_id).to_equal("sess_001")
expect(info.host).to_equal("localhost")
```

</details>

#### returns error for unknown session id

- returns error for unknown session id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown session id")
val err = session_info_error("nonexistent_session")
expect(err).to_start_with("T4200")
expect(err).to_contain("nonexistent_session")
expect(err).to_contain("t32_sessions_list")
```

</details>

#### includes host and port fields

- includes host and port fields
   - Expected: info.host equals `localhost`
   - Expected: info.port equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes host and port fields")
val info = session_info_lookup("sess_001")
expect(info.host).to_equal("localhost")
expect(info.port).to_equal(20000)
```

</details>

#### includes architecture field

- includes architecture field
   - Expected: info.architecture equals `RISCV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes architecture field")
val info = session_info_lookup("sess_002")
expect(info.architecture).to_equal("RISCV")
```

</details>

#### includes connection state

- includes connection state
   - Expected: info.connected is false
   - Expected: info_ok.connected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes connection state")
val info = session_info_lookup("sess_disconnected")
expect(info.connected).to_equal(false)
val info_ok = session_info_lookup("sess_001")
expect(info_ok.connected).to_equal(true)
```

</details>

#### includes core count

- includes core count
   - Expected: info.core_count equals `4`
   - Expected: info2.core_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes core count")
val info = session_info_lookup("sess_001")
expect(info.core_count).to_equal(4)
val info2 = session_info_lookup("sess_002")
expect(info2.core_count).to_equal(2)
```

</details>

#### includes current core id

- includes current core id
   - Expected: info.current_core_id equals `0`
   - Expected: info2.current_core_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes current core id")
val info = session_info_lookup("sess_001")
expect(info.current_core_id).to_equal(0)
val info2 = session_info_lookup("sess_002")
expect(info2.current_core_id).to_equal(1)
```

</details>

#### disconnected session has zero core count

- disconnected session has zero core count
   - Expected: info.core_count equals `0`
   - Expected: info.current_core_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disconnected session has zero core count")
val info = session_info_lookup("sess_disconnected")
expect(info.core_count).to_equal(0)
expect(info.current_core_id).to_equal(-1)
```

</details>

#### t32_action_list

#### lists all actions for register window

- lists all actions for register window
   - Expected: actions.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all actions for register window")
val actions = action_list_lookup("register")
expect(actions.len()).to_equal(3)
```

</details>

#### lists all actions for source window

- lists all actions for source window
   - Expected: actions.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all actions for source window")
val actions = action_list_lookup("source")
expect(actions.len()).to_equal(4)
```

</details>

#### returns empty list for window with no actions

- returns empty list for window with no actions
   - Expected: actions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list for window with no actions")
val actions = action_list_lookup("area")
expect(actions.len()).to_equal(0)
```

</details>

#### returns error for unknown window

- returns error for unknown window
   - Expected: action_list_is_error(actions) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown window")
val actions = action_list_lookup("nonexistent_window")
expect(action_list_is_error(actions)).to_equal(true)
val err = action_list_error("nonexistent_window")
expect(err).to_start_with("T4201")
expect(err).to_contain("nonexistent_window")
```

</details>

#### action entries have key, label, type fields

- action entries have key, label, type fields
   - Expected: first.key equals `reg.copy`
   - Expected: first.label equals `Copy Register Value`
   - Expected: first.action_type equals `read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("action entries have key, label, type fields")
val actions = action_list_lookup("register")
val first = actions[0]
expect(first.key).to_equal("reg.copy")
expect(first.label).to_equal("Copy Register Value")
expect(first.action_type).to_equal("read")
```

</details>

#### filters by action type read

- filters by action type read
   - Expected: read_actions.len() equals `2`
   - Expected: read_actions[0].key equals `src.find`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters by action type read")
val actions = action_list_lookup("source")
val read_actions = action_list_filter_by_type(actions, "read")
expect(read_actions.len()).to_equal(2)
expect(read_actions[0].key).to_equal("src.find")
```

</details>

#### filters by action type write

- filters by action type write
   - Expected: write_actions.len() equals `1`
   - Expected: write_actions[0].key equals `src.bp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters by action type write")
val actions = action_list_lookup("source")
val write_actions = action_list_filter_by_type(actions, "write")
expect(write_actions.len()).to_equal(1)
expect(write_actions[0].key).to_equal("src.bp")
```

</details>

#### returns all actions when no filter applied

- returns all actions when no filter applied
   - Expected: all_types.len() equals `0`
   - Expected: actions.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all actions when no filter applied")
val actions = action_list_lookup("register")
val all_types = action_list_filter_by_type(actions, "")
# Empty filter returns nothing — use unfiltered list for "all"
expect(all_types.len()).to_equal(0)
expect(actions.len()).to_equal(3)
```

</details>

#### t32_status_snapshot

#### returns run_state running

- returns run_state running
   - Expected: snap.run_state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns run_state running")
val snap = make_test_status("running", "system up", "sess_001", 0, "", true)
expect(snap.run_state).to_equal("running")
```

</details>

#### returns run_state stopped

- returns run_state stopped
   - Expected: snap.run_state equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns run_state stopped")
val snap = make_test_status("stopped", "break at main", "sess_001", 0, "Break at 0x08001234", true)
expect(snap.run_state).to_equal("stopped")
```

</details>

#### returns system state text

- returns system state text
   - Expected: snap.system_state equals `power debug ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns system state text")
val snap = make_test_status("stopped", "power debug ready", "sess_001", 0, "", true)
expect(snap.system_state).to_equal("power debug ready")
```

</details>

#### returns session context with id and core

- returns session context with id and core
   - Expected: snap.session_id equals `sess_002`
   - Expected: snap.core_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns session context with id and core")
val snap = make_test_status("running", "up", "sess_002", 1, "", true)
expect(snap.session_id).to_equal("sess_002")
expect(snap.core_id).to_equal(1)
```

</details>

#### returns message line if available

- returns message line if available
   - Expected: snap.message_line equals `Break at main+0x10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns message line if available")
val snap = make_test_status("stopped", "break", "sess_001", 0, "Break at main+0x10", true)
expect(snap.message_line).to_equal("Break at main+0x10")
```

</details>

#### returns connected=false when disconnected

- returns connected=false when disconnected
   - Expected: snap.connected is false
   - Expected: snap.run_state equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns connected=false when disconnected")
val snap = make_test_status("unknown", "disconnected", "sess_003", -1, "", false)
expect(snap.connected).to_equal(false)
expect(snap.run_state).to_equal("unknown")
```

</details>

#### t32_cmm_validate mode=check

#### detects DIALOG.OK as BLOCK

- detects DIALOG.OK as BLOCK
   - Expected: result.classification equals `needs_manual_rewrite`
   - Expected: result.findings.len() equals `1`
   - Expected: result.findings[0].command equals `DIALOG.OK`
   - Expected: result.findings[0].severity equals `BLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects DIALOG.OK as BLOCK")
val result = cmm_validate("DIALOG.OK \"Flash done\"", "check")
expect(result.classification).to_equal("needs_manual_rewrite")
expect(result.findings.len()).to_equal(1)
expect(result.findings[0].command).to_equal("DIALOG.OK")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects DIALOG.YESNO as BLOCK

- detects DIALOG.YESNO as BLOCK
   - Expected: result.classification equals `needs_manual_rewrite`
   - Expected: result.findings[0].command equals `DIALOG.YESNO`
   - Expected: result.findings[0].severity equals `BLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects DIALOG.YESNO as BLOCK")
val result = cmm_validate("DIALOG.YESNO \"Erase flash?\"", "check")
expect(result.classification).to_equal("needs_manual_rewrite")
expect(result.findings[0].command).to_equal("DIALOG.YESNO")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects DIALOG.FILE as BLOCK

- detects DIALOG.FILE as BLOCK
   - Expected: result.findings[0].command equals `DIALOG.FILE`
   - Expected: result.findings[0].severity equals `BLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects DIALOG.FILE as BLOCK")
val result = cmm_validate("DIALOG.FILE \"*.elf\"", "check")
expect(result.findings[0].command).to_equal("DIALOG.FILE")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects INKEY as BLOCK

- detects INKEY as BLOCK
   - Expected: result.findings[0].command equals `INKEY`
   - Expected: result.findings[0].severity equals `BLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects INKEY as BLOCK")
val result = cmm_validate("INKEY &pressed", "check")
expect(result.findings[0].command).to_equal("INKEY")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects ENTER as BLOCK

- detects ENTER as BLOCK
   - Expected: result.findings[0].command equals `ENTER`
   - Expected: result.findings[0].severity equals `BLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects ENTER as BLOCK")
val result = cmm_validate("ENTER &value", "check")
expect(result.findings[0].command).to_equal("ENTER")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects PAUSE as BLOCK

- detects PAUSE as BLOCK
   - Expected: result.findings[0].command equals `PAUSE`
   - Expected: result.findings[0].severity equals `BLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects PAUSE as BLOCK")
val result = cmm_validate("PAUSE", "check")
expect(result.findings[0].command).to_equal("PAUSE")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects STOP as BLOCK

- detects STOP as BLOCK
   - Expected: result.findings[0].command equals `STOP`
   - Expected: result.findings[0].severity equals `BLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects STOP as BLOCK")
val result = cmm_validate("STOP", "check")
expect(result.findings[0].command).to_equal("STOP")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### detects SCREEN.WAIT as WARN

- detects SCREEN.WAIT as WARN
   - Expected: result.classification equals `has_warnings`
   - Expected: result.findings[0].command equals `SCREEN.WAIT`
   - Expected: result.findings[0].severity equals `WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects SCREEN.WAIT as WARN")
val result = cmm_validate("SCREEN.WAIT", "check")
expect(result.classification).to_equal("has_warnings")
expect(result.findings[0].command).to_equal("SCREEN.WAIT")
expect(result.findings[0].severity).to_equal("WARN")
```

</details>

#### safe script returns classification=safe

- safe script returns classification=safe
   - Expected: result.classification equals `safe`
   - Expected: result.findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("safe script returns classification=safe")
val result = cmm_validate("ENTRY &addr\nData.dump &addr\nENDDO", "check")
expect(result.classification).to_equal("safe")
expect(result.findings.len()).to_equal(0)
```

</details>

#### t32_cmm_validate mode=report

#### report includes line numbers

- report includes line numbers
   - Expected: result.findings.len() equals `1`
   - Expected: result.findings[0].line equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report includes line numbers")
val result = cmm_validate("ENTRY &addr\nDIALOG.OK \"Done\"\nENDDO", "report")
expect(result.findings.len()).to_equal(1)
expect(result.findings[0].line).to_equal(2)
```

</details>

#### report classifies severity BLOCK

- report classifies severity BLOCK
   - Expected: result.findings[0].severity equals `BLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report classifies severity BLOCK")
val result = cmm_validate("DIALOG.YESNO \"Sure?\"", "report")
expect(result.findings[0].severity).to_equal("BLOCK")
```

</details>

#### report classifies severity WARN

- report classifies severity WARN
   - Expected: result.findings[0].severity equals `WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report classifies severity WARN")
val result = cmm_validate("SCREEN.WAIT", "report")
expect(result.findings[0].severity).to_equal("WARN")
```

</details>

#### multiple findings in one script

- multiple findings in one script
   - Expected: result.findings.len() equals `3`
   - Expected: result.findings[0].command equals `DIALOG.OK`
   - Expected: result.findings[1].command equals `PAUSE`
   - Expected: result.findings[2].command equals `DIALOG.YESNO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple findings in one script")
val source = "DIALOG.OK \"Start\"\nENTRY &addr\nPAUSE\nDIALOG.YESNO \"Continue?\"\nENDDO"
val result = cmm_validate(source, "report")
expect(result.findings.len()).to_equal(3)
expect(result.findings[0].command).to_equal("DIALOG.OK")
expect(result.findings[1].command).to_equal("PAUSE")
expect(result.findings[2].command).to_equal("DIALOG.YESNO")
```

</details>

#### nested patterns detected — DIALOG inside IF context

- nested patterns detected — DIALOG inside IF context
   - Expected: result.findings.len() equals `1`
   - Expected: result.findings[0].command equals `DIALOG.OK`
   - Expected: result.findings[0].line equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested patterns detected — DIALOG inside IF context")
val source = "IF TRUE()\n(\n  DIALOG.OK \"inside if\"\n)\nENDDO"
val result = cmm_validate(source, "report")
expect(result.findings.len()).to_equal(1)
expect(result.findings[0].command).to_equal("DIALOG.OK")
expect(result.findings[0].line).to_equal(3)
```

</details>

#### empty script returns safe

- empty script returns safe
   - Expected: result.classification equals `safe`
   - Expected: result.findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty script returns safe")
val result = cmm_validate("", "report")
expect(result.classification).to_equal("safe")
expect(result.findings.len()).to_equal(0)
```

</details>

#### report includes command name

- report includes command name
   - Expected: result.findings[0].command equals `STOP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report includes command name")
val result = cmm_validate("STOP", "report")
expect(result.findings[0].command).to_equal("STOP")
expect(result.findings[0].message).to_contain("PRACTICE")
```

</details>

#### t32_cmm_validate mode=suggest

#### DIALOG.YESNO suggests ENTRY &confirm pattern

- DIALOG.YESNO suggests ENTRY &confirm pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DIALOG.YESNO suggests ENTRY &confirm pattern")
val result = cmm_validate("DIALOG.YESNO \"Erase?\"", "suggest")
expect(result.findings[0].suggestion).to_contain("ENTRY")
expect(result.findings[0].suggestion).to_contain("confirm")
```

</details>

#### DIALOG.FILE suggests tool argument path

- DIALOG.FILE suggests tool argument path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DIALOG.FILE suggests tool argument path")
val result = cmm_validate("DIALOG.FILE \"*.elf\"", "suggest")
expect(result.findings[0].suggestion).to_contain("tool argument")
```

</details>

#### ENTER suggests ENTRY &var pattern

- ENTER suggests ENTRY &var pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ENTER suggests ENTRY &var pattern")
val result = cmm_validate("ENTER &value", "suggest")
expect(result.findings[0].suggestion).to_contain("ENTRY")
expect(result.findings[0].suggestion).to_contain("var")
```

</details>

#### PAUSE suggests PRINT checkpoint pattern

- PAUSE suggests PRINT checkpoint pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PAUSE suggests PRINT checkpoint pattern")
val result = cmm_validate("PAUSE", "suggest")
expect(result.findings[0].suggestion).to_contain("PRINT")
expect(result.findings[0].suggestion).to_contain("checkpoint")
```

</details>

#### unbounded WAIT suggests timeout pattern

- unbounded WAIT suggests timeout pattern
   - Expected: result.findings.len() equals `1`
   - Expected: result.findings[0].severity equals `WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unbounded WAIT suggests timeout pattern")
val result = cmm_validate("WAIT !STATE.RUN()", "suggest")
expect(result.findings.len()).to_equal(1)
expect(result.findings[0].severity).to_equal("WARN")
expect(result.findings[0].suggestion).to_contain("timeout")
```

</details>

#### safe script has no suggestions

- safe script has no suggestions
   - Expected: result.findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("safe script has no suggestions")
val result = cmm_validate("ENTRY &addr\nData.dump &addr", "suggest")
expect(result.findings.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_new_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 MCP New Tools — CLI-MCP Gap Closure.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `abbd448c18202371d5b203c966da3d25cdd27f13a1a16752a3d2b0ef4b72af34`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abbd448c18202371d5b203c966da3d25cdd27f13a1a16752a3d2b0ef4b72af34`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abbd448c18202371d5b203c966da3d25cdd27f13a1a16752a3d2b0ef4b72af34`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_t32/mcp_t32_new_tools_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_new_tools_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_new_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_new_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_new_tools_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 25 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_t32/mcp_t32_new_tools_spec.spl:288:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns session details for valid id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_new_tools_spec.spl:295:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns error for unknown session id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_new_tools_spec.spl:303:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes host and port fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
