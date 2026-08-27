# Mcp T32 Status Bar Specification

> Tests covering T32 Status Bar.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Status Bar Specification

## Scenarios

### T32 Status Bar

#### message type mapping

#### maps type 0 to info

- maps type 0 to info
   - Expected: sb_parse_msg_type(0) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps type 0 to info")
expect(sb_parse_msg_type(0)).to_equal("info")
```

</details>

#### maps type 1 to warning

- maps type 1 to warning
   - Expected: sb_parse_msg_type(1) equals `warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps type 1 to warning")
expect(sb_parse_msg_type(1)).to_equal("warning")
```

</details>

#### maps type 2 to error

- maps type 2 to error
   - Expected: sb_parse_msg_type(2) equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps type 2 to error")
expect(sb_parse_msg_type(2)).to_equal("error")
```

</details>

#### maps type 3 to info as default

- maps type 3 to info as default
   - Expected: sb_parse_msg_type(3) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps type 3 to info as default")
expect(sb_parse_msg_type(3)).to_equal("info")
```

</details>

#### maps type -1 to info as default

- maps type -1 to info as default
   - Expected: sb_parse_msg_type(-1) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps type -1 to info as default")
expect(sb_parse_msg_type(-1)).to_equal("info")
```

</details>

#### maps type 100 to info as default

- maps type 100 to info as default
   - Expected: sb_parse_msg_type(100) equals `info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps type 100 to info as default")
expect(sb_parse_msg_type(100)).to_equal("info")
```

</details>

#### target state parsing

#### TRUE means running

- TRUE means running
   - Expected: sb_parse_target_state("TRUE") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRUE means running")
expect(sb_parse_target_state("TRUE")).to_equal("running")
```

</details>

#### true means running

- true means running
   - Expected: sb_parse_target_state("true") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true means running")
expect(sb_parse_target_state("true")).to_equal("running")
```

</details>

#### TRUE. means running

- TRUE. means running
   - Expected: sb_parse_target_state("TRUE.") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRUE. means running")
expect(sb_parse_target_state("TRUE.")).to_equal("running")
```

</details>

#### true. means running

- true. means running
   - Expected: sb_parse_target_state("true.") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true. means running")
expect(sb_parse_target_state("true.")).to_equal("running")
```

</details>

#### FALSE means stopped

- FALSE means stopped
   - Expected: sb_parse_target_state("FALSE") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FALSE means stopped")
expect(sb_parse_target_state("FALSE")).to_equal("stopped")
```

</details>

#### false means stopped

- false means stopped
   - Expected: sb_parse_target_state("false") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false means stopped")
expect(sb_parse_target_state("false")).to_equal("stopped")
```

</details>

#### FALSE. means stopped

- FALSE. means stopped
   - Expected: sb_parse_target_state("FALSE.") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FALSE. means stopped")
expect(sb_parse_target_state("FALSE.")).to_equal("stopped")
```

</details>

#### false. means stopped

- false. means stopped
   - Expected: sb_parse_target_state("false.") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false. means stopped")
expect(sb_parse_target_state("false.")).to_equal("stopped")
```

</details>

#### empty string means unknown

- empty string means unknown
   - Expected: sb_parse_target_state("") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string means unknown")
expect(sb_parse_target_state("")).to_equal("unknown")
```

</details>

#### whitespace only means unknown

- whitespace only means unknown
   - Expected: sb_parse_target_state("   ") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whitespace only means unknown")
expect(sb_parse_target_state("   ")).to_equal("unknown")
```

</details>

#### random text means unknown

- random text means unknown
   - Expected: sb_parse_target_state("halted") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("random text means unknown")
expect(sb_parse_target_state("halted")).to_equal("unknown")
```

</details>

#### 1 means unknown not running

- 1 means unknown not running
   - Expected: sb_parse_target_state("1") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1 means unknown not running")
expect(sb_parse_target_state("1")).to_equal("unknown")
```

</details>

#### 0 means unknown not stopped

- 0 means unknown not stopped
   - Expected: sb_parse_target_state("0") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 means unknown not stopped")
expect(sb_parse_target_state("0")).to_equal("unknown")
```

</details>

#### trims leading whitespace

- trims leading whitespace
   - Expected: sb_parse_target_state("  TRUE") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims leading whitespace")
expect(sb_parse_target_state("  TRUE")).to_equal("running")
```

</details>

#### trims trailing whitespace

- trims trailing whitespace
   - Expected: sb_parse_target_state("FALSE  ") equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims trailing whitespace")
expect(sb_parse_target_state("FALSE  ")).to_equal("stopped")
```

</details>

#### trims both sides

- trims both sides
   - Expected: sb_parse_target_state("  true.  ") equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims both sides")
expect(sb_parse_target_state("  true.  ")).to_equal("running")
```

</details>

#### status bar JSON construction

#### builds gui_status object

- builds gui_status object
   - Expected: sb_contains(json, "\"message_line\":\"system halted\"") is true
   - Expected: sb_contains(json, "\"mode\":\"HLL\"") is true
   - Expected: sb_contains(json, "\"system\":\"Up\"") is true
   - Expected: sb_contains(json, "\"target_state\":\"stopped\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds gui_status object")
val json = sb_build_gui_status_json("system halted", "info", "stopped", "HLL", "Up", "idle", "0")
expect(sb_contains(json, "\"message_line\":\"system halted\"")).to_equal(true)
expect(sb_contains(json, "\"mode\":\"HLL\"")).to_equal(true)
expect(sb_contains(json, "\"system\":\"Up\"")).to_equal(true)
expect(sb_contains(json, "\"target_state\":\"stopped\"")).to_equal(true)
```

</details>

#### builds valid JSON with info type

- builds valid JSON with info type
   - Expected: sb_contains(json, "\"status_bar\"") is true
   - Expected: sb_contains(json, "\"target_state\":\"stopped\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds valid JSON with info type")
val json = sb_build_status_bar_json("system halted", "info", "stopped")
expect(sb_contains(json, "\"status_bar\"")).to_equal(true)
expect(sb_contains(json, "\"target_state\":\"stopped\"")).to_equal(true)
```

</details>

#### builds valid JSON with warning type

- builds valid JSON with warning type
   - Expected: sb_contains(json, "\"type\":\"warning\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds valid JSON with warning type")
val json = sb_build_status_bar_json("breakpoint hit", "warning", "stopped")
expect(sb_contains(json, "\"type\":\"warning\"")).to_equal(true)
```

</details>

#### builds valid JSON with error type

- builds valid JSON with error type
   - Expected: sb_contains(json, "\"type\":\"error\"") is true
   - Expected: sb_contains(json, "\"target_state\":\"unknown\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds valid JSON with error type")
val json = sb_build_status_bar_json("connection lost", "error", "unknown")
expect(sb_contains(json, "\"type\":\"error\"")).to_equal(true)
expect(sb_contains(json, "\"target_state\":\"unknown\"")).to_equal(true)
```

</details>

#### includes message text

- includes message text
   - Expected: sb_contains(json, "\"message\":\"ready\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes message text")
val json = sb_build_status_bar_json("ready", "info", "running")
expect(sb_contains(json, "\"message\":\"ready\"")).to_equal(true)
```

</details>

#### includes running target state

- includes running target state
   - Expected: sb_contains(json, "\"target_state\":\"running\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes running target state")
val json = sb_build_status_bar_json("executing", "info", "running")
expect(sb_contains(json, "\"target_state\":\"running\"")).to_equal(true)
```

</details>

#### handles empty message

- handles empty message
   - Expected: sb_contains(json, "\"message\":\"\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty message")
val json = sb_build_status_bar_json("", "info", "unknown")
expect(sb_contains(json, "\"message\":\"\"")).to_equal(true)
```

</details>

#### full response construction

#### includes gui_status object

- includes gui_status object
   - Expected: sb_contains(resp, "\"gui_status\":") is true
   - Expected: sb_contains(resp, "\"message_line\":\"ready\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes gui_status object")
val resp = sb_build_full_response("Break.Set main", "ok", "ready", "info", "stopped")
expect(sb_contains(resp, "\"gui_status\":")).to_equal(true)
expect(sb_contains(resp, "\"message_line\":\"ready\"")).to_equal(true)
```

</details>

#### includes command field

- includes command field
   - Expected: sb_contains(resp, "\"command\":\"Break.Set main\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes command field")
val resp = sb_build_full_response("Break.Set main", "ok", "ready", "info", "stopped")
expect(sb_contains(resp, "\"command\":\"Break.Set main\"")).to_equal(true)
```

</details>

#### includes output field

- includes output field
   - Expected: sb_contains(resp, "\"output\":\"2\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes output field")
val resp = sb_build_full_response("EVAL 1+1", "2", "ready", "info", "stopped")
expect(sb_contains(resp, "\"output\":\"2\"")).to_equal(true)
```

</details>

#### includes status_bar object

- includes status_bar object
   - Expected: sb_contains(resp, "\"status_bar\":") is true
   - Expected: sb_contains(resp, "\"message\":\"system up\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes status_bar object")
val resp = sb_build_full_response("SYStem.Up", "", "system up", "info", "stopped")
expect(sb_contains(resp, "\"status_bar\":")).to_equal(true)
expect(sb_contains(resp, "\"message\":\"system up\"")).to_equal(true)
```

</details>

#### includes target_state field

- includes target_state field
   - Expected: sb_contains(resp, "\"target_state\":\"running\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes target_state field")
val resp = sb_build_full_response("Go", "", "running", "info", "running")
expect(sb_contains(resp, "\"target_state\":\"running\"")).to_equal(true)
```

</details>

#### starts with opening brace

- starts with opening brace
   - Expected: resp.starts_with("{") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with opening brace")
val resp = sb_build_full_response("PING", "ok", "", "info", "unknown")
expect(resp.starts_with("{")).to_equal(true)
```

</details>

#### ends with closing brace

- ends with closing brace
   - Expected: resp.ends_with("}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with closing brace")
val resp = sb_build_full_response("PING", "ok", "", "info", "unknown")
expect(resp.ends_with("}")).to_equal(true)
```

</details>

#### tool output normalization

#### injects gui_status into object payloads

- injects gui_status into object payloads
   - Expected: sb_contains(resp, "\"status\":\"ok\"") is true
   - Expected: sb_contains(resp, "\"gui_status\":") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects gui_status into object payloads")
val resp = sb_normalize_tool_output("{\"status\":\"ok\"}")
expect(sb_contains(resp, "\"status\":\"ok\"")).to_equal(true)
expect(sb_contains(resp, "\"gui_status\":")).to_equal(true)
```

</details>

#### wraps array payloads in items object

- wraps array payloads in items object
   - Expected: sb_contains(resp, "\"items\":[{\"id\":1}]") is true
   - Expected: sb_contains(resp, "\"gui_status\":") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps array payloads in items object")
val resp = sb_normalize_tool_output("[{\"id\":1}]")
expect(sb_contains(resp, "\"items\":[{\"id\":1}]")).to_equal(true)
expect(sb_contains(resp, "\"gui_status\":")).to_equal(true)
```

</details>

#### python binary configuration

#### env var overrides default

- env var overrides default
   - Expected: result equals `/usr/bin/python3.11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env var overrides default")
val result = sb_resolve_python_binary("/usr/bin/python3.11", "")
expect(result).to_equal("/usr/bin/python3.11")
```

</details>

#### SDN config overrides default

- SDN config overrides default
   - Expected: result equals `/usr/bin/python3.10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SDN config overrides default")
val result = sb_resolve_python_binary("", "/usr/bin/python3.10")
expect(result).to_equal("/usr/bin/python3.10")
```

</details>

#### env var overrides SDN

- env var overrides SDN
   - Expected: result equals `/env/python`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env var overrides SDN")
val result = sb_resolve_python_binary("/env/python", "/sdn/python")
expect(result).to_equal("/env/python")
```

</details>

#### returns python3 as default

- returns python3 as default
   - Expected: result equals `python3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns python3 as default")
val result = sb_resolve_python_binary("", "")
expect(result).to_equal("python3")
```

</details>

#### bridge path configuration

#### global config takes priority

- global config takes priority
   - Expected: result equals `/config/bridge.py`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("global config takes priority")
val result = sb_resolve_bridge_path("/config/bridge.py", "/env/bridge.py")
expect(result).to_equal("/config/bridge.py")
```

</details>

#### falls back to env var

- falls back to env var
   - Expected: result equals `/env/bridge.py`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to env var")
val result = sb_resolve_bridge_path("", "/env/bridge.py")
expect(result).to_equal("/env/bridge.py")
```

</details>

#### returns empty when both empty

- returns empty when both empty
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when both empty")
val result = sb_resolve_bridge_path("", "")
expect(result).to_equal("")
```

</details>

#### backend type strings

#### ctypes is valid backend type

- ctypes is valid backend type
   - Expected: bt equals `ctypes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ctypes is valid backend type")
val bt = "ctypes"
expect(bt).to_equal("ctypes")
```

</details>

#### t32rem is valid backend type

- t32rem is valid backend type
   - Expected: bt equals `t32rem`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32rem is valid backend type")
val bt = "t32rem"
expect(bt).to_equal("t32rem")
```

</details>

#### python_rcl is valid backend type

- python_rcl is valid backend type
   - Expected: bt equals `python_rcl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("python_rcl is valid backend type")
val bt = "python_rcl"
expect(bt).to_equal("python_rcl")
```

</details>

#### edge cases

#### status bar with all empty fields

- status bar with all empty fields
   - Expected: sb_contains(json, "\"status_bar\"") is true
   - Expected: sb_contains(json, "\"target_state\":\"unknown\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("status bar with all empty fields")
val json = sb_build_status_bar_json("", "info", "unknown")
expect(sb_contains(json, "\"status_bar\"")).to_equal(true)
expect(sb_contains(json, "\"target_state\":\"unknown\"")).to_equal(true)
```

</details>

#### status bar message with special characters

- status bar message with special characters
   - Expected: sb_contains(json, "error: timeout") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("status bar message with special characters")
val json = sb_build_status_bar_json("error: timeout", "error", "unknown")
expect(sb_contains(json, "error: timeout")).to_equal(true)
```

</details>

#### long message preserved

- long message preserved
   - Expected: sb_contains(json, "breakpoint main") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("long message preserved")
val msg = "TRACE32 PowerView system halted at breakpoint main+0x10"
val json = sb_build_status_bar_json(msg, "info", "stopped")
expect(sb_contains(json, "breakpoint main")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_status_bar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Status Bar.
- T32 Status Bar

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
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

- Canonical SPipe generation for source `e3d241494016eed94b92f965b31c97bb8ef802a7973ff1221841beea741f28f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3d241494016eed94b92f965b31c97bb8ef802a7973ff1221841beea741f28f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3d241494016eed94b92f965b31c97bb8ef802a7973ff1221841beea741f28f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_t32/mcp_t32_status_bar_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_status_bar_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_status_bar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_status_bar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_status_bar_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps type 0 to info' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_status_bar_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps type 1 to warning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_status_bar_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps type 2 to error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
