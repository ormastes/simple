# Mcp T32 Status Bar Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_status_bar_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_status_bar_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_status_bar_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_status_bar_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_msg_type(0)).to_equal("info")
```

</details>

#### maps type 1 to warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_msg_type(1)).to_equal("warning")
```

</details>

#### maps type 2 to error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_msg_type(2)).to_equal("error")
```

</details>

#### maps type 3 to info as default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_msg_type(3)).to_equal("info")
```

</details>

#### maps type -1 to info as default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_msg_type(-1)).to_equal("info")
```

</details>

#### maps type 100 to info as default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_msg_type(100)).to_equal("info")
```

</details>

#### target state parsing

#### TRUE means running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("TRUE")).to_equal("running")
```

</details>

#### true means running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("true")).to_equal("running")
```

</details>

#### TRUE. means running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("TRUE.")).to_equal("running")
```

</details>

#### true. means running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("true.")).to_equal("running")
```

</details>

#### FALSE means stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("FALSE")).to_equal("stopped")
```

</details>

#### false means stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("false")).to_equal("stopped")
```

</details>

#### FALSE. means stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("FALSE.")).to_equal("stopped")
```

</details>

#### false. means stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("false.")).to_equal("stopped")
```

</details>

#### empty string means unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("")).to_equal("unknown")
```

</details>

#### whitespace only means unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("   ")).to_equal("unknown")
```

</details>

#### random text means unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("halted")).to_equal("unknown")
```

</details>

#### 1 means unknown not running

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("1")).to_equal("unknown")
```

</details>

#### 0 means unknown not stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("0")).to_equal("unknown")
```

</details>

#### trims leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("  TRUE")).to_equal("running")
```

</details>

#### trims trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("FALSE  ")).to_equal("stopped")
```

</details>

#### trims both sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sb_parse_target_state("  true.  ")).to_equal("running")
```

</details>

#### status bar JSON construction

#### builds gui_status object

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_gui_status_json("system halted", "info", "stopped", "HLL", "Up", "idle", "0")
expect(sb_contains(json, "\"message_line\":\"system halted\"")).to_equal(true)
expect(sb_contains(json, "\"mode\":\"HLL\"")).to_equal(true)
expect(sb_contains(json, "\"system\":\"Up\"")).to_equal(true)
expect(sb_contains(json, "\"target_state\":\"stopped\"")).to_equal(true)
```

</details>

#### builds valid JSON with info type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_status_bar_json("system halted", "info", "stopped")
expect(sb_contains(json, "\"status_bar\"")).to_equal(true)
expect(sb_contains(json, "\"target_state\":\"stopped\"")).to_equal(true)
```

</details>

#### builds valid JSON with warning type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_status_bar_json("breakpoint hit", "warning", "stopped")
expect(sb_contains(json, "\"type\":\"warning\"")).to_equal(true)
```

</details>

#### builds valid JSON with error type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_status_bar_json("connection lost", "error", "unknown")
expect(sb_contains(json, "\"type\":\"error\"")).to_equal(true)
expect(sb_contains(json, "\"target_state\":\"unknown\"")).to_equal(true)
```

</details>

#### includes message text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_status_bar_json("ready", "info", "running")
expect(sb_contains(json, "\"message\":\"ready\"")).to_equal(true)
```

</details>

#### includes running target state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_status_bar_json("executing", "info", "running")
expect(sb_contains(json, "\"target_state\":\"running\"")).to_equal(true)
```

</details>

#### handles empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_status_bar_json("", "info", "unknown")
expect(sb_contains(json, "\"message\":\"\"")).to_equal(true)
```

</details>

#### full response construction

#### includes gui_status object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_build_full_response("Break.Set main", "ok", "ready", "info", "stopped")
expect(sb_contains(resp, "\"gui_status\":")).to_equal(true)
expect(sb_contains(resp, "\"message_line\":\"ready\"")).to_equal(true)
```

</details>

#### includes command field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_build_full_response("Break.Set main", "ok", "ready", "info", "stopped")
expect(sb_contains(resp, "\"command\":\"Break.Set main\"")).to_equal(true)
```

</details>

#### includes output field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_build_full_response("EVAL 1+1", "2", "ready", "info", "stopped")
expect(sb_contains(resp, "\"output\":\"2\"")).to_equal(true)
```

</details>

#### includes status_bar object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_build_full_response("SYStem.Up", "", "system up", "info", "stopped")
expect(sb_contains(resp, "\"status_bar\":")).to_equal(true)
expect(sb_contains(resp, "\"message\":\"system up\"")).to_equal(true)
```

</details>

#### includes target_state field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_build_full_response("Go", "", "running", "info", "running")
expect(sb_contains(resp, "\"target_state\":\"running\"")).to_equal(true)
```

</details>

#### starts with opening brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_build_full_response("PING", "ok", "", "info", "unknown")
expect(resp.starts_with("{")).to_equal(true)
```

</details>

#### ends with closing brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_build_full_response("PING", "ok", "", "info", "unknown")
expect(resp.ends_with("}")).to_equal(true)
```

</details>

#### tool output normalization

#### injects gui_status into object payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_normalize_tool_output("{\"status\":\"ok\"}")
expect(sb_contains(resp, "\"status\":\"ok\"")).to_equal(true)
expect(sb_contains(resp, "\"gui_status\":")).to_equal(true)
```

</details>

#### wraps array payloads in items object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = sb_normalize_tool_output("[{\"id\":1}]")
expect(sb_contains(resp, "\"items\":[{\"id\":1}]")).to_equal(true)
expect(sb_contains(resp, "\"gui_status\":")).to_equal(true)
```

</details>

#### python binary configuration

#### env var overrides default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sb_resolve_python_binary("/usr/bin/python3.11", "")
expect(result).to_equal("/usr/bin/python3.11")
```

</details>

#### SDN config overrides default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sb_resolve_python_binary("", "/usr/bin/python3.10")
expect(result).to_equal("/usr/bin/python3.10")
```

</details>

#### env var overrides SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sb_resolve_python_binary("/env/python", "/sdn/python")
expect(result).to_equal("/env/python")
```

</details>

#### returns python3 as default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sb_resolve_python_binary("", "")
expect(result).to_equal("python3")
```

</details>

#### bridge path configuration

#### global config takes priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sb_resolve_bridge_path("/config/bridge.py", "/env/bridge.py")
expect(result).to_equal("/config/bridge.py")
```

</details>

#### falls back to env var

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sb_resolve_bridge_path("", "/env/bridge.py")
expect(result).to_equal("/env/bridge.py")
```

</details>

#### returns empty when both empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sb_resolve_bridge_path("", "")
expect(result).to_equal("")
```

</details>

#### backend type strings

#### ctypes is valid backend type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bt = "ctypes"
expect(bt).to_equal("ctypes")
```

</details>

#### t32rem is valid backend type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bt = "t32rem"
expect(bt).to_equal("t32rem")
```

</details>

#### python_rcl is valid backend type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bt = "python_rcl"
expect(bt).to_equal("python_rcl")
```

</details>

#### edge cases

#### status bar with all empty fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_status_bar_json("", "info", "unknown")
expect(sb_contains(json, "\"status_bar\"")).to_equal(true)
expect(sb_contains(json, "\"target_state\":\"unknown\"")).to_equal(true)
```

</details>

#### status bar message with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = sb_build_status_bar_json("error: timeout", "error", "unknown")
expect(sb_contains(json, "error: timeout")).to_equal(true)
```

</details>

#### long message preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/mcp_t32/mcp_t32_status_bar_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
