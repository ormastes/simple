# T32 MCP Server -- Tool Handler Unit Tests

> Tests for the T32 MCP server tool handlers: field mapping functions, window catalog, headless setup command generation, and CMM command database. All functions under test are pure (no I/O, no side effects).

<!-- sdn-diagram:id=t32_mcp_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_mcp_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_mcp_tools_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_mcp_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Server -- Tool Handler Unit Tests

Tests for the T32 MCP server tool handlers: field mapping functions, window catalog, headless setup command generation, and CMM command database. All functions under test are pure (no I/O, no side effects).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-MCP-002 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/t32_tools/t32_mcp_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the T32 MCP server tool handlers: field mapping functions,
window catalog, headless setup command generation, and CMM command database.
All functions under test are pure (no I/O, no side effects).

## Source

`examples/10_tooling/trace32_tools/t32_mcp/action_tools.spl`
`examples/10_tooling/trace32_tools/t32_mcp/headless_tools.spl`
`examples/10_tooling/trace32_tools/t32_mcp/window_tools.spl`

## Scenarios

### T32 MCP Field Mapping

#### t32_field_to_eval maps common fields

#### maps 'pc' to Register(PC) EVAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("pc")
expect(result).to_equal("Register(PC)")
```

</details>

#### maps 'sp' to Register(SP) EVAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("sp")
expect(result).to_equal("Register(SP)")
```

</details>

#### maps 'lr' to Register(LR)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("lr")
expect(result).to_equal("Register(LR)")
```

</details>

#### maps 'cpsr' to Register(CPSR)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("cpsr")
expect(result).to_equal("Register(CPSR)")
```

</details>

#### maps register.R0 to Register(R0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("register.R0")
expect(result).to_equal("Register(R0)")
```

</details>

#### maps var.x to Var.VALUE(x)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("var.x")
expect(result).to_equal("Var.VALUE(x)")
```

</details>

#### maps memory.0x1000 to Data.Long(0x1000)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("memory.0x1000")
expect(result).to_equal("Data.Long(0x1000)")
```

</details>

#### maps status.mode to DEBUGMODE()

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("status.mode")
expect(result).to_equal("DEBUGMODE()")
```

</details>

#### maps status.system to SYStem.MODE()

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("status.system")
expect(result).to_equal("SYStem.MODE()")
```

</details>

#### maps status.trace to Trace.STATE()

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("status.trace")
expect(result).to_equal("Trace.STATE()")
```

</details>

#### maps status.cursor to TRACK.ADDRESS()

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("status.cursor")
expect(result).to_equal("TRACK.ADDRESS()")
```

</details>

#### returns raw expression for unknown fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("PRACTICE.STATE()")
expect(result).to_equal("PRACTICE.STATE()")
```

</details>

#### status field helpers

#### recognizes status alias keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_status_field("status")).to_equal(true)
expect(t32_is_status_field("status.current")).to_equal(true)
expect(t32_is_status_field("mode")).to_equal(true)
expect(t32_is_status_field("cursor")).to_equal(true)
```

</details>

#### normalizes running state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_normalize_current_status("1", "RUN", "Attach")
expect(result).to_equal("running")
```

</details>

#### normalizes stopped state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_normalize_current_status("0", "Break", "Attach")
expect(result).to_equal("stopped")
```

</details>

#### normalizes disconnected state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_normalize_current_status("0", "Down", "Down")
expect(result).to_equal("disconnected")
```

</details>

#### maps toolbar buttons for running

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_toolbar_run_enabled("running")).to_equal("false")
expect(t32_toolbar_stop_enabled("running")).to_equal("true")
```

</details>

#### maps toolbar buttons for stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_toolbar_run_enabled("stopped")).to_equal("true")
expect(t32_toolbar_stop_enabled("stopped")).to_equal("false")
```

</details>

### T32 MCP Field Set Commands

#### t32_field_to_set_cmd maps to T32 commands

#### maps pc set to Register.Set PC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("pc", "0x8000")
expect(result).to_equal("Register.Set PC 0x8000")
```

</details>

#### maps sp set to Register.Set SP

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("sp", "0x20000")
expect(result).to_equal("Register.Set SP 0x20000")
```

</details>

#### maps register.R0 to Register.Set R0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("register.R0", "42")
expect(result).to_equal("Register.Set R0 42")
```

</details>

#### maps var.count to Var.Set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("var.count", "10")
expect(result).to_equal("Var.Set count = 10")
```

</details>

#### maps memory.0x1000 to Data.Set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("memory.0x1000", "0xDEAD")
expect(result).to_equal("Data.Set 0x1000 %Long 0xDEAD")
```

</details>

#### returns empty for unknown fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("unknown_field", "value")
expect(result).to_equal("")
```

</details>

### T32 MCP Window Catalog

#### hardcoded catalog

#### has 15 entries in hardcoded catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = t32_hardcoded_window_catalog()
expect(catalog.len()).to_equal(15)
```

</details>

#### finds register_view entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = t32_hardcoded_window_catalog()
var found = false
for entry in catalog:
    if entry.starts_with("register_view|"):
        found = true
expect(found).to_equal(true)
```

</details>

#### returns capture command for register_view

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = t32_hardcoded_window_catalog()
var found_capture = ""
for entry in catalog:
    if entry.starts_with("register_view|"):
        # Parse pipe-delimited: "key|title|kind|open_cmd|capture_cmd"
        val seg = entry.split("|")
        if seg.len() >= 5:
            found_capture = seg[4]
expect(found_capture).to_equal("WinPrint.Register.view")
```

</details>

#### SDN parsing

#### parses SDN catalog format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window my_win\n  title: Test Window\n  kind: custom\n  open_command: MyCmd\n  capture_command: WinPrint.MyCmd\n"
val catalog = t32_parse_window_sdn(sdn)
expect(catalog.len()).to_equal(1)
expect(catalog[0]).to_contain("my_win")
expect(catalog[0]).to_contain("Test Window")
```

</details>

### T32 MCP Headless Setup

#### helper functions

#### converts to lower case

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_to_lower("Hello WORLD")
expect(result).to_equal("hello world")
```

</details>

#### detects substring containment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_text_contains("hello world", "world")
expect(result).to_equal(true)
```

</details>

#### returns false for non-contained substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_text_contains("hello", "xyz")
expect(result).to_equal(false)
```

</details>

### T32 MCP CMM Command DB

#### database content

#### has 90+ commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = t32_build_cmm_command_db()
expect(db.len()).to_be_greater_than(90)
```

</details>

#### includes Data.dump command

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = t32_build_cmm_command_db()
var found = false
for cmd in db:
    if cmd.starts_with("Data.dump|"):
        found = true
expect(found).to_equal(true)
```

</details>

#### includes Break.Set command

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = t32_build_cmm_command_db()
var found = false
for cmd in db:
    if cmd.starts_with("Break.Set|"):
        found = true
expect(found).to_equal(true)
```

</details>

#### filtering

#### filters by group

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = t32_build_cmm_command_db()
var data_count: i64 = 0
for cmd in db:
    if t32_text_contains(cmd, "|Data|"):
        data_count = data_count + 1
expect(data_count).to_be_greater_than(5)
```

</details>

#### searches by substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = t32_build_cmm_command_db()
var flash_count: i64 = 0
for cmd in db:
    if t32_text_contains(t32_to_lower(cmd), "flash"):
        flash_count = flash_count + 1
expect(flash_count).to_be_greater_than(3)
```

</details>

#### returns empty for unknown group

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = t32_build_cmm_command_db()
var unknown_count: i64 = 0
for cmd in db:
    if t32_text_contains(cmd, "|NonExistentGroup|"):
        unknown_count = unknown_count + 1
expect(unknown_count).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
