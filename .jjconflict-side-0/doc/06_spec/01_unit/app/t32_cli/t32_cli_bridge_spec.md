# T32 Cli Bridge Specification

> 1. Ok

<!-- sdn-diagram:id=t32_cli_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_cli_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_cli_bridge_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_cli_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Bridge Specification

## Scenarios

### T32 CLI Bridge

#### session-free functions

#### bridge_sessions_list returns Ok with empty session list

1. Ok
   - Expected: r.kind equals `scalar`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
STUB_SESSIONS = []
STUB_CURRENT_SESSION = ""
val result = stub_sessions_list()
match result:
    Ok(r):
        expect(r.kind).to_equal("scalar")
        expect(r.scalar_value).to_contain("No sessions")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### bridge_resources_list returns Ok with resource URIs

1. Ok
   - Expected: r.kind equals `list`
   - Expected: r.items.len() equals `3`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_resources_list()
match result:
    Ok(r):
        expect(r.kind).to_equal("list")
        expect(r.items.len()).to_equal(3)
        expect(r.items[0]).to_contain("t32:///sessions")
        expect(r.items[1]).to_contain("t32:///windows")
        expect(r.items[2]).to_contain("t32:///history")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### bridge_window_list returns Ok with window entries from catalog

1. Ok
   - Expected: r.kind equals `table`
   - Expected: r.title equals `Windows`
   - Expected: r.rows[0][0] equals `Key`
   - Expected: r.rows[0][1] equals `Title`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_window_list()
match result:
    Ok(r):
        expect(r.kind).to_equal("table")
        expect(r.title).to_equal("Windows")
        # Header + 3 data rows
        expect(r.rows.len()).to_be_greater_than(1)
        # First row is header
        expect(r.rows[0][0]).to_equal("Key")
        expect(r.rows[0][1]).to_equal("Title")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### bridge_cmm_commands returns Ok with command database entries

1. Ok
   - Expected: r.kind equals `table`
   - Expected: r.rows[0][0] equals `Name`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_cmm_commands("", "")
match result:
    Ok(r):
        expect(r.kind).to_equal("table")
        expect(r.title).to_contain("CMM Commands")
        # Header + at least 1 data row
        expect(r.rows.len()).to_be_greater_than(1)
        expect(r.rows[0][0]).to_equal("Name")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### bridge_cmm_commands filters by group

1. Ok
   - Expected: r.kind equals `table`
   - Expected: r.rows[1][2] equals `Break`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_cmm_commands("Break", "")
match result:
    Ok(r):
        expect(r.kind).to_equal("table")
        # Header + Break commands only
        expect(r.rows.len()).to_be_greater_than(1)
        expect(r.rows[1][2]).to_equal("Break")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### session-dependent functions return Err without session

#### bridge_cmd_run without session returns Err

1. Ok
   - Expected: "should error" equals `got Ok`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
STUB_SESSIONS = []
STUB_CURRENT_SESSION = ""
val result = stub_cmd_run("Break.Set 0x1000")
match result:
    Ok(r):
        expect("should error").to_equal("got Ok")
    Err(e):
        expect(e).to_contain("session")
        expect(e.len()).to_be_greater_than(0)
```

</details>

#### bridge_eval without session returns Err

1. Ok
   - Expected: "should error" equals `got Ok`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
STUB_SESSIONS = []
STUB_CURRENT_SESSION = ""
val result = stub_eval("Register.PP()")
match result:
    Ok(r):
        expect("should error").to_equal("got Ok")
    Err(e):
        expect(e).to_contain("session")
        expect(e.len()).to_be_greater_than(0)
```

</details>

#### bridge_field_get without session returns Err

1. Ok
   - Expected: "should error" equals `got Ok`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
STUB_SESSIONS = []
STUB_CURRENT_SESSION = ""
val result = stub_field_get("pc")
match result:
    Ok(r):
        expect("should error").to_equal("got Ok")
    Err(e):
        expect(e).to_contain("session")
        expect(e.len()).to_be_greater_than(0)
```

</details>

#### bridge_error_check without session returns Err

1. Ok
   - Expected: "should error" equals `got Ok`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
STUB_SESSIONS = []
STUB_CURRENT_SESSION = ""
val result = stub_error_check()
match result:
    Ok(r):
        expect("should error").to_equal("got Ok")
    Err(e):
        expect(e).to_contain("session")
```

</details>

#### bridge_status_snapshot without session returns Err

1. Ok
   - Expected: "should error" equals `got Ok`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
STUB_SESSIONS = []
STUB_CURRENT_SESSION = ""
val result = stub_status_snapshot()
match result:
    Ok(r):
        expect("should error").to_equal("got Ok")
    Err(e):
        expect(e).to_contain("session")
```

</details>

#### history and jobs (no session needed for empty results)

#### bridge_history_tail returns Ok with empty history

1. Ok
   - Expected: r.kind equals `table`
   - Expected: r.rows.len() equals `1`
   - Expected: r.rows[0][0] equals `Command`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
STUB_HISTORY = []
val result = stub_history_tail(10)
match result:
    Ok(r):
        expect(r.kind).to_equal("table")
        expect(r.title).to_contain("History")
        # Only header row when history is empty
        expect(r.rows.len()).to_equal(1)
        expect(r.rows[0][0]).to_equal("Command")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### bridge_job_list returns Ok with empty job list

1. Ok
   - Expected: r.kind equals `scalar`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_job_list("")
match result:
    Ok(r):
        expect(r.kind).to_equal("scalar")
        expect(r.scalar_value).to_contain("No jobs")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### CMM validation (pure logic, no hardware)

#### bridge_cmm_validate with safe source returns safe classification

1. Ok
   - Expected: r.kind equals `table`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "; Comment\nBreak.Set 0x1000\nGo"
val result = stub_cmm_validate(source, "check")
match result:
    Ok(r):
        expect(r.kind).to_equal("table")
        expect(r.title).to_contain("safe")
        expect(r.gui_status).to_contain("classification: safe")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### bridge_cmm_validate detects blocking commands

1. Ok
   - Expected: r.kind equals `table`
   - Expected: r.rows.len() equals `2`
   - Expected: r.rows[1][1] equals `DIALOG.OK`
   - Expected: r.rows[1][2] equals `BLOCK`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "DIALOG.OK \"Press OK to continue\""
val result = stub_cmm_validate(source, "check")
match result:
    Ok(r):
        expect(r.kind).to_equal("table")
        expect(r.title).to_contain("needs_manual_rewrite")
        # Header + 1 finding
        expect(r.rows.len()).to_equal(2)
        expect(r.rows[1][1]).to_equal("DIALOG.OK")
        expect(r.rows[1][2]).to_equal("BLOCK")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### bridge_cmm_validate with many blockers marks unsafe_for_headless

1. Ok
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "DIALOG.OK \"a\"\nDIALOG.YESNO \"b\"\nDIALOG.FILE \"c\"\nINKEY\nSCREEN.WAIT"
val result = stub_cmm_validate(source, "check")
match result:
    Ok(r):
        expect(r.title).to_contain("unsafe_for_headless")
        expect(r.gui_status).to_contain("classification: unsafe_for_headless")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

#### bridge_cmm_validate with empty source returns Err

1. Ok
   - Expected: "should error" equals `got Ok`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_cmm_validate("", "check")
match result:
    Ok(r):
        expect("should error").to_equal("got Ok")
    Err(e):
        expect(e).to_contain("source is required")
```

</details>

#### bridge_cmm_validate rejects invalid mode

1. Ok
   - Expected: "should error" equals `got Ok`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_cmm_validate("Break.Set", "invalid")
match result:
    Ok(r):
        expect("should error").to_equal("got Ok")
    Err(e):
        expect(e).to_contain("Invalid mode")
        expect(e).to_contain("check, report, suggest")
```

</details>

#### dialog parse (requires source input)

#### bridge_dialog_parse with empty source returns Err

1. Ok
   - Expected: "should error" equals `got Ok`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_dialog_parse("")
match result:
    Ok(r):
        expect("should error").to_equal("got Ok")
    Err(e):
        expect(e).to_contain("source is required")
```

</details>

#### bridge_dialog_parse with non-empty source returns a table result

1. Ok
   - Expected: r.kind equals `table`
2. Err
   - Expected: "should not error" equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = stub_dialog_parse("DIALOG.view\n(&DEFPOS.X\n)")
match result:
    Ok(r):
        expect(r.kind).to_equal("table")
        expect(r.title).to_contain("Dialog Elements")
    Err(e):
        expect("should not error").to_equal(e)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/t32_cli_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 CLI Bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
