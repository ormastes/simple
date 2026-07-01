# Mcp T32 Dialog Tools Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_dialog_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_dialog_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_dialog_tools_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_dialog_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Dialog Tools Specification

## Scenarios

### T32 Dialog Tools

#### label validation

#### accepts simple identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("mycheck")).to_equal(true)
```

</details>

#### accepts identifier with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("ok_btn")).to_equal(true)
```

</details>

#### accepts identifier with digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("field123")).to_equal(true)
```

</details>

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("")).to_equal(false)
```

</details>

#### rejects label with space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("my check")).to_equal(false)
```

</details>

#### rejects label with semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("label;rm")).to_equal(false)
```

</details>

#### rejects label with pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("label|cmd")).to_equal(false)
```

</details>

#### rejects label with ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("label&cmd")).to_equal(false)
```

</details>

#### rejects label with backtick

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("x`y")).to_equal(false)
```

</details>

#### rejects label with parenthesis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_validate_ident("fn(x)")).to_equal(false)
```

</details>

#### action validation

#### accepts set action

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_dialog_action("set")).to_equal(true)
```

</details>

#### accepts disable action

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_dialog_action("disable")).to_equal(true)
```

</details>

#### accepts enable action

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_dialog_action("enable")).to_equal(true)
```

</details>

#### accepts deselect action

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_dialog_action("deselect")).to_equal(true)
```

</details>

#### rejects unknown action

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_dialog_action("toggle")).to_equal(false)
```

</details>

#### rejects empty action

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_dialog_action("")).to_equal(false)
```

</details>

#### rejects click as action

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_dialog_action("click")).to_equal(false)
```

</details>

#### dialog_get command generation

#### builds boolean query

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_get_cmd("mycheck", "boolean")
expect(cmd).to_equal("EVAL DIALOG.BOOLEAN(mycheck)")
```

</details>

#### builds string query

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_get_cmd("myedit", "string")
expect(cmd).to_equal("EVAL DIALOG.STRING(myedit)")
```

</details>

#### builds value query

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_get_cmd("myval", "value")
expect(cmd).to_equal("EVAL DIALOG.VALUE(myval)")
```

</details>

#### returns empty for unknown type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_get_cmd("x", "integer")
expect(cmd).to_equal("")
```

</details>

#### dialog_set command generation

#### builds set command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_set_cmd("mycheck", "set")
expect(cmd).to_equal("DIALOG.Set mycheck")
```

</details>

#### builds disable command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_set_cmd("mycheck", "disable")
expect(cmd).to_equal("DIALOG.Disable mycheck")
```

</details>

#### builds enable command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_set_cmd("mycheck", "enable")
expect(cmd).to_equal("DIALOG.Enable mycheck")
```

</details>

#### builds deselect command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_set_cmd("mycheck", "deselect")
expect(cmd).to_equal("DIALOG.Deselect mycheck")
```

</details>

#### returns empty for invalid action

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_set_cmd("mycheck", "toggle")
expect(cmd).to_equal("")
```

</details>

#### dialog_click command generation

#### builds exist check command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_exist_cmd("ok_btn")
expect(cmd).to_equal("EVAL DIALOG.EXIST(ok_btn)")
```

</details>

#### builds execute command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = build_dialog_execute_cmd("ok_btn")
expect(cmd).to_equal("DIALOG.EXECUTE ok_btn")
```

</details>

#### exist result parsing

#### parses TRUE as exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_exist_result("TRUE")).to_equal(true)
```

</details>

#### parses true lowercase as exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_exist_result("true")).to_equal(true)
```

</details>

#### parses 1 as exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_exist_result("1")).to_equal(true)
```

</details>

#### parses FALSE as not exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_exist_result("FALSE")).to_equal(false)
```

</details>

#### parses 0 as not exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_exist_result("0")).to_equal(false)
```

</details>

#### parses empty as not exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_exist_result("")).to_equal(false)
```

</details>

#### error messages

#### not found error includes label

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = dialog_error_not_found("mycheck")
expect(err).to_start_with("T4100")
expect(err).to_contain("mycheck")
```

</details>

#### no dialog error includes hint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = dialog_error_no_dialog()
expect(err).to_start_with("T4101")
expect(err).to_contain("t32_cmm_run")
```

</details>

#### invalid action error includes action name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = dialog_error_invalid_action("toggle")
expect(err).to_start_with("T4102")
expect(err).to_contain("toggle")
```

</details>

#### mode parsing

#### defaults to sync

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_dialog_mode("")).to_equal("sync")
```

</details>

#### accepts async

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_dialog_mode("async")).to_equal("async")
```

</details>

#### rejects invalid mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_dialog_mode("background")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_dialog_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Dialog Tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
