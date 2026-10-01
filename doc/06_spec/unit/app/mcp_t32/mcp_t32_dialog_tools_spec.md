# Mcp T32 Dialog Tools Specification

> Tests covering T32 Dialog Tools.

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

- accepts simple identifier
   - Expected: test_validate_ident("mycheck") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts simple identifier")
expect(test_validate_ident("mycheck")).to_equal(true)
```

</details>

#### accepts identifier with underscore

- accepts identifier with underscore
   - Expected: test_validate_ident("ok_btn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts identifier with underscore")
expect(test_validate_ident("ok_btn")).to_equal(true)
```

</details>

#### accepts identifier with digits

- accepts identifier with digits
   - Expected: test_validate_ident("field123") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts identifier with digits")
expect(test_validate_ident("field123")).to_equal(true)
```

</details>

#### rejects empty string

- rejects empty string
   - Expected: test_validate_ident("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty string")
expect(test_validate_ident("")).to_equal(false)
```

</details>

#### rejects label with space

- rejects label with space
   - Expected: test_validate_ident("my check") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects label with space")
expect(test_validate_ident("my check")).to_equal(false)
```

</details>

#### rejects label with semicolon

- rejects label with semicolon
   - Expected: test_validate_ident("label;rm") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects label with semicolon")
expect(test_validate_ident("label;rm")).to_equal(false)
```

</details>

#### rejects label with pipe

- rejects label with pipe
   - Expected: test_validate_ident("label|cmd") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects label with pipe")
expect(test_validate_ident("label|cmd")).to_equal(false)
```

</details>

#### rejects label with ampersand

- rejects label with ampersand
   - Expected: test_validate_ident("label&cmd") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects label with ampersand")
expect(test_validate_ident("label&cmd")).to_equal(false)
```

</details>

#### rejects label with backtick

- rejects label with backtick
   - Expected: test_validate_ident("x`y") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects label with backtick")
expect(test_validate_ident("x`y")).to_equal(false)
```

</details>

#### rejects label with parenthesis

- rejects label with parenthesis
   - Expected: test_validate_ident("fn(x)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects label with parenthesis")
expect(test_validate_ident("fn(x)")).to_equal(false)
```

</details>

#### action validation

#### accepts set action

- accepts set action
   - Expected: validate_dialog_action("set") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts set action")
expect(validate_dialog_action("set")).to_equal(true)
```

</details>

#### accepts disable action

- accepts disable action
   - Expected: validate_dialog_action("disable") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts disable action")
expect(validate_dialog_action("disable")).to_equal(true)
```

</details>

#### accepts enable action

- accepts enable action
   - Expected: validate_dialog_action("enable") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts enable action")
expect(validate_dialog_action("enable")).to_equal(true)
```

</details>

#### accepts deselect action

- accepts deselect action
   - Expected: validate_dialog_action("deselect") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts deselect action")
expect(validate_dialog_action("deselect")).to_equal(true)
```

</details>

#### rejects unknown action

- rejects unknown action
   - Expected: validate_dialog_action("toggle") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown action")
expect(validate_dialog_action("toggle")).to_equal(false)
```

</details>

#### rejects empty action

- rejects empty action
   - Expected: validate_dialog_action("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty action")
expect(validate_dialog_action("")).to_equal(false)
```

</details>

#### rejects click as action

- rejects click as action
   - Expected: validate_dialog_action("click") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects click as action")
expect(validate_dialog_action("click")).to_equal(false)
```

</details>

#### dialog_get command generation

#### builds boolean query

- builds boolean query
   - Expected: cmd equals `EVAL DIALOG.BOOLEAN(mycheck)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds boolean query")
val cmd = build_dialog_get_cmd("mycheck", "boolean")
expect(cmd).to_equal("EVAL DIALOG.BOOLEAN(mycheck)")
```

</details>

#### builds string query

- builds string query
   - Expected: cmd equals `EVAL DIALOG.STRING(myedit)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds string query")
val cmd = build_dialog_get_cmd("myedit", "string")
expect(cmd).to_equal("EVAL DIALOG.STRING(myedit)")
```

</details>

#### builds value query

- builds value query
   - Expected: cmd equals `EVAL DIALOG.VALUE(myval)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds value query")
val cmd = build_dialog_get_cmd("myval", "value")
expect(cmd).to_equal("EVAL DIALOG.VALUE(myval)")
```

</details>

#### returns empty for unknown type

- returns empty for unknown type
   - Expected: cmd equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unknown type")
val cmd = build_dialog_get_cmd("x", "integer")
expect(cmd).to_equal("")
```

</details>

#### dialog_set command generation

#### builds set command

- builds set command
   - Expected: cmd equals `DIALOG.Set mycheck`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds set command")
val cmd = build_dialog_set_cmd("mycheck", "set")
expect(cmd).to_equal("DIALOG.Set mycheck")
```

</details>

#### builds disable command

- builds disable command
   - Expected: cmd equals `DIALOG.Disable mycheck`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds disable command")
val cmd = build_dialog_set_cmd("mycheck", "disable")
expect(cmd).to_equal("DIALOG.Disable mycheck")
```

</details>

#### builds enable command

- builds enable command
   - Expected: cmd equals `DIALOG.Enable mycheck`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds enable command")
val cmd = build_dialog_set_cmd("mycheck", "enable")
expect(cmd).to_equal("DIALOG.Enable mycheck")
```

</details>

#### builds deselect command

- builds deselect command
   - Expected: cmd equals `DIALOG.Deselect mycheck`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds deselect command")
val cmd = build_dialog_set_cmd("mycheck", "deselect")
expect(cmd).to_equal("DIALOG.Deselect mycheck")
```

</details>

#### returns empty for invalid action

- returns empty for invalid action
   - Expected: cmd equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for invalid action")
val cmd = build_dialog_set_cmd("mycheck", "toggle")
expect(cmd).to_equal("")
```

</details>

#### dialog_click command generation

#### builds exist check command

- builds exist check command
   - Expected: cmd equals `EVAL DIALOG.EXIST(ok_btn)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds exist check command")
val cmd = build_dialog_exist_cmd("ok_btn")
expect(cmd).to_equal("EVAL DIALOG.EXIST(ok_btn)")
```

</details>

#### builds execute command

- builds execute command
   - Expected: cmd equals `DIALOG.EXECUTE ok_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds execute command")
val cmd = build_dialog_execute_cmd("ok_btn")
expect(cmd).to_equal("DIALOG.EXECUTE ok_btn")
```

</details>

#### exist result parsing

#### parses TRUE as exists

- parses TRUE as exists
   - Expected: parse_exist_result("TRUE") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses TRUE as exists")
expect(parse_exist_result("TRUE")).to_equal(true)
```

</details>

#### parses true lowercase as exists

- parses true lowercase as exists
   - Expected: parse_exist_result("true") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses true lowercase as exists")
expect(parse_exist_result("true")).to_equal(true)
```

</details>

#### parses 1 as exists

- parses 1 as exists
   - Expected: parse_exist_result("1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses 1 as exists")
expect(parse_exist_result("1")).to_equal(true)
```

</details>

#### parses FALSE as not exists

- parses FALSE as not exists
   - Expected: parse_exist_result("FALSE") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses FALSE as not exists")
expect(parse_exist_result("FALSE")).to_equal(false)
```

</details>

#### parses 0 as not exists

- parses 0 as not exists
   - Expected: parse_exist_result("0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses 0 as not exists")
expect(parse_exist_result("0")).to_equal(false)
```

</details>

#### parses empty as not exists

- parses empty as not exists
   - Expected: parse_exist_result("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty as not exists")
expect(parse_exist_result("")).to_equal(false)
```

</details>

#### error messages

#### not found error includes label

- not found error includes label


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not found error includes label")
val err = dialog_error_not_found("mycheck")
expect(err).to_start_with("T4100")
expect(err).to_contain("mycheck")
```

</details>

#### no dialog error includes hint

- no dialog error includes hint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no dialog error includes hint")
val err = dialog_error_no_dialog()
expect(err).to_start_with("T4101")
expect(err).to_contain("t32_cmm_run")
```

</details>

#### invalid action error includes action name

- invalid action error includes action name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid action error includes action name")
val err = dialog_error_invalid_action("toggle")
expect(err).to_start_with("T4102")
expect(err).to_contain("toggle")
```

</details>

#### mode parsing

#### defaults to sync

- defaults to sync
   - Expected: parse_dialog_mode("") equals `sync`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to sync")
expect(parse_dialog_mode("")).to_equal("sync")
```

</details>

#### accepts async

- accepts async
   - Expected: parse_dialog_mode("async") equals `async`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts async")
expect(parse_dialog_mode("async")).to_equal("async")
```

</details>

#### rejects invalid mode

- rejects invalid mode
   - Expected: parse_dialog_mode("background") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid mode")
expect(parse_dialog_mode("background")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_dialog_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Dialog Tools.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aab2eb48121c86dd4cfa797dbbaed8c8a958b090207f0f042ae319bf69927592`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aab2eb48121c86dd4cfa797dbbaed8c8a958b090207f0f042ae319bf69927592`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aab2eb48121c86dd4cfa797dbbaed8c8a958b090207f0f042ae319bf69927592`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_t32/mcp_t32_dialog_tools_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_dialog_tools_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_dialog_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_dialog_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_dialog_tools_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts simple identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_dialog_tools_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts identifier with underscore' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_dialog_tools_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts identifier with digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
