# logger_spec

> Purpose: Prove that log_level_to_int.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# logger_spec

Purpose: Prove that log_level_to_int.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/logger_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that log_level_to_int.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### log_level_to_int

#### converts debug to 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts debug to 0
- Verify: converts debug to 0
   - Expected: log_level_to_int("debug") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts debug to 0")
step("Verify: converts debug to 0")
# @req: REQ-APP-MCP-UNIT-001
expect(log_level_to_int("debug")).to_equal(0)
```

</details>

#### converts info to 1

- converts info to 1
- Verify: converts info to 1
   - Expected: log_level_to_int("info") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts info to 1")
step("Verify: converts info to 1")
expect(log_level_to_int("info")).to_equal(1)
```

</details>

#### converts notice to 2

- converts notice to 2
- Verify: converts notice to 2
   - Expected: log_level_to_int("notice") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts notice to 2")
step("Verify: converts notice to 2")
expect(log_level_to_int("notice")).to_equal(2)
```

</details>

#### converts warning to 3

- converts warning to 3
- Verify: converts warning to 3
   - Expected: log_level_to_int("warning") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts warning to 3")
step("Verify: converts warning to 3")
expect(log_level_to_int("warning")).to_equal(3)
```

</details>

#### converts error to 4

- converts error to 4
- Verify: converts error to 4
   - Expected: log_level_to_int("error") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts error to 4")
step("Verify: converts error to 4")
expect(log_level_to_int("error")).to_equal(4)
```

</details>

#### converts critical to 5

- converts critical to 5
- Verify: converts critical to 5
   - Expected: log_level_to_int("critical") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts critical to 5")
step("Verify: converts critical to 5")
expect(log_level_to_int("critical")).to_equal(5)
```

</details>

#### converts alert to 6

- converts alert to 6
- Verify: converts alert to 6
   - Expected: log_level_to_int("alert") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts alert to 6")
step("Verify: converts alert to 6")
expect(log_level_to_int("alert")).to_equal(6)
```

</details>

#### converts emergency to 7

- converts emergency to 7
- Verify: converts emergency to 7
   - Expected: log_level_to_int("emergency") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts emergency to 7")
step("Verify: converts emergency to 7")
expect(log_level_to_int("emergency")).to_equal(7)
```

</details>

#### returns -1 for unknown level

- returns -1 for unknown level
- Verify: returns -1 for unknown level
   - Expected: log_level_to_int("unknown") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for unknown level")
step("Verify: returns -1 for unknown level")
expect(log_level_to_int("unknown")).to_equal(-1)
```

</details>

#### returns -1 for empty string

- returns -1 for empty string
- Verify: returns -1 for empty string
   - Expected: log_level_to_int("") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for empty string")
step("Verify: returns -1 for empty string")
expect(log_level_to_int("")).to_equal(-1)
```

</details>

### log_level_to_int - ordering

#### debug is lower than info

- debug is lower than info
- Verify: debug is lower than info
   - Expected: debug_level < info_level is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug is lower than info")
step("Verify: debug is lower than info")
val debug_level = log_level_to_int("debug")
val info_level = log_level_to_int("info")
expect(debug_level < info_level).to_equal(true)
```

</details>

#### info is lower than notice

- info is lower than notice
- Verify: info is lower than notice
   - Expected: log_level_to_int("info") < log_level_to_int("notice") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("info is lower than notice")
step("Verify: info is lower than notice")
expect(log_level_to_int("info") < log_level_to_int("notice")).to_equal(true)
```

</details>

#### notice is lower than warning

- notice is lower than warning
- Verify: notice is lower than warning
   - Expected: log_level_to_int("notice") < log_level_to_int("warning") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("notice is lower than warning")
step("Verify: notice is lower than warning")
expect(log_level_to_int("notice") < log_level_to_int("warning")).to_equal(true)
```

</details>

#### warning is lower than error

- warning is lower than error
- Verify: warning is lower than error
   - Expected: log_level_to_int("warning") < log_level_to_int("error") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warning is lower than error")
step("Verify: warning is lower than error")
expect(log_level_to_int("warning") < log_level_to_int("error")).to_equal(true)
```

</details>

#### error is lower than critical

- error is lower than critical
- Verify: error is lower than critical
   - Expected: log_level_to_int("error") < log_level_to_int("critical") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error is lower than critical")
step("Verify: error is lower than critical")
expect(log_level_to_int("error") < log_level_to_int("critical")).to_equal(true)
```

</details>

#### critical is lower than alert

- critical is lower than alert
- Verify: critical is lower than alert
   - Expected: log_level_to_int("critical") < log_level_to_int("alert") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("critical is lower than alert")
step("Verify: critical is lower than alert")
expect(log_level_to_int("critical") < log_level_to_int("alert")).to_equal(true)
```

</details>

#### alert is lower than emergency

- alert is lower than emergency
- Verify: alert is lower than emergency
   - Expected: log_level_to_int("alert") < log_level_to_int("emergency") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alert is lower than emergency")
step("Verify: alert is lower than emergency")
expect(log_level_to_int("alert") < log_level_to_int("emergency")).to_equal(true)
```

</details>

### log_level_to_int - filtering logic

#### message at min level should emit

- message at min level should emit
- Verify: message at min level should emit
   - Expected: msg_level >= min_level is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message at min level should emit")
step("Verify: message at min level should emit")
val min_level = log_level_to_int("warning")
val msg_level = log_level_to_int("warning")
expect(msg_level >= min_level).to_equal(true)
```

</details>

#### message above min level should emit

- message above min level should emit
- Verify: message above min level should emit
   - Expected: msg_level >= min_level is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message above min level should emit")
step("Verify: message above min level should emit")
val min_level = log_level_to_int("warning")
val msg_level = log_level_to_int("error")
expect(msg_level >= min_level).to_equal(true)
```

</details>

#### message below min level should not emit

- message below min level should not emit
- Verify: message below min level should not emit
   - Expected: msg_level >= min_level is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message below min level should not emit")
step("Verify: message below min level should not emit")
val min_level = log_level_to_int("warning")
val msg_level = log_level_to_int("info")
expect(msg_level >= min_level).to_equal(false)
```

</details>

#### debug messages suppressed at info level

- debug messages suppressed at info level
- Verify: debug messages suppressed at info level
   - Expected: msg_level >= min_level is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug messages suppressed at info level")
step("Verify: debug messages suppressed at info level")
val min_level = log_level_to_int("info")
val msg_level = log_level_to_int("debug")
expect(msg_level >= min_level).to_equal(false)
```

</details>

#### emergency always passes any valid level

- emergency always passes any valid level
- Verify: emergency always passes any valid level
   - Expected: msg_level >= min_level is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emergency always passes any valid level")
step("Verify: emergency always passes any valid level")
val min_level = log_level_to_int("emergency")
val msg_level = log_level_to_int("emergency")
expect(msg_level >= min_level).to_equal(true)
```

</details>

### make_log_notification

#### includes notifications/message method

- includes notifications/message method
- Verify: includes notifications/message method
   - Expected: notif contains `notifications/message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes notifications/message method")
step("Verify: includes notifications/message method")
val notif = make_log_notification("info", "Server started", "mcp")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>

#### includes log level

- includes log level
- Verify: includes log level
   - Expected: notif contains `warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes log level")
step("Verify: includes log level")
val notif = make_log_notification("warning", "Low memory", "mcp")
expect(notif.contains("warning")).to_equal(true)
```

</details>

#### includes log data

- includes log data
- Verify: includes log data
   - Expected: notif contains `Connection failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes log data")
step("Verify: includes log data")
val notif = make_log_notification("error", "Connection failed", "mcp")
expect(notif.contains("Connection failed")).to_equal(true)
```

</details>

#### includes logger name when provided

- includes logger name when provided
- Verify: includes logger name when provided
   - Expected: notif contains `mcp.tools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes logger name when provided")
step("Verify: includes logger name when provided")
val notif = make_log_notification("info", "Test message", "mcp.tools")
expect(notif.contains("mcp.tools")).to_equal(true)
```

</details>

#### includes jsonrpc version

- includes jsonrpc version
- Verify: includes jsonrpc version
   - Expected: notif contains `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes jsonrpc version")
step("Verify: includes jsonrpc version")
val notif = make_log_notification("debug", "Debug data", "")
expect(notif.contains("2.0")).to_equal(true)
```

</details>

#### handles empty logger name

- handles empty logger name
- Verify: handles empty logger name
   - Expected: notif contains `notifications/message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty logger name")
step("Verify: handles empty logger name")
val notif = make_log_notification("info", "Test", "")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>

#### handles special characters in data

- handles special characters in data
- Verify: handles special characters in data
   - Expected: notif contains `notifications/message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles special characters in data")
step("Verify: handles special characters in data")
val notif = make_log_notification("info", "line1{NL}line2", "mcp")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>

### make_notification

#### creates notification with method and params

- creates notification with method and params
- Verify: creates notification with method and params
   - Expected: notif contains `test/method`
   - Expected: notif contains `params`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates notification with method and params")
step("Verify: creates notification with method and params")
val params = jo1(jp("level", js("info")))
val notif = make_notification("test/method", params)
expect(notif.contains("test/method")).to_equal(true)
expect(notif.contains("params")).to_equal(true)
```

</details>

#### includes jsonrpc version

- includes jsonrpc version
- Verify: includes jsonrpc version
   - Expected: notif contains `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes jsonrpc version")
step("Verify: includes jsonrpc version")
val notif = make_notification("test/method", LB() + RB())
expect(notif.contains("2.0")).to_equal(true)
```

</details>

### make_notification_no_params

#### creates notification without params

- creates notification without params
- Verify: creates notification without params
   - Expected: notif contains `notifications/initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates notification without params")
step("Verify: creates notification without params")
val notif = make_notification_no_params("notifications/initialized")
expect(notif.contains("notifications/initialized")).to_equal(true)
```

</details>

#### does not include params

- does not include params
- Verify: does not include params
   - Expected: notif does not contain `params`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not include params")
step("Verify: does not include params")
val notif = make_notification_no_params("test/method")
expect(notif.contains("params")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-MCP-UNIT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7f157c32a514fcd6502fce5cfc018c78e7b726ed7dcb83a71a121c2032bd7059`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f157c32a514fcd6502fce5cfc018c78e7b726ed7dcb83a71a121c2032bd7059`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f157c32a514fcd6502fce5cfc018c78e7b726ed7dcb83a71a121c2032bd7059`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/logger_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/logger_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/logger_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/logger_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/logger_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/logger_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts debug to 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/logger_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts info to 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/logger_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts notice to 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
