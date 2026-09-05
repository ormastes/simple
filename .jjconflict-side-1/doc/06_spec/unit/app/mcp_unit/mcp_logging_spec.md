# @manual: primary

> Purpose: Prove that MCP Log Level Mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that MCP Log Level Mapping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_logging_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that MCP Log Level Mapping.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-APP-MCP-UNIT-001
doc/01_research/local/REQ-APP-MCP-UNIT-001.md
doc/03_plan/sys_test/REQ-APP-MCP-UNIT-001.md
doc/04_architecture/REQ-APP-MCP-UNIT-001.md
doc/05_design/REQ-APP-MCP-UNIT-001.md

## Scenarios

### MCP Log Level Mapping

<details>
<summary>Advanced: maps debug to 0</summary>

#### maps debug to 0 _(slow)_

- Verify: maps debug to 0
   - Expected: log_level_to_int("debug") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps debug to 0")
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: maps info to 1</summary>

#### maps info to 1 _(slow)_

- Verify: maps info to 1
   - Expected: log_level_to_int("info") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps info to 1")
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: maps notice to 2</summary>

#### maps notice to 2 _(slow)_

- Verify: maps notice to 2
   - Expected: log_level_to_int("notice") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps notice to 2")
expect(log_level_to_int("notice")).to_equal(2)
```

</details>


</details>

<details>
<summary>Advanced: maps warning to 3</summary>

#### maps warning to 3 _(slow)_

- Verify: maps warning to 3
   - Expected: log_level_to_int("warning") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps warning to 3")
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: maps error to 4</summary>

#### maps error to 4 _(slow)_

- Verify: maps error to 4
   - Expected: log_level_to_int("error") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps error to 4")
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: maps critical to 5</summary>

#### maps critical to 5 _(slow)_

- Verify: maps critical to 5
   - Expected: log_level_to_int("critical") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps critical to 5")
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: maps alert to 6</summary>

#### maps alert to 6 _(slow)_

- Verify: maps alert to 6
   - Expected: log_level_to_int("alert") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps alert to 6")
expect(log_level_to_int("alert")).to_equal(6)
```

</details>


</details>

<details>
<summary>Advanced: maps emergency to 7</summary>

#### maps emergency to 7 _(slow)_

- Verify: maps emergency to 7
   - Expected: log_level_to_int("emergency") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps emergency to 7")
expect(log_level_to_int("emergency")).to_equal(7)
```

</details>


</details>

<details>
<summary>Advanced: returns -1 for unknown level</summary>

#### returns -1 for unknown level _(slow)_

- Verify: returns -1 for unknown level
   - Expected: log_level_to_int("unknown") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: returns -1 for unknown level")
expect(log_level_to_int("unknown")).to_equal(-1)
```

</details>


</details>

### MCP Log Notification Building

<details>
<summary>Advanced: builds log notification with all fields</summary>

#### builds log notification with all fields _(slow)_

- Verify: builds log notification with all fields
   - Expected: notif contains `"level":"info"`
   - Expected: notif contains `Test message`
   - Expected: notif contains `"logger":"mcp.server"`
   - Expected: notif contains `notifications/message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds log notification with all fields")
val notif = make_log_notification("info", "Test message", "mcp.server")
expect(notif.contains("\"level\":\"info\"")).to_equal(true)
expect(notif.contains("Test message")).to_equal(true)
expect(notif.contains("\"logger\":\"mcp.server\"")).to_equal(true)
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds log notification without logger</summary>

#### builds log notification without logger _(slow)_

- Verify: builds log notification without logger
   - Expected: notif contains `"level":"error"`
   - Expected: notif contains `Something failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds log notification without logger")
val notif = make_log_notification("error", "Something failed", "")
expect(notif.contains("\"level\":\"error\"")).to_equal(true)
expect(notif.contains("Something failed")).to_equal(true)
```

</details>


</details>

### MCP Log Level Comparison

<details>
<summary>Advanced: debug is lowest priority</summary>

#### debug is lowest priority _(slow)_

- Verify: debug is lowest priority
   - Expected: log_level_to_int("debug") < log_level_to_int("info") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: debug is lowest priority")
expect(log_level_to_int("debug") < log_level_to_int("info")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: emergency is highest priority</summary>

#### emergency is highest priority _(slow)_

- Verify: emergency is highest priority
   - Expected: log_level_to_int("emergency") > log_level_to_int("error") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: emergency is highest priority")
expect(log_level_to_int("emergency") > log_level_to_int("error")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: levels increase monotonically</summary>

#### levels increase monotonically _(slow)_

- Verify: levels increase monotonically
   - Expected: log_level_to_int("debug") < log_level_to_int("info") is true
   - Expected: log_level_to_int("info") < log_level_to_int("warning") is true
   - Expected: log_level_to_int("warning") < log_level_to_int("error") is true
   - Expected: log_level_to_int("error") < log_level_to_int("emergency") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: levels increase monotonically")
expect(log_level_to_int("debug") < log_level_to_int("info")).to_equal(true)
expect(log_level_to_int("info") < log_level_to_int("warning")).to_equal(true)
expect(log_level_to_int("warning") < log_level_to_int("error")).to_equal(true)
expect(log_level_to_int("error") < log_level_to_int("emergency")).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 14 |
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

- Canonical SPipe generation for source `d67d206261390235dd06b51560ba319406d292efbe9edc1b0a2bb9e2fbb61917`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d67d206261390235dd06b51560ba319406d292efbe9edc1b0a2bb9e2fbb61917`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d67d206261390235dd06b51560ba319406d292efbe9edc1b0a2bb9e2fbb61917`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/mcp_unit/mcp_logging_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_logging_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/mcp_unit/mcp_logging_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_logging_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_logging_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_logging_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/mcp_unit/mcp_logging_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps debug to 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_logging_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps info to 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_logging_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps notice to 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
