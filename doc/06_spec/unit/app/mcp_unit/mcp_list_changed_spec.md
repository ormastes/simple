# Mcp List Changed Specification

> Tests covering MCP Tools List Changed, MCP Resources List Changed, MCP Prompts List Changed, MCP List Changed Capabilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp List Changed Specification

## Scenarios

### MCP Tools List Changed

#### when tools list changes

#### sends correct method

- sends correct method
   - Expected: notif contains `notifications/tools/list_changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends correct method")
val notif = make_tools_list_changed()
expect(notif.contains("notifications/tools/list_changed")).to_equal(true)
```

</details>

#### is a notification (no id)

- is a notification (no id)
   - Expected: notif does not contain `"id"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a notification (no id)")
val notif = make_tools_list_changed()
expect(notif.contains("\"id\"")).to_equal(false)
```

</details>

#### includes jsonrpc version

- includes jsonrpc version
   - Expected: notif contains `"jsonrpc":"2.0"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes jsonrpc version")
val notif = make_tools_list_changed()
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP Resources List Changed

#### when resources list changes

#### sends correct method

- sends correct method
   - Expected: notif contains `notifications/resources/list_changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends correct method")
val notif = make_resources_list_changed()
expect(notif.contains("notifications/resources/list_changed")).to_equal(true)
```

</details>

#### is a notification (no id)

- is a notification (no id)
   - Expected: notif does not contain `"id"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a notification (no id)")
val notif = make_resources_list_changed()
expect(notif.contains("\"id\"")).to_equal(false)
```

</details>

#### includes jsonrpc version

- includes jsonrpc version
   - Expected: notif contains `"jsonrpc":"2.0"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes jsonrpc version")
val notif = make_resources_list_changed()
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP Prompts List Changed

#### when prompts list changes

#### sends correct method

- sends correct method
   - Expected: notif contains `notifications/prompts/list_changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends correct method")
val notif = make_prompts_list_changed()
expect(notif.contains("notifications/prompts/list_changed")).to_equal(true)
```

</details>

#### is a notification (no id)

- is a notification (no id)
   - Expected: notif does not contain `"id"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a notification (no id)")
val notif = make_prompts_list_changed()
expect(notif.contains("\"id\"")).to_equal(false)
```

</details>

#### includes jsonrpc version

- includes jsonrpc version
   - Expected: notif contains `"jsonrpc":"2.0"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes jsonrpc version")
val notif = make_prompts_list_changed()
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP List Changed Capabilities

#### when validating notification format

#### tools notification has method field

- tools notification has method field
   - Expected: notif contains `"method":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tools notification has method field")
val notif = make_tools_list_changed()
expect(notif.contains("\"method\":")).to_equal(true)
```

</details>

#### resources notification has method field

- resources notification has method field
   - Expected: notif contains `"method":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resources notification has method field")
val notif = make_resources_list_changed()
expect(notif.contains("\"method\":")).to_equal(true)
```

</details>

#### prompts notification has method field

- prompts notification has method field
   - Expected: notif contains `"method":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prompts notification has method field")
val notif = make_prompts_list_changed()
expect(notif.contains("\"method\":")).to_equal(true)
```

</details>

#### generic notification_no_params works

- generic notification_no_params works
   - Expected: notif contains `custom/method`
   - Expected: notif contains `"jsonrpc":"2.0"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generic notification_no_params works")
val notif = make_notification_no_params("custom/method")
expect(notif.contains("custom/method")).to_equal(true)
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_list_changed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Tools List Changed, MCP Resources List Changed, MCP Prompts List Changed, MCP List Changed Capabilities.
- MCP Tools List Changed
- MCP Resources List Changed
- MCP Prompts List Changed
- MCP List Changed Capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `5158d4db299b210686db47074f08d0341bb1bd31057434157955d5d05f3e2000`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5158d4db299b210686db47074f08d0341bb1bd31057434157955d5d05f3e2000`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5158d4db299b210686db47074f08d0341bb1bd31057434157955d5d05f3e2000`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_list_changed_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_list_changed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_list_changed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_list_changed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_list_changed_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sends correct method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_list_changed_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is a notification (no id)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_list_changed_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes jsonrpc version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
