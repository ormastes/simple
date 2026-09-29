# Mcp Notifications Specification

> Tests covering MCP Progress Notifications, MCP Log Notifications, MCP List Changed Notifications, MCP Resource Updated Notification, MCP Generic Notification Building.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Notifications Specification

## Scenarios

### MCP Progress Notifications

<details>
<summary>Advanced: builds progress notification with token</summary>

#### builds progress notification with token _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds progress notification with token
   - Expected: notif contains `"progressToken":"tok-1"`
   - Expected: notif contains `"progress":50`
   - Expected: notif contains `"total":100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds progress notification with token")
val notif = make_progress_notification("tok-1", 50, 100, "Processing")
expect(notif.contains("\"progressToken\":\"tok-1\"")).to_equal(true)
expect(notif.contains("\"progress\":50")).to_equal(true)
expect(notif.contains("\"total\":100")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: uses correct method</summary>

#### uses correct method _(slow)_

- uses correct method
   - Expected: notif contains `notifications/progress`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses correct method")
val notif = make_progress_notification("tok-1", 0, 10, "Starting")
expect(notif.contains("notifications/progress")).to_equal(true)
```

</details>


</details>

### MCP Log Notifications

<details>
<summary>Advanced: builds log notification with level and data</summary>

#### builds log notification with level and data _(slow)_

- builds log notification with level and data
   - Expected: notif contains `"level":"info"`
   - Expected: notif contains `Server started`
   - Expected: notif contains `"logger":"mcp"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds log notification with level and data")
val notif = make_log_notification("info", "Server started", "mcp")
expect(notif.contains("\"level\":\"info\"")).to_equal(true)
expect(notif.contains("Server started")).to_equal(true)
expect(notif.contains("\"logger\":\"mcp\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: uses correct method</summary>

#### uses correct method _(slow)_

- uses correct method
   - Expected: notif contains `notifications/message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses correct method")
val notif = make_log_notification("error", "fail", "")
expect(notif.contains("notifications/message")).to_equal(true)
```

</details>


</details>

### MCP List Changed Notifications

<details>
<summary>Advanced: builds tools list changed</summary>

#### builds tools list changed _(slow)_

- builds tools list changed
   - Expected: notif contains `notifications/tools/list_changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds tools list changed")
val notif = make_tools_list_changed()
expect(notif.contains("notifications/tools/list_changed")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds resources list changed</summary>

#### builds resources list changed _(slow)_

- builds resources list changed
   - Expected: notif contains `notifications/resources/list_changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds resources list changed")
val notif = make_resources_list_changed()
expect(notif.contains("notifications/resources/list_changed")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds prompts list changed</summary>

#### builds prompts list changed _(slow)_

- builds prompts list changed
   - Expected: notif contains `notifications/prompts/list_changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds prompts list changed")
val notif = make_prompts_list_changed()
expect(notif.contains("notifications/prompts/list_changed")).to_equal(true)
```

</details>


</details>

### MCP Resource Updated Notification

<details>
<summary>Advanced: builds with URI</summary>

#### builds with URI _(slow)_

- builds with URI
   - Expected: notif contains `notifications/resources/updated`
   - Expected: notif contains `file:///test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with URI")
val notif = make_resource_updated_notification("file:///test.spl")
expect(notif.contains("notifications/resources/updated")).to_equal(true)
expect(notif.contains("file:///test.spl")).to_equal(true)
```

</details>


</details>

### MCP Generic Notification Building

<details>
<summary>Advanced: builds notification with params</summary>

#### builds notification with params _(slow)_

- builds notification with params
   - Expected: notif contains `"method":"custom/method"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds notification with params")
val params = LB() + jp("key", js("value")) + RB()
val notif = make_notification("custom/method", params)
expect(notif.contains("\"method\":\"custom/method\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds notification without params</summary>

#### builds notification without params _(slow)_

- builds notification without params
   - Expected: notif contains `"method":"simple/notify"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds notification without params")
val notif = make_notification_no_params("simple/notify")
expect(notif.contains("\"method\":\"simple/notify\"")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_notifications_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Progress Notifications, MCP Log Notifications, MCP List Changed Notifications, MCP Resource Updated Notification, MCP Generic Notification Building.
- MCP Progress Notifications
- MCP Log Notifications
- MCP List Changed Notifications
- MCP Resource Updated Notification
- MCP Generic Notification Building

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
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

- Canonical SPipe generation for source `ce2a3c94a6f261313059aaa04ff7f456cee12aa25a489f4720973c9052eb969c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce2a3c94a6f261313059aaa04ff7f456cee12aa25a489f4720973c9052eb969c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce2a3c94a6f261313059aaa04ff7f456cee12aa25a489f4720973c9052eb969c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_notifications_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_notifications_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_notifications_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_notifications_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_notifications_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds progress notification with token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_notifications_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses correct method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_notifications_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds log notification with level and data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
