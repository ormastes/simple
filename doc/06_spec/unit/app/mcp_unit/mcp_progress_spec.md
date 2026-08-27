# Mcp Progress Specification

> Tests covering MCP Progress Notification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Progress Specification

## Scenarios

### MCP Progress Notification

<details>
<summary>Advanced: includes progress token</summary>

#### includes progress token _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- includes progress token
   - Expected: notif contains `"progressToken":"tok-abc"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes progress token")
val notif = make_progress_notification("tok-abc", 5, 10, "Working")
expect(notif.contains("\"progressToken\":\"tok-abc\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes progress and total</summary>

#### includes progress and total _(slow)_

- includes progress and total
   - Expected: notif contains `"progress":50`
   - Expected: notif contains `"total":100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes progress and total")
val notif = make_progress_notification("tok-1", 50, 100, "")
expect(notif.contains("\"progress\":50")).to_equal(true)
expect(notif.contains("\"total\":100")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes message when provided</summary>

#### includes message when provided _(slow)_

- includes message when provided
   - Expected: notif contains `Step 3 of 10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes message when provided")
val notif = make_progress_notification("tok-1", 3, 10, "Step 3 of 10")
expect(notif.contains("Step 3 of 10")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: uses notifications/progress method</summary>

#### uses notifications/progress method _(slow)_

- uses notifications/progress method
   - Expected: notif contains `"method":"notifications/progress"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses notifications/progress method")
val notif = make_progress_notification("tok-1", 0, 0, "")
expect(notif.contains("\"method\":\"notifications/progress\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: is valid JSON-RPC notification</summary>

#### is valid JSON-RPC notification _(slow)_

- is valid JSON-RPC notification
   - Expected: notif contains `"jsonrpc":"2.0"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is valid JSON-RPC notification")
val notif = make_progress_notification("tok-1", 1, 5, "test")
expect(notif.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_progress_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Progress Notification.
- MCP Progress Notification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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

- Canonical SPipe generation for source `1b02ae28144fd38135637a1f91ca4a5f56056df9f816b701fd44efe9e208f34a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b02ae28144fd38135637a1f91ca4a5f56056df9f816b701fd44efe9e208f34a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b02ae28144fd38135637a1f91ca4a5f56056df9f816b701fd44efe9e208f34a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_progress_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_progress_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_progress_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_progress_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_progress_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes progress token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_progress_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes progress and total' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_progress_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes message when provided' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
