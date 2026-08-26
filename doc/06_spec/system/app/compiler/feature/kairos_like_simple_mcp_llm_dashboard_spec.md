# Kairos Like Simple Mcp Llm Dashboard Specification

> Tests covering KAIROS-like simple mcp and llm dashboard, REQ-KAIROS-001: session identity and lifecycle, REQ-KAIROS-002 and REQ-KAIROS-003: ticks and signals, REQ-KAIROS-004: child-agent delegation, REQ-KAIROS-005 and REQ-KAIROS-006: briefs and notifications, REQ-KAIROS-007 and REQ-KAIROS-008: standalone modes, REQ-KAIROS-009 and REQ-KAIROS-010: combined live mode, REQ-KAIROS-011 and REQ-KAIROS-012: recovery and bounded retention.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kairos Like Simple Mcp Llm Dashboard Specification

## Scenarios

### KAIROS-like simple mcp and llm dashboard

### REQ-KAIROS-001: session identity and lifecycle

#### should create and persist an assistant session with stable identity
#### should allow a paused session to resume with preserved state

- should allow a paused session to resume with preserved state
   - Expected: result equals `session-resumed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should allow a paused session to resume with preserved state")
val result = "session-resumed"
expect(result).to_equal("session-resumed")
```

</details>

### REQ-KAIROS-002 and REQ-KAIROS-003: ticks and signals

#### should record a periodic tick wake reason in the session timeline

- should record a periodic tick wake reason in the session timeline
   - Expected: wake_reason equals `tick`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record a periodic tick wake reason in the session timeline")
val wake_reason = "tick"
expect(wake_reason).to_equal("tick")
```

</details>

#### should record an external signal wakeup with source metadata

- should record an external signal wakeup with source metadata
   - Expected: wake_reason equals `signal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record an external signal wakeup with source metadata")
val wake_reason = "signal"
expect(wake_reason).to_equal("signal")
```

</details>

### REQ-KAIROS-004: child-agent delegation

#### should track a child task with parent linkage and terminal summary

- should track a child task with parent linkage and terminal summary
   - Expected: status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should track a child task with parent linkage and terminal summary")
val status = "completed"
expect(status).to_equal("completed")
```

</details>

### REQ-KAIROS-005 and REQ-KAIROS-006: briefs and notifications

#### should produce a compact brief from recent session activity

- should produce a compact brief from recent session activity
   - Expected: brief equals `brief`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should produce a compact brief from recent session activity")
val brief = "brief"
expect(brief).to_equal("brief")
```

</details>

#### should preserve notification decision and delivery status

- should preserve notification decision and delivery status
   - Expected: delivery equals `recorded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve notification decision and delivery status")
val delivery = "recorded"
expect(delivery).to_equal("recorded")
```

</details>

### REQ-KAIROS-007 and REQ-KAIROS-008: standalone modes

#### should support standalone simple mcp control without the dashboard

- should support standalone simple mcp control without the dashboard
   - Expected: mode equals `mcp-standalone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should support standalone simple mcp control without the dashboard")
val mode = "mcp-standalone"
expect(mode).to_equal("mcp-standalone")
```

</details>

#### should support standalone dashboard replay without live mcp

- should support standalone dashboard replay without live mcp
   - Expected: mode equals `dashboard-replay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should support standalone dashboard replay without live mcp")
val mode = "dashboard-replay"
expect(mode).to_equal("dashboard-replay")
```

</details>

### REQ-KAIROS-009 and REQ-KAIROS-010: combined live mode

#### should attach dashboard live state without moving source of truth

- should attach dashboard live state without moving source of truth
   - Expected: result equals `attached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should attach dashboard live state without moving source of truth")
val result = "attached"
expect(result).to_equal("attached")
```

</details>

#### should expose operator-visible task tree and recent events

- should expose operator-visible task tree and recent events
   - Expected: result equals `visible`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose operator-visible task tree and recent events")
val result = "visible"
expect(result).to_equal("visible")
```

</details>

### REQ-KAIROS-011 and REQ-KAIROS-012: recovery and bounded retention

#### should preserve structured failure evidence after a child-task crash

- should preserve structured failure evidence after a child-task crash
   - Expected: result equals `failure-recorded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve structured failure evidence after a child-task crash")
val result = "failure-recorded"
expect(result).to_equal("failure-recorded")
```

</details>

#### should apply bounded retention or coalescing under bursty signals

- should apply bounded retention or coalescing under bursty signals
   - Expected: result equals `bounded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply bounded retention or coalescing under bursty signals")
val result = "bounded"
expect(result).to_equal("bounded")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering KAIROS-like simple mcp and llm dashboard, REQ-KAIROS-001: session identity and lifecycle, REQ-KAIROS-002 and REQ-KAIROS-003: ticks and signals, REQ-KAIROS-004: child-agent delegation, REQ-KAIROS-005 and REQ-KAIROS-006: briefs and notifications, REQ-KAIROS-007 and REQ-KAIROS-008: standalone modes, REQ-KAIROS-009 and REQ-KAIROS-010: combined live mode, REQ-KAIROS-011 and REQ-KAIROS-012: recovery and bounded retention.
- KAIROS-like simple mcp and llm dashboard
- REQ-KAIROS-001: session identity and lifecycle
- REQ-KAIROS-002 and REQ-KAIROS-003: ticks and signals
- REQ-KAIROS-004: child-agent delegation
- REQ-KAIROS-005 and REQ-KAIROS-006: briefs and notifications
- REQ-KAIROS-007 and REQ-KAIROS-008: standalone modes
- REQ-KAIROS-009 and REQ-KAIROS-010: combined live mode
- REQ-KAIROS-011 and REQ-KAIROS-012: recovery and bounded retention

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

- `REQ-SSPEC-SYSTEM`
- `REQ-KAIROS-001`
- `REQ-KAIROS-002`
- `REQ-KAIROS-003`
- `REQ-KAIROS-004`
- `REQ-KAIROS-005`
- `REQ-KAIROS-006`
- `REQ-KAIROS-007`
- `REQ-KAIROS-008`
- `REQ-KAIROS-009`
- `REQ-KAIROS-010`
- `REQ-KAIROS-011`
- `REQ-KAIROS-012`
- `REQ-KAIROS-003:`
- `REQ-KAIROS-006:`
- `REQ-KAIROS-008:`
- `REQ-KAIROS-010:`
- `REQ-KAIROS-012:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f61486301c50aba2023655438c18be2172307da4e8aa9834723e4e1088ee12c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f61486301c50aba2023655438c18be2172307da4e8aa9834723e4e1088ee12c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f61486301c50aba2023655438c18be2172307da4e8aa9834723e4e1088ee12c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **60/100**; effective score: **49/100**; blockers: **3**.

SSpec documentization score: 49/100
source: test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl
mirror: doc/06_spec/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.md (current)
findings: 15 blockers: 3
  narrative=100 structure=60 oracle=0
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=60; blocker cap makes effective=49
doc/06_spec/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 12 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:12:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should create and persist an assistant session with stable identity' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:12:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create and persist an assistant session with stable identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should allow a paused session to resume with preserved state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should allow a paused session to resume with preserved state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record a periodic tick wake reason in the session timeline' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should record a periodic tick wake reason in the session timeline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record an external signal wakeup with source metadata' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should record an external signal wakeup with source metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should track a child task with parent linkage and terminal summary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should produce a compact brief from recent session activity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
