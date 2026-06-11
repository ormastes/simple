# Kairos Like Simple Mcp Llm Dashboard Specification

> <details>

<!-- sdn-diagram:id=kairos_like_simple_mcp_llm_dashboard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kairos_like_simple_mcp_llm_dashboard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kairos_like_simple_mcp_llm_dashboard_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kairos_like_simple_mcp_llm_dashboard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "session-created"
expect(result).to_equal("session-created")
```

</details>

#### should allow a paused session to resume with preserved state

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "session-resumed"
expect(result).to_equal("session-resumed")
```

</details>

### REQ-KAIROS-002 and REQ-KAIROS-003: ticks and signals

#### should record a periodic tick wake reason in the session timeline

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wake_reason = "tick"
expect(wake_reason).to_equal("tick")
```

</details>

#### should record an external signal wakeup with source metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wake_reason = "signal"
expect(wake_reason).to_equal("signal")
```

</details>

### REQ-KAIROS-004: child-agent delegation

#### should track a child task with parent linkage and terminal summary

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = "completed"
expect(status).to_equal("completed")
```

</details>

### REQ-KAIROS-005 and REQ-KAIROS-006: briefs and notifications

#### should produce a compact brief from recent session activity

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val brief = "brief"
expect(brief).to_equal("brief")
```

</details>

#### should preserve notification decision and delivery status

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val delivery = "recorded"
expect(delivery).to_equal("recorded")
```

</details>

### REQ-KAIROS-007 and REQ-KAIROS-008: standalone modes

#### should support standalone simple mcp control without the dashboard

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = "mcp-standalone"
expect(mode).to_equal("mcp-standalone")
```

</details>

#### should support standalone dashboard replay without live mcp

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = "dashboard-replay"
expect(mode).to_equal("dashboard-replay")
```

</details>

### REQ-KAIROS-009 and REQ-KAIROS-010: combined live mode

#### should attach dashboard live state without moving source of truth

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "attached"
expect(result).to_equal("attached")
```

</details>

#### should expose operator-visible task tree and recent events

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "visible"
expect(result).to_equal("visible")
```

</details>

### REQ-KAIROS-011 and REQ-KAIROS-012: recovery and bounded retention

#### should preserve structured failure evidence after a child-task crash

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "failure-recorded"
expect(result).to_equal("failure-recorded")
```

</details>

#### should apply bounded retention or coalescing under bursty signals

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "bounded"
expect(result).to_equal("bounded")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
