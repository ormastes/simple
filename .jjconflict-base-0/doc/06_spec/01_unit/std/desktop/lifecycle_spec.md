# Lifecycle Specification

> Tests covering Desktop App Lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifecycle Specification

## Scenarios

### Desktop App Lifecycle

#### creates AppLifecycle instance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates AppLifecycle instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates AppLifecycle instance")
val app = AppLifecycle.new("test-app")
expect app.app_id == "test-app"
```

</details>

#### converts lifecycle event to name

- converts lifecycle event to name

</details>

#### converts lifecycle event to name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts lifecycle event to name")
val name = lifecycle_event_name(LifecycleEvent.Ready)
expect name == "Ready"
```

</details>

#### registers event handlers

- registers event handlers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers event handlers")
val app = AppLifecycle.new("test-app")
val app2 = app.on(LifecycleEvent.Ready, "on_ready")
val handlers = app2.get_handlers(LifecycleEvent.Ready)
expect handlers.length() == 1
```

</details>

#### transitions app phase

- transitions app phase


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions app phase")
val app = AppLifecycle.new("test-app")
val running = app.set_phase(AppPhase.Running)
val phase_name = match running.phase:
    AppPhase.Initializing: "init"
    AppPhase.Running: "running"
    AppPhase.ShuttingDown: "shutdown"
expect phase_name == "running"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Desktop App Lifecycle.
- Desktop App Lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `415ea2d4bb68c099596a0590029402a4c6fab15b8d92d8952d16b66d5040f992`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `415ea2d4bb68c099596a0590029402a4c6fab15b8d92d8952d16b66d5040f992`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `415ea2d4bb68c099596a0590029402a4c6fab15b8d92d8952d16b66d5040f992`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/desktop/lifecycle_spec.spl
mirror: doc/06_spec/01_unit/std/desktop/lifecycle_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/desktop/lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/desktop/lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/desktop/lifecycle_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates AppLifecycle instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/desktop/lifecycle_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts lifecycle event to name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/desktop/lifecycle_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers event handlers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
