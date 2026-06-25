# Lifecycle Specification

> <details>

<!-- sdn-diagram:id=lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lifecycle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifecycle Specification

## Scenarios

### Desktop App Lifecycle

#### creates AppLifecycle instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = AppLifecycle.new("test-app")
expect app.app_id == "test-app"
```

</details>

#### converts lifecycle event to name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = lifecycle_event_name(LifecycleEvent.Ready)
expect name == "Ready"
```

</details>

#### registers event handlers

1. expect handlers length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = AppLifecycle.new("test-app")
val app2 = app.on(LifecycleEvent.Ready, "on_ready")
val handlers = app2.get_handlers(LifecycleEvent.Ready)
expect handlers.length() == 1
```

</details>

#### transitions app phase

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
