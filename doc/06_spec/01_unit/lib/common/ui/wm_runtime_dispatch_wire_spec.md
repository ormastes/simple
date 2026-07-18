# Wm Runtime Dispatch Wire Specification

> <details>

<!-- sdn-diagram:id=wm_runtime_dispatch_wire_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_runtime_dispatch_wire_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_runtime_dispatch_wire_spec -> std
wm_runtime_dispatch_wire_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_runtime_dispatch_wire_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Runtime Dispatch Wire Specification

## Scenarios

### WM runtime dispatch wire format

#### serializes command fields in stable order

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = wm_runtime_dispatch_command(
    "window_focus",
    "surf1",
    "demo.app",
    "win1",
    "window_id=win1;app_id=demo.app",
    true
)

expect(wm_runtime_dispatch_wire(command)).to_equal("kind=window_focus;target=surf1;app=demo.app;window=win1;handled=true;payload=window_id=win1;app_id=demo.app")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wm_runtime_dispatch_wire_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WM runtime dispatch wire format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
