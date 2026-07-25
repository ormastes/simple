# X11 Backend Gate Specification

> <details>

<!-- sdn-diagram:id=x11_backend_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x11_backend_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x11_backend_gate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x11_backend_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X11 Backend Gate Specification

## Scenarios

### X11-class backend readiness gate

### feature coverage

#### lists native WM features needed by a future Wine backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = x11_backend_required_features()
expect(required.len()).to_be_greater_than(10)
expect(required[0]).to_equal("display")
```

</details>

#### reports the first missing X11-class renderer feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = x11_backend_gate("display screen window map-unmap configure surface damage clip expose present input focus atom property wm-name wm-class wm-protocols")
expect(state).to_equal("missing-wm-state")
```

</details>

#### returns ready when all required features are declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = x11_backend_gate("display screen window map-unmap configure surface damage clip expose present input focus atom property wm-name wm-class wm-protocols wm-state cursor clipboard text glyph blit fill")
expect(state).to_equal("ready")
```

</details>

### event coverage

#### requires a full window lifecycle and interaction stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = x11_backend_event_gate("create map configure expose focus input")
expect(state).to_equal("missing-unmap")
```

</details>

### pixel coverage

#### requires golden, damage, text, cursor, and present evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = x11_backend_pixel_gate("golden damage text")
expect(state).to_equal("missing-cursor")
```

</details>

### WM property coverage

#### requires X11 WM atoms and properties that Wine checks during window setup

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = x11_backend_property_gate("WM_NAME WM_CLASS WM_PROTOCOLS")
expect(state).to_equal("missing-_NET_WM_STATE")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/x11_backend_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- X11-class backend readiness gate
- feature coverage
- event coverage
- pixel coverage
- WM property coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
