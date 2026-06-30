# Wine Simpleos Window Bridge Specification

> <details>

<!-- sdn-diagram:id=wine_simpleos_window_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_simpleos_window_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_simpleos_window_bridge_spec -> common
wine_simpleos_window_bridge_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_simpleos_window_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Simpleos Window Bridge Specification

## Scenarios

### Wine SimpleOS window bridge

#### starts with only SimpleOS winfs evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bridge = wine_simpleos_window_bridge_new()
expect(wine_simpleos_window_bridge_gate(bridge)).to_equal("missing-simpleos-window-record")
```

</details>

#### creates WindowRecord framebuffer metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 42, "wine", "hello", 320, 200)
expect(created.ok).to_equal(true)
expect(created.record.buffer_ref.kind).to_equal("simpleos-framebuffer")
expect(created.record.buffer_ref.bytes).to_equal(256000)
```

</details>

#### rejects invalid and missing window operations with structured states

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 0, "wine", "bad", 320, 200)
expect(invalid.state).to_equal("invalid-window")
val missing = wine_simpleos_map_window(wine_simpleos_window_bridge_new(), 99)
expect(missing.state).to_equal("missing-window")
```

</details>

#### records deterministic present checksum evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 1, "wine", "hello", 10, 10)
val mapped = wine_simpleos_map_window(created.bridge, 1)
val presented = wine_simpleos_present_window(mapped.bridge, 1, 5)
expect(presented.bridge.checksum).to_equal(406)
expect(wine_simpleos_window_evidence(presented.bridge)).to_contain("framebuffer-checksum")
expect(wine_simpleos_window_bridge_gate(presented.bridge)).to_equal("missing-unmap")
```

</details>

#### requires SimpleOS cursor and clipboard evidence before X11 bridge readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 1, "wine", "hello", 320, 200)
val mapped = wine_simpleos_map_window(created.bridge, 1)
val configured = wine_simpleos_configure_window(mapped.bridge, 1, 10, 20, 640, 480)
val focused = wine_simpleos_focus_window(configured.bridge, 1)
val presented = wine_simpleos_present_window(focused.bridge, 1, 7)
val unmapped = wine_simpleos_unmap_window(presented.bridge, 1)
val destroyed = wine_simpleos_destroy_window(unmapped.bridge, 1)
expect(wine_simpleos_window_bridge_gate(destroyed.bridge)).to_equal("missing-cursor")
val cursor = wine_simpleos_set_cursor(destroyed.bridge, "arrow")
expect(wine_simpleos_window_bridge_gate(cursor.bridge)).to_equal("missing-clipboard")
```

</details>

#### unmaps WindowRecord state without destroying the record

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 1, "wine", "hello", 10, 10)
val mapped = wine_simpleos_map_window(created.bridge, 1)
val unmapped = wine_simpleos_unmap_window(mapped.bridge, 1)
expect(unmapped.ok).to_equal(true)
expect(unmapped.state).to_equal("unmapped")
expect(unmapped.record.state).to_equal(WindowState.Hidden)
expect(wine_simpleos_window_evidence(unmapped.bridge)).to_contain("unmap")
```

</details>

#### reaches the production bridge gate after lifecycle operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val destroyed = _ready_bridge()
expect(destroyed.record.state).to_equal(WindowState.Destroyed)
expect(wine_simpleos_window_bridge_gate(destroyed.bridge)).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wine_simpleos_window_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine SimpleOS window bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
