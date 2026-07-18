# Wine X11 Adapter Specification

> <details>

<!-- sdn-diagram:id=wine_x11_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_x11_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_x11_adapter_spec -> nogc_async_mut
wine_x11_adapter_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_x11_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine X11 Adapter Specification

## Scenarios

### Wine X11-class backend adapter

#### starts with only display and screen discovery

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = wine_x11_backend_new()
expect(wine_x11_backend_feature_gate(backend)).to_equal("missing-window")
expect(wine_x11_backend_event_state(backend)).to_equal("missing-create")
```

</details>

#### creates, maps, configures, focuses, and unmaps windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
expect(created.state).to_equal("created")
val mapped = wine_x11_map_window(created.backend, "w1")
val configured = wine_x11_configure_window(mapped.backend, "w1", 800, 600)
val focused = wine_x11_focus_window(configured.backend, "w1")
val unmapped = wine_x11_unmap_window(focused.backend, "w1")
expect(focused.backend.focused_window).to_equal("w1")
expect(unmapped.backend.focused_window).to_equal("")
expect(wine_x11_backend_event_state(focused.backend)).to_equal("missing-unmap")
expect(wine_x11_backend_event_state(unmapped.backend)).to_equal("missing-expose")
```

</details>

#### rejects operations on missing windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val damaged = wine_x11_damage_window(wine_x11_backend_new(), "missing")
expect(damaged.ok).to_equal(false)
expect(damaged.state).to_equal("missing-window")
```

</details>

#### records damage, present, text, glyph, fill, and cursor pixel evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val mapped = wine_x11_map_window(created.backend, "w1")
val damaged = wine_x11_damage_window(mapped.backend, "w1")
val filled = wine_x11_fill_window(damaged.backend, "w1")
val texted = wine_x11_text_window(filled.backend, "w1", "abc")
val cursor = wine_x11_set_cursor(texted.backend, "ibeam")
expect(cursor.backend.features).to_contain("glyph")
expect(wine_x11_backend_pixel_state(cursor.backend)).to_equal("ready")
```

</details>

#### records clipboard and destroy events

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val clip = wine_x11_set_clipboard(created.backend, "hello")
val destroyed = wine_x11_destroy_window(clip.backend, "w1")
expect(destroyed.backend.clipboard_text).to_equal("hello")
expect(destroyed.backend.mapped_windows.len()).to_equal(0)
```

</details>

#### records X11 WM atom and property evidence for Wine windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val atom = wine_x11_intern_atom(created.backend, "WM_DELETE_WINDOW")
val named = wine_x11_set_wm_name(atom.backend, "w1", "hello")
val classed = wine_x11_set_wm_class(named.backend, "w1", "hello.exe", "Wine")
val protocols = wine_x11_set_wm_protocols(classed.backend, "w1", ["WM_DELETE_WINDOW"])
val stated = wine_x11_set_wm_state(protocols.backend, "w1", "_NET_WM_STATE_NORMAL")
expect(stated.backend.features).to_contain("wm-protocols")
expect(stated.backend.properties).to_contain("WM_DELETE_WINDOW")
expect(wine_x11_backend_property_state(stated.backend)).to_equal("ready")
```

</details>

#### rejects invalid X11 WM property operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val empty_atom = wine_x11_intern_atom(created.backend, "")
expect(empty_atom.ok).to_equal(false)
expect(empty_atom.state).to_equal("invalid-atom")
val missing_window = wine_x11_set_wm_name(created.backend, "missing", "hello")
expect(missing_window.ok).to_equal(false)
expect(missing_window.state).to_equal("missing-window")
val empty_protocols = wine_x11_set_wm_protocols(created.backend, "w1", [])
expect(empty_protocols.ok).to_equal(false)
expect(empty_protocols.state).to_equal("invalid-property")
```

</details>

#### polls deterministic X11-class events in FIFO order

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val mapped = wine_x11_map_window(created.backend, "w1")
val configured = wine_x11_configure_window(mapped.backend, "w1", 800, 600)
val first = wine_x11_poll_event(configured.backend)
val second = wine_x11_poll_event(first.backend)
val third = wine_x11_poll_event(second.backend)
val empty = wine_x11_poll_event(third.backend)
expect(configured.backend.event_queue.len()).to_equal(3)
expect(first.event).to_equal("create:w1")
expect(second.event).to_equal("map:w1")
expect(third.event).to_equal("configure:w1")
expect(empty.state).to_equal("event-queue-empty")
```

</details>

#### reaches the existing X11-class feature, event, and pixel gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _ready_backend()
expect(result.ok).to_equal(true)
expect(wine_x11_backend_feature_gate(result.backend)).to_equal("ready")
expect(wine_x11_backend_event_state(result.backend)).to_equal("ready")
expect(wine_x11_backend_pixel_state(result.backend)).to_equal("ready")
expect(wine_x11_backend_property_state(result.backend)).to_equal("ready")
expect(wine_x11_backend_ready(result.backend)).to_equal("ready")
```

</details>

#### does not treat modeled X11 readiness as production readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _ready_backend()
expect(wine_x11_backend_ready(result.backend)).to_equal("ready")
expect(wine_x11_backend_production_ready(result.backend)).to_equal("missing-simpleos-window-record")
```

</details>

#### binds SimpleOS window evidence for production readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _ready_backend()
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 1, "wine", "hello", 640, 480)
val mapped = wine_simpleos_map_window(created.bridge, 1)
val configured = wine_simpleos_configure_window(mapped.bridge, 1, 0, 0, 640, 480)
val focused = wine_simpleos_focus_window(configured.bridge, 1)
val presented = wine_simpleos_present_window(focused.bridge, 1, 3)
val cursor = wine_simpleos_set_cursor(presented.bridge, "arrow")
val clipboard = wine_simpleos_set_clipboard(cursor.bridge, "clip")
val unmapped = wine_simpleos_unmap_window(clipboard.bridge, 1)
val destroyed = wine_simpleos_destroy_window(unmapped.bridge, 1)
val bound = wine_x11_backend_bind_simpleos(result.backend, destroyed.bridge)
expect(bound.ok).to_equal(true)
expect(wine_x11_backend_production_ready(bound.backend)).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wine_x11_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine X11-class backend adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
