# Compositor Specification

> <details>

<!-- sdn-diagram:id=compositor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compositor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compositor_spec -> std
compositor_spec -> nogc_async_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compositor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compositor Specification

## Scenarios

### WM Compositor ECS World

#### starts empty with no windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
expect(wm_compositor_window_count(c)).to_equal(0)
```

</details>

#### creates a window and increments count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
val r = wm_compositor_window_create(c, 1, "wine-app", "Hello", 640, 480)
expect(r.ok).to_equal(true)
expect(r.state).to_equal("created")
expect(wm_compositor_window_count(r.compositor)).to_equal(1)
```

</details>

#### rejects creating a window with id 0 or duplicate id

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
val bad = wm_compositor_window_create(c, 0, "wine-app", "Bad", 640, 480)
expect(bad.ok).to_equal(false)
expect(bad.state).to_equal("invalid-id")
val r1 = wm_compositor_window_create(c, 2, "wine-app", "Win", 640, 480)
val dup = wm_compositor_window_create(r1.compositor, 2, "wine-app", "Dup", 320, 200)
expect(dup.ok).to_equal(false)
expect(dup.state).to_equal("window-exists")
```

</details>

#### configures geometry and increments generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
val r1 = wm_compositor_window_create(c, 1, "wine-app", "Win", 320, 200)
val r2 = wm_compositor_window_configure(r1.compositor, 1, 10, 20, 800, 600)
expect(r2.ok).to_equal(true)
expect(r2.state).to_equal("configured")
expect(r2.generation).to_be_greater_than(0)
```

</details>

#### records focus state for the active window

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
val r1 = wm_compositor_window_create(c, 5, "wine-app", "Win", 640, 480)
val r2 = wm_compositor_window_focus(r1.compositor, 5)
expect(r2.ok).to_equal(true)
expect(r2.state).to_equal("focused")
expect(r2.focused_id).to_equal(5)
```

</details>

#### records framebuffer present with nonzero checksum evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
val r1 = wm_compositor_window_create(c, 1, "wine-app", "Win", 10, 10)
val r2 = wm_compositor_window_present(r1.compositor, 1, 5)
expect(r2.ok).to_equal(true)
expect(r2.state).to_equal("presented")
expect(r2.checksum).to_be_greater_than(0)
```

</details>

#### tracks cursor and clipboard state

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
val r1 = wm_compositor_set_cursor(c, "crosshair")
expect(r1.ok).to_equal(true)
expect(r1.cursor_name).to_equal("crosshair")
val r2 = wm_compositor_set_clipboard(r1.compositor, "some text")
expect(r2.ok).to_equal(true)
val clip = wm_compositor_get_clipboard(r2.compositor)
expect(clip).to_equal("some text")
```

</details>

#### destroys a window and decrements count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
val r1 = wm_compositor_window_create(c, 3, "wine-app", "Win", 640, 480)
val r2 = wm_compositor_window_destroy(r1.compositor, 3)
expect(r2.ok).to_equal(true)
expect(r2.state).to_equal("destroyed")
expect(wm_compositor_window_count(r2.compositor)).to_equal(0)
```

</details>

#### rejects configure/focus/present/destroy on missing window

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = wm_compositor_new()
val rc = wm_compositor_window_configure(c, 99, 0, 0, 640, 480)
expect(rc.ok).to_equal(false)
expect(rc.state).to_equal("missing-window")
val rf = wm_compositor_window_focus(c, 99)
expect(rf.ok).to_equal(false)
val rp = wm_compositor_window_present(c, 99, 1)
expect(rp.ok).to_equal(false)
val rd = wm_compositor_window_destroy(c, 99)
expect(rd.ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/wm/compositor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WM Compositor ECS World

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
