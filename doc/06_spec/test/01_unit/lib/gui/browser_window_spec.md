# Browser Window Specification

> <details>

<!-- sdn-diagram:id=browser_window_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_window_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_window_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_window_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Window Specification

## Scenarios

### BrowserWindow.new

#### sets id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = _make_window()
expect w.id to_equal 99
```

</details>

#### sets title

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = _make_window()
expect w.title to_equal "Test Window"
```

</details>

#### sets bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = _make_window()
expect w.bounds.right to_equal 1280.0
```

</details>

### WindowStyle.default

#### has frame=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = WindowStyle.default()
expect s.frame to_equal true
```

</details>

#### has transparent=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = WindowStyle.default()
expect s.transparent to_equal false
```

</details>

### BrowserWindow visibility

#### show sets is_visible=true

1. var w =  make window
2. w show


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = _make_window()
w.show()
expect w.is_visible to_equal true
```

</details>

#### hide sets is_visible=false

1. var w =  make window
2. w show
3. w hide


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = _make_window()
w.show()
w.hide()
expect w.is_visible to_equal false
```

</details>

### BrowserWindow mutations

#### set_title updates

1. var w =  make window
2. w set title


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = _make_window()
w.set_title("Updated")
expect w.title to_equal "Updated"
```

</details>

#### set_bounds updates

1. var w =  make window
2. w set bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = _make_window()
val new_bounds = SkRect(left: 0.0, top: 0.0, right: 640.0, bottom: 480.0)
w.set_bounds(new_bounds)
expect w.bounds.right to_equal 640.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gui/browser_window_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserWindow.new
- WindowStyle.default
- BrowserWindow visibility
- BrowserWindow mutations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
