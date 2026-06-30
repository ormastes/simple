# Attach Session Specification

> _Live DOM mirror surfaced by M10 — push / find / flatten semantics.""_

<!-- sdn-diagram:id=attach_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=attach_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

attach_session_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=attach_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Attach Session Specification

## Scenarios

### Chromium DevTools DOM mirror — basics
_Live DOM mirror surfaced by M10 — push / find / flatten semantics.""_

#### starts empty with root id -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mirror = DevToolsDomMirror.new()
expect(mirror.is_empty()).to_be_true()
expect(mirror.count() == 0).to_be_true()
expect(mirror.root_id_of() == -1).to_be_true()
```

</details>

#### push_element makes the first node the root

- var mirror = DevToolsDomMirror new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mirror = DevToolsDomMirror.new()
val html_id = mirror.push_element("html", 0)
expect(mirror.count() == 1).to_be_true()
expect(mirror.root_id_of() == html_id).to_be_true()
expect(mirror.has_node(html_id)).to_be_true()
```

</details>

#### attach_child records parent/child links in order

- var mirror = DevToolsDomMirror new


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mirror = DevToolsDomMirror.new()
val root = mirror.push_element("html", 0)
val body = mirror.push_element("body", 1)
val div  = mirror.push_element("div", 2)
val ok1 = mirror.attach_child(root, body)
val ok2 = mirror.attach_child(body, div)
expect(ok1).to_be_true()
expect(ok2).to_be_true()
val root_idx = mirror.find_by_id(root)
expect(root_idx == 0).to_be_true()
val root_node = mirror.node_at(root_idx)
expect(root_node.child_count() == 1).to_be_true()
```

</details>

#### set_bounds stores geometry on the target node

- var mirror = DevToolsDomMirror new


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mirror = DevToolsDomMirror.new()
val div = mirror.push_element("div", 0)
val ok = mirror.set_bounds(div, 12, 34, 56, 78)
expect(ok).to_be_true()
val node = mirror.node_at(mirror.find_by_id(div))
expect(node.has_bounds()).to_be_true()
expect(node.x == 12).to_be_true()
expect(node.y == 34).to_be_true()
expect(node.width == 56).to_be_true()
expect(node.height == 78).to_be_true()
```

</details>

#### push_text stores a text-node marker

- var mirror = DevToolsDomMirror new
- mirror push element


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mirror = DevToolsDomMirror.new()
mirror.push_element("p", 0)
val tid = mirror.push_text("hello", 1)
expect(mirror.has_node(tid)).to_be_true()
val idx = mirror.find_by_id(tid)
val n = mirror.node_at(idx)
expect(n.is_text()).to_be_true()
```

</details>

#### max_depth reports the deepest depth

- var mirror = DevToolsDomMirror new
- mirror push element
- mirror push element
- mirror push element
- mirror push element


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mirror = DevToolsDomMirror.new()
mirror.push_element("html", 0)
mirror.push_element("body", 1)
mirror.push_element("div", 2)
mirror.push_element("span", 3)
expect(mirror.max_depth() == 3).to_be_true()
```

</details>

#### flattened_labels returns one label per node

- var mirror = DevToolsDomMirror new
- mirror push element
- mirror push element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mirror = DevToolsDomMirror.new()
mirror.push_element("html", 0)
mirror.push_element("body", 1)
val labels = mirror.flattened_labels()
expect(labels.len() == 2).to_be_true()
```

</details>

#### clear resets the mirror to empty

- var mirror = DevToolsDomMirror new
- mirror push element
- mirror push element
- mirror clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mirror = DevToolsDomMirror.new()
mirror.push_element("html", 0)
mirror.push_element("body", 1)
mirror.clear()
expect(mirror.is_empty()).to_be_true()
expect(mirror.root_id_of() == -1).to_be_true()
```

</details>

### Chromium DevTools CSS inspector — computed styles

#### starts empty with no selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = DevToolsCssInspector.new()
expect(css.is_empty()).to_be_true()
expect(not css.has_selection()).to_be_true()
expect(css.selected_id_of() == -1).to_be_true()
```

</details>

#### set_property lazily creates a block and stores the value

- var css = DevToolsCssInspector new
- css set property


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var css = DevToolsCssInspector.new()
css.set_property(7, "color", "rgb(255,0,0)")
expect(css.has_block(7)).to_be_true()
val block = css.block_for(7)
expect(block.count() == 1).to_be_true()
expect(block.value_of("color") == "rgb(255,0,0)").to_be_true()
```

</details>

#### set_property keeps insertion order when updating

- var css = DevToolsCssInspector new
- css set property
- css set property
- css set property


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var css = DevToolsCssInspector.new()
css.set_property(1, "color", "red")
css.set_property(1, "background", "blue")
css.set_property(1, "color", "green")
val block = css.block_for(1)
expect(block.count() == 2).to_be_true()
expect(block.value_of("color") == "green").to_be_true()
expect(block.value_of("background") == "blue").to_be_true()
```

</details>

#### select returns false for nodes without a block

- var css = DevToolsCssInspector new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var css = DevToolsCssInspector.new()
val ok = css.select(42)
expect(not ok).to_be_true()
expect(not css.has_selection()).to_be_true()
```

</details>

#### selected_lines returns the formatted property list

- var css = DevToolsCssInspector new
- css set property
- css set property


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var css = DevToolsCssInspector.new()
css.set_property(3, "color", "red")
css.set_property(3, "margin", "4px")
val ok = css.select(3)
expect(ok).to_be_true()
val lines = css.selected_lines()
expect(lines.len() == 2).to_be_true()
```

</details>

#### clear drops blocks and selection

- var css = DevToolsCssInspector new
- css set property
- css select
- css clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var css = DevToolsCssInspector.new()
css.set_property(1, "color", "red")
css.select(1)
css.clear()
expect(css.is_empty()).to_be_true()
expect(not css.has_selection()).to_be_true()
```

</details>

### Chromium DevTools attach session — FSM

#### starts detached with no window

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = DevToolsAttachSession.new()
expect(s.is_detached()).to_be_true()
expect(s.window_id_of() == -1).to_be_true()
expect(s.snapshot_epoch_of() == 0).to_be_true()
```

</details>

#### attach flips the status to ATTACHED

- var s = DevToolsAttachSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
val ok = s.attach(11)
expect(ok).to_be_true()
expect(s.is_attached()).to_be_true()
expect(s.window_id_of() == 11).to_be_true()
expect(s.status().label() == "attached").to_be_true()
```

</details>

#### attach rejects negative window ids

- var s = DevToolsAttachSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
val ok = s.attach(-5)
expect(not ok).to_be_true()
expect(s.is_detached()).to_be_true()
```

</details>

#### begin_snapshot + end_snapshot bumps the epoch

- var s = DevToolsAttachSession new
- s attach
- s begin snapshot
- s push element


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
s.attach(3)
s.begin_snapshot()
s.push_element("html", 0)
val done = s.end_snapshot()
expect(done).to_be_true()
expect(s.is_rendering()).to_be_true()
expect(s.snapshot_epoch_of() == 1).to_be_true()
```

</details>

#### detach clears the DOM mirror and CSS view

- var s = DevToolsAttachSession new
- s attach
- s begin snapshot
- s push element
- s set style property
- s end snapshot
- s detach


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
s.attach(5)
s.begin_snapshot()
s.push_element("html", 0)
s.set_style_property(1, "color", "red")
s.end_snapshot()
s.detach()
expect(s.is_detached()).to_be_true()
expect(s.dom_node_count() == 0).to_be_true()
expect(s.css().is_empty()).to_be_true()
```

</details>

#### push_element on a detached session returns -1

- var s = DevToolsAttachSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
val id = s.push_element("html", 0)
expect(id == -1).to_be_true()
```

</details>

#### begin_snapshot on a detached session returns false

- var s = DevToolsAttachSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
val ok = s.begin_snapshot()
expect(not ok).to_be_true()
```

</details>

### Chromium DevTools attach session — panel read path

#### dom_labels exposes one label per pushed node

- var s = DevToolsAttachSession new
- s attach
- s begin snapshot
- s push element
- s push element
- s push text
- s end snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
s.attach(1)
s.begin_snapshot()
s.push_element("html", 0)
s.push_element("body", 1)
s.push_text("hi", 2)
s.end_snapshot()
val labels = s.dom_labels()
expect(labels.len() == 3).to_be_true()
expect(s.dom_root_id() > 0).to_be_true()
```

</details>

#### set_style_property + select_node feeds the inspector

- var s = DevToolsAttachSession new
- s attach
- s begin snapshot
- s set node bounds
- s set style property
- s set style property
- s end snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
s.attach(1)
s.begin_snapshot()
val root = s.push_element("div", 0)
s.set_node_bounds(root, 20, 30, 140, 48)
s.set_style_property(root, "color", "red")
s.set_style_property(root, "margin", "2px")
s.end_snapshot()
val picked = s.select_node(root)
expect(picked).to_be_true()
val lines = s.selected_style_lines()
expect(lines.len() == 2).to_be_true()
val node = s.dom().node_at(s.dom().find_by_id(root))
expect(node.has_bounds()).to_be_true()
expect(node.width == 140).to_be_true()
```

</details>

#### set_node_bounds returns false while detached

- var s = DevToolsAttachSession new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
val ok = s.set_node_bounds(1, 0, 0, 10, 10)
expect(not ok).to_be_true()
```

</details>

#### status label reports the current FSM state

- var s = DevToolsAttachSession new
- s attach
- s begin snapshot
- s push element
- s end snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
expect(s.status().label() == "detached").to_be_true()
s.attach(2)
expect(s.status().label() == "attached").to_be_true()
s.begin_snapshot()
s.push_element("html", 0)
s.end_snapshot()
expect(s.status().label() == "rendering").to_be_true()
```

</details>

#### DevToolsAttachStatus exposes rendering / attached / detached

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = DevToolsAttachStatus.detached()
val a = DevToolsAttachStatus.attached()
val r = DevToolsAttachStatus.rendering()
expect(d.is_detached()).to_be_true()
expect(a.is_attached()).to_be_true()
expect(r.is_rendering()).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium.devtools/attach_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chromium DevTools DOM mirror — basics
- Chromium DevTools CSS inspector — computed styles
- Chromium DevTools attach session — FSM
- Chromium DevTools attach session — panel read path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
