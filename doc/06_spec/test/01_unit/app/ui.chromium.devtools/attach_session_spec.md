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
| 24 | 24 | 0 | 0 |

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

1. var mirror = DevToolsDomMirror new


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

1. var mirror = DevToolsDomMirror new


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

#### push_text stores a text-node marker

1. var mirror = DevToolsDomMirror new
2. mirror push element


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

1. var mirror = DevToolsDomMirror new
2. mirror push element
3. mirror push element
4. mirror push element
5. mirror push element


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

1. var mirror = DevToolsDomMirror new
2. mirror push element
3. mirror push element


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

1. var mirror = DevToolsDomMirror new
2. mirror push element
3. mirror push element
4. mirror clear


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

1. var css = DevToolsCssInspector new
2. css set property


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

1. var css = DevToolsCssInspector new
2. css set property
3. css set property
4. css set property


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

1. var css = DevToolsCssInspector new


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

1. var css = DevToolsCssInspector new
2. css set property
3. css set property


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

1. var css = DevToolsCssInspector new
2. css set property
3. css select
4. css clear


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

1. var s = DevToolsAttachSession new


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
expect(s.status().code() == DEVTOOLS_STATUS_ATTACHED).to_be_true()
```

</details>

#### attach rejects negative window ids

1. var s = DevToolsAttachSession new


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

1. var s = DevToolsAttachSession new
2. s attach
3. s begin snapshot
4. s push element


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

1. var s = DevToolsAttachSession new
2. s attach
3. s begin snapshot
4. s push element
5. s set style property
6. s end snapshot
7. s detach


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

1. var s = DevToolsAttachSession new


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

1. var s = DevToolsAttachSession new


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

1. var s = DevToolsAttachSession new
2. s attach
3. s begin snapshot
4. s push element
5. s push element
6. s push text
7. s end snapshot


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

1. var s = DevToolsAttachSession new
2. s attach
3. s begin snapshot
4. s set style property
5. s set style property
6. s end snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = DevToolsAttachSession.new()
s.attach(1)
s.begin_snapshot()
val root = s.push_element("div", 0)
s.set_style_property(root, "color", "red")
s.set_style_property(root, "margin", "2px")
s.end_snapshot()
val picked = s.select_node(root)
expect(picked).to_be_true()
val lines = s.selected_style_lines()
expect(lines.len() == 2).to_be_true()
```

</details>

#### status label reports the current FSM state

1. var s = DevToolsAttachSession new
2. s attach
3. s begin snapshot
4. s push element
5. s end snapshot


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
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
