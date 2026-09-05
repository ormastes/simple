# Attach Session Specification

> Tests covering Chromium DevTools DOM mirror — basics, Chromium DevTools CSS inspector — computed styles, Chromium DevTools attach session — FSM, Chromium DevTools attach session — panel read path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Attach Session Specification

## Scenarios

### Chromium DevTools DOM mirror — basics

#### starts empty with root id -1

- starts empty with root id -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts empty with root id -1")
"""A fresh mirror has zero nodes and a sentinel root id."""
val mirror = DevToolsDomMirror.new()
expect(mirror.is_empty()).to_be_true()
expect(mirror.count() == 0).to_be_true()
expect(mirror.root_id_of() == -1).to_be_true()
```

</details>

#### push_element makes the first node the root

- push_element makes the first node the root


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_element makes the first node the root")
var mirror = DevToolsDomMirror.new()
val html_id = mirror.push_element("html", 0)
expect(mirror.count() == 1).to_be_true()
expect(mirror.root_id_of() == html_id).to_be_true()
expect(mirror.has_node(html_id)).to_be_true()
```

</details>

#### attach_child records parent/child links in order

- attach_child records parent/child links in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attach_child records parent/child links in order")
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

- push_text stores a text-node marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_text stores a text-node marker")
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

- max_depth reports the deepest depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("max_depth reports the deepest depth")
var mirror = DevToolsDomMirror.new()
mirror.push_element("html", 0)
mirror.push_element("body", 1)
mirror.push_element("div", 2)
mirror.push_element("span", 3)
expect(mirror.max_depth() == 3).to_be_true()
```

</details>

#### flattened_labels returns one label per node

- flattened_labels returns one label per node


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flattened_labels returns one label per node")
var mirror = DevToolsDomMirror.new()
mirror.push_element("html", 0)
mirror.push_element("body", 1)
val labels = mirror.flattened_labels()
expect(labels.len() == 2).to_be_true()
```

</details>

#### clear resets the mirror to empty

- clear resets the mirror to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear resets the mirror to empty")
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

- starts empty with no selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts empty with no selection")
val css = DevToolsCssInspector.new()
expect(css.is_empty()).to_be_true()
expect(not css.has_selection()).to_be_true()
expect(css.selected_id_of() == -1).to_be_true()
```

</details>

#### set_property lazily creates a block and stores the value

- set_property lazily creates a block and stores the value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_property lazily creates a block and stores the value")
var css = DevToolsCssInspector.new()
css.set_property(7, "color", "rgb(255,0,0)")
expect(css.has_block(7)).to_be_true()
val block = css.block_for(7)
expect(block.count() == 1).to_be_true()
expect(block.value_of("color") == "rgb(255,0,0)").to_be_true()
```

</details>

#### set_property keeps insertion order when updating

- set_property keeps insertion order when updating


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_property keeps insertion order when updating")
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

- select returns false for nodes without a block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("select returns false for nodes without a block")
var css = DevToolsCssInspector.new()
val ok = css.select(42)
expect(not ok).to_be_true()
expect(not css.has_selection()).to_be_true()
```

</details>

#### selected_lines returns the formatted property list

- selected_lines returns the formatted property list


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selected_lines returns the formatted property list")
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

- clear drops blocks and selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear drops blocks and selection")
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

- starts detached with no window


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts detached with no window")
val s = DevToolsAttachSession.new()
expect(s.is_detached()).to_be_true()
expect(s.window_id_of() == -1).to_be_true()
expect(s.snapshot_epoch_of() == 0).to_be_true()
```

</details>

#### attach flips the status to ATTACHED

- attach flips the status to ATTACHED


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attach flips the status to ATTACHED")
var s = DevToolsAttachSession.new()
val ok = s.attach(11)
expect(ok).to_be_true()
expect(s.is_attached()).to_be_true()
expect(s.window_id_of() == 11).to_be_true()
expect(s.status().code() == DEVTOOLS_STATUS_ATTACHED).to_be_true()
```

</details>

#### attach rejects negative window ids

- attach rejects negative window ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attach rejects negative window ids")
var s = DevToolsAttachSession.new()
val ok = s.attach(-5)
expect(not ok).to_be_true()
expect(s.is_detached()).to_be_true()
```

</details>

#### begin_snapshot + end_snapshot bumps the epoch

- begin_snapshot + end_snapshot bumps the epoch


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("begin_snapshot + end_snapshot bumps the epoch")
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

- detach clears the DOM mirror and CSS view


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detach clears the DOM mirror and CSS view")
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

- push_element on a detached session returns -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_element on a detached session returns -1")
var s = DevToolsAttachSession.new()
val id = s.push_element("html", 0)
expect(id == -1).to_be_true()
```

</details>

#### begin_snapshot on a detached session returns false

- begin_snapshot on a detached session returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("begin_snapshot on a detached session returns false")
var s = DevToolsAttachSession.new()
val ok = s.begin_snapshot()
expect(not ok).to_be_true()
```

</details>

### Chromium DevTools attach session — panel read path

#### dom_labels exposes one label per pushed node

- dom_labels exposes one label per pushed node


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dom_labels exposes one label per pushed node")
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

- set_style_property + select_node feeds the inspector


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_style_property + select_node feeds the inspector")
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

- status label reports the current FSM state


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("status label reports the current FSM state")
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

- DevToolsAttachStatus exposes rendering / attached / detached


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DevToolsAttachStatus exposes rendering / attached / detached")
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
| Source | `test/unit/app/ui.chromium.devtools/attach_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chromium DevTools DOM mirror — basics, Chromium DevTools CSS inspector — computed styles, Chromium DevTools attach session — FSM, Chromium DevTools attach session — panel read path.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68c1a71f6fd85f2e9ee99d52ab1a64758c41d026071157554c92cd34a357ff42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68c1a71f6fd85f2e9ee99d52ab1a64758c41d026071157554c92cd34a357ff42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68c1a71f6fd85f2e9ee99d52ab1a64758c41d026071157554c92cd34a357ff42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium.devtools/attach_session_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium.devtools/attach_session_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium.devtools/attach_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium.devtools/attach_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium.devtools/attach_session_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts empty with root id -1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium.devtools/attach_session_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'push_element makes the first node the root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium.devtools/attach_session_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attach_child records parent/child links in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
