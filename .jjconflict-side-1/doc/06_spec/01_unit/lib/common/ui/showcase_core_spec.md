# showcase_core — the shared, host-agnostic showcase logic

> `app.ui_showcase.showcase_core` is the single body of logic that four screen hosts (2d / gui / web / wm) run unchanged; only the `ScreenHost` impl differs between targets. This spec exercises it with no host at all, which is exactly the point: if any of these assertions needed a host, the "identical on four targets" claim would already be false.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# showcase_core — the shared, host-agnostic showcase logic

`app.ui_showcase.showcase_core` is the single body of logic that four screen hosts (2d / gui / web / wm) run unchanged; only the `ScreenHost` impl differs between targets. This spec exercises it with no host at all, which is exactly the point: if any of these assertions needed a host, the "identical on four targets" claim would already be false.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md |
| Design | doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/ui/showcase_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`app.ui_showcase.showcase_core` is the single body of logic that four screen
hosts (2d / gui / web / wm) run unchanged; only the `ScreenHost` impl differs
between targets. This spec exercises it with no host at all, which is exactly
the point: if any of these assertions needed a host, the "identical on four
targets" claim would already be false.

`WidgetNode` is a HANDLE over a process-global widget store, so every example
here uses its OWN id prefix. Two examples sharing a prefix would silently
share nodes and the results would be meaningless.

What is pinned: the toolbar is the existing `menubar` builder (kind
`menubar`, no new widget kind); both linked scroll panels exist; a wheel over
the left panel moves the right panel to the SAME offset while the deliberately
unlinked `_panel_free` panel stays at 0 (the negative control proving the link
is a real mechanism, not a global scroll); a scrollbar drag mirrors the same
way; a key event reaches the focused text input's `value`; the probe labels
change on every event so each input is VISIBLE in the rendered frame; and the
tree really does produce a non-empty `DrawIrV3Scene`.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md

## Design

**Design:** doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md

## Research

**Research:** N/A

## Examples

Wheel +3 over the left panel: left offset becomes positive, right offset
matches it exactly, free offset stays 0.

## Scenarios

### showcase_core — tree shape

#### builds a toolbar as the existing menubar widget with five items

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a toolbar as the existing menubar widget with five items
- Build under prefix sc_a and inspect the toolbar node
   - Expected: toolbar.kind_name() equals `menubar`
   - Expected: WidgetNode(id: "sc_a{SC_TOOLBAR}_menu_0").get_prop("label") equals `New`
   - Expected: WidgetNode(id: "sc_a{SC_TOOLBAR}_menu_4").get_prop("label") equals `Quit`
   - Expected: showcase_prefix(st) equals `sc_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds a toolbar as the existing menubar widget with five items")
step("Build under prefix sc_a and inspect the toolbar node")
val st = showcase_build("sc_a")
val toolbar = WidgetNode(id: "sc_a{SC_TOOLBAR}")

expect(toolbar.kind_name()).to_equal("menubar")
expect(WidgetNode(id: "sc_a{SC_TOOLBAR}_menu_0").get_prop("label")).to_equal("New")
expect(WidgetNode(id: "sc_a{SC_TOOLBAR}_menu_4").get_prop("label")).to_equal("Quit")
expect(showcase_prefix(st)).to_equal("sc_a")
```

</details>

#### builds two linked scroll panels plus an unlinked control panel

- builds two linked scroll panels plus an unlinked control panel
- All three scroll containers exist with kind scroll and offset 0
   - Expected: WidgetNode(id: "sc_b{SC_LINK_SRC}").kind_name() equals `scroll`
   - Expected: WidgetNode(id: "sc_b{SC_LINK_DST}").kind_name() equals `scroll`
   - Expected: WidgetNode(id: "sc_b{SC_FREE}").kind_name() equals `scroll`
   - Expected: showcase_scroll_offset("sc_b", SC_LINK_SRC) equals `0`
   - Expected: showcase_scroll_offset("sc_b", SC_LINK_DST) equals `0`
   - Expected: showcase_scroll_offset("sc_b", SC_FREE) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds two linked scroll panels plus an unlinked control panel")
step("All three scroll containers exist with kind scroll and offset 0")
val st = showcase_build("sc_b")

expect(WidgetNode(id: "sc_b{SC_LINK_SRC}").kind_name()).to_equal("scroll")
expect(WidgetNode(id: "sc_b{SC_LINK_DST}").kind_name()).to_equal("scroll")
expect(WidgetNode(id: "sc_b{SC_FREE}").kind_name()).to_equal("scroll")
expect(showcase_scroll_offset("sc_b", SC_LINK_SRC)).to_equal(0)
expect(showcase_scroll_offset("sc_b", SC_LINK_DST)).to_equal(0)
expect(showcase_scroll_offset("sc_b", SC_FREE)).to_equal(0)
```

</details>

#### builds an event probe pane with a focusable text input

- builds an event probe pane with a focusable text input
- The probe labels start in their reset state
   - Expected: probe_label("sc_c", SC_PROBE_LAST) equals `last: -`
   - Expected: probe_label("sc_c", SC_PROBE_CLICK) equals `clicks: 0`
   - Expected: probe_label("sc_c", SC_PROBE_DRAG) equals `drag: -`
   - Expected: WidgetNode(id: "sc_c{SC_PROBE_INPUT}").kind_name() equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds an event probe pane with a focusable text input")
step("The probe labels start in their reset state")
val st = showcase_build("sc_c")

expect(probe_label("sc_c", SC_PROBE_LAST)).to_equal("last: -")
expect(probe_label("sc_c", SC_PROBE_CLICK)).to_equal("clicks: 0")
expect(probe_label("sc_c", SC_PROBE_DRAG)).to_equal("drag: -")
expect(WidgetNode(id: "sc_c{SC_PROBE_INPUT}").kind_name()).to_equal("input")
```

</details>

### showcase_core — linked-panel scroll sync

#### a wheel over the left panel moves the right panel to the same offset, leaving the free panel at 0

- a wheel over the left panel moves the right panel to the same offset, leaving the free panel at 0
- Scroll the left panel with three wheel notches
- Left must have actually moved — otherwise mirroring 0 onto 0 would pass vacuously
   - Expected: left > 0 is true
   - Expected: right equals `left`
   - Expected: free equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a wheel over the left panel moves the right panel to the same offset, leaving the free panel at 0")
step("Scroll the left panel with three wheel notches")
var st = showcase_build("sc_d")
val px = panel_center_x(st, "sc_d{SC_LINK_SRC}")
val py = panel_center_y(st, "sc_d{SC_LINK_SRC}")
st = showcase_apply(st, host_pointer_wheel(px, py, 3), W, H)

val left = showcase_scroll_offset("sc_d", SC_LINK_SRC)
val right = showcase_scroll_offset("sc_d", SC_LINK_DST)
val free = showcase_scroll_offset("sc_d", SC_FREE)

step("Left must have actually moved — otherwise mirroring 0 onto 0 would pass vacuously")
expect(left > 0).to_equal(true)
expect(right).to_equal(left)
expect(free).to_equal(0)
```

</details>

#### the sync is one-directional: the free panel is never touched by a left-panel scroll

- the sync is one-directional: the free panel is never touched by a left-panel scroll
- Two successive wheels, checking the negative control each time
   - Expected: after_two > after_one is true
   - Expected: showcase_scroll_offset("sc_e", SC_LINK_DST) equals `after_two`
   - Expected: showcase_scroll_offset("sc_e", SC_FREE) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the sync is one-directional: the free panel is never touched by a left-panel scroll")
step("Two successive wheels, checking the negative control each time")
var st = showcase_build("sc_e")
val px = panel_center_x(st, "sc_e{SC_LINK_SRC}")
val py = panel_center_y(st, "sc_e{SC_LINK_SRC}")
st = showcase_apply(st, host_pointer_wheel(px, py, 2), W, H)
val after_one = showcase_scroll_offset("sc_e", SC_LINK_SRC)
st = showcase_apply(st, host_pointer_wheel(px, py, 2), W, H)
val after_two = showcase_scroll_offset("sc_e", SC_LINK_SRC)

expect(after_two > after_one).to_equal(true)
expect(showcase_scroll_offset("sc_e", SC_LINK_DST)).to_equal(after_two)
expect(showcase_scroll_offset("sc_e", SC_FREE)).to_equal(0)
```

</details>

#### a scrollbar drag (down, move, up) mirrors onto the linked panel

- a scrollbar drag (down, move, up) mirrors onto the linked panel
- Press, drag and release, then compare the two linked offsets
- The press must have really landed on the scrollbar gutter, not just anywhere
   - Expected: WidgetNode(id: "sc_f{SC_LINK_SRC}").get_prop("ui_scrollbar_dragging") equals `true`
   - Expected: dragged > 0 is true
   - Expected: showcase_scroll_offset("sc_f", SC_FREE) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a scrollbar drag (down, move, up) mirrors onto the linked panel")
step("Press, drag and release, then compare the two linked offsets")
var st = showcase_build("sc_f")
val rect = node_rect(st, "sc_f{SC_LINK_SRC}")
val gx = scrollbar_x(st, "sc_f{SC_LINK_SRC}")
st = showcase_apply(st, host_pointer_down(gx, rect.y + 4, HOST_BTN_LEFT), W, H)

step("The press must have really landed on the scrollbar gutter, not just anywhere")
expect(WidgetNode(id: "sc_f{SC_LINK_SRC}").get_prop("ui_scrollbar_dragging")).to_equal("true")

st = showcase_apply(st, host_pointer_move(gx, rect.y + rect.h - 4), W, H)
val dragged = showcase_scroll_offset("sc_f", SC_LINK_SRC)
expect(dragged > 0).to_equal(true)

st = showcase_apply(st, host_pointer_up(gx, rect.y + rect.h - 4, HOST_BTN_LEFT), W, H)

expect(showcase_scroll_offset("sc_f", SC_LINK_DST)).to_equal(
    showcase_scroll_offset("sc_f", SC_LINK_SRC)
)
expect(showcase_scroll_offset("sc_f", SC_FREE)).to_equal(0)
```

</details>

### showcase_core — event reducer and the visible probe

#### a matched left press and release counts one click and rewrites the click probe label

- a matched left press and release counts one click and rewrites the click probe label
- Press and release on the same focusable target
- A press only arms the target; activation waits for release
   - Expected: showcase_click_count("sc_g") equals `0`
   - Expected: st.focused_id == target is false
- The matching release activates exactly the armed target
   - Expected: probe_label("sc_g", SC_PROBE_LAST) contains `target`
   - Expected: st.focused_id equals `target`
   - Expected: showcase_click_count("sc_g") equals `1`
   - Expected: probe_label("sc_g", SC_PROBE_CLICK) equals `clicks: 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a matched left press and release counts one click and rewrites the click probe label")
step("Press and release on the same focusable target")
var st = showcase_build("sc_g")
val target = "sc_g{SC_PROBE_INPUT}"
val px = panel_center_x(st, target)
val py = panel_center_y(st, target)
st = showcase_apply(st, host_pointer_down(px, py, HOST_BTN_LEFT), W, H)

step("A press only arms the target; activation waits for release")
expect(showcase_click_count("sc_g")).to_equal(0)
expect(st.focused_id == target).to_equal(false)
st = showcase_apply(st, host_pointer_up(px, py, HOST_BTN_LEFT), W, H)

step("The matching release activates exactly the armed target")
expect(probe_label("sc_g", SC_PROBE_LAST).contains(target)).to_equal(true)
expect(st.focused_id).to_equal(target)
expect(showcase_click_count("sc_g")).to_equal(1)
expect(probe_label("sc_g", SC_PROBE_CLICK)).to_equal("clicks: 1")
```

</details>

#### does not activate when release lands outside the pressed target

- does not activate when release lands outside the pressed target
- Press the input, then release on a different widget
   - Expected: showcase_click_count("sc_g_cancel") equals `0`
   - Expected: st.focused_id == target is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not activate when release lands outside the pressed target")
step("Press the input, then release on a different widget")
var st = showcase_build("sc_g_cancel")
val target = "sc_g_cancel{SC_PROBE_INPUT}"
val px = panel_center_x(st, target)
val py = panel_center_y(st, target)
st = showcase_apply(st, host_pointer_down(px, py, HOST_BTN_LEFT), W, H)
st = showcase_apply(st, host_pointer_up(0, 0, HOST_BTN_LEFT), W, H)

expect(showcase_click_count("sc_g_cancel")).to_equal(0)
expect(st.focused_id == target).to_equal(false)
```

</details>

#### a drag (press then move) counts a drag and rewrites the drag probe label

- a drag (press then move) counts a drag and rewrites the drag probe label
- Press to set the anchor, then move
   - Expected: showcase_drag_count("sc_h") equals `1`
   - Expected: probe_label("sc_h", SC_PROBE_DRAG) equals `drag: 90,140 (1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a drag (press then move) counts a drag and rewrites the drag probe label")
step("Press to set the anchor, then move")
var st = showcase_build("sc_h")
st = showcase_apply(st, host_pointer_down(60, 20, HOST_BTN_LEFT), W, H)
st = showcase_apply(st, host_pointer_move(90, 140), W, H)

expect(showcase_drag_count("sc_h")).to_equal(1)
expect(probe_label("sc_h", SC_PROBE_DRAG)).to_equal("drag: 90,140 (1)")
```

</details>

#### a key event reaches the focused text input's committed value

- a key event reaches the focused text input's committed value
- Focus the probe input explicitly, then type x then y
- The widget layer's own value prop must hold the characters — not just our probe mirror
   - Expected: WidgetNode(id: "sc_i{SC_PROBE_INPUT}").get_prop("value") equals `xy`
   - Expected: showcase_typed_text("sc_i") equals `xy`
   - Expected: probe_label("sc_i", SC_PROBE_KEYS) equals `typed: xy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a key event reaches the focused text input's committed value")
step("Focus the probe input explicitly, then type x then y")
var st = showcase_build("sc_i")
st = showcase_focus(st, "sc_i{SC_PROBE_INPUT}")
st = showcase_apply(st, host_key_down(120, "x", 0), W, H)
st = showcase_apply(st, host_key_down(121, "y", 0), W, H)

step("The widget layer's own value prop must hold the characters — not just our probe mirror")
expect(WidgetNode(id: "sc_i{SC_PROBE_INPUT}").get_prop("value")).to_equal("xy")
expect(showcase_typed_text("sc_i")).to_equal("xy")
expect(probe_label("sc_i", SC_PROBE_KEYS)).to_equal("typed: xy")
```

</details>

#### a resize is recorded in the probe so it is visible in the next frame

- a resize is recorded in the probe so it is visible in the next frame
- Resize to 640x480
   - Expected: probe_label("sc_j", SC_PROBE_LAST) equals `last: resize 640x480`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a resize is recorded in the probe so it is visible in the next frame")
step("Resize to 640x480")
var st = showcase_build("sc_j")
st = showcase_apply(st, host_resize(640, 480), W, H)

expect(probe_label("sc_j", SC_PROBE_LAST)).to_equal("last: resize 640x480")
```

</details>

### showcase_core — frame production and report

#### the tree produces a non-empty DrawIrV3 scene through the value path

- the tree produces a non-empty DrawIrV3 scene through the value path
- widget_tree_to_draw_ir_cpu -> draw_ir_v2_to_v3
   - Expected: scene.commands.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the tree produces a non-empty DrawIrV3 scene through the value path")
step("widget_tree_to_draw_ir_cpu -> draw_ir_v2_to_v3")
val st = showcase_build("sc_k")
val scene = showcase_scene(st, W, H)

expect(scene.commands.len() > 0).to_equal(true)
```

</details>

#### showcase_report collects the transcript the evidence capture needs

- showcase_report collects the transcript the evidence capture needs
- Wheel, click and type, then read the report back
   - Expected: report.host_name equals `2d`
   - Expected: report.frames equals `7`
   - Expected: report.clicks equals `0`
   - Expected: report.typed_text equals `z`
   - Expected: report.left_offset > 0 is true
   - Expected: report.right_offset equals `report.left_offset`
   - Expected: report.free_offset equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("showcase_report collects the transcript the evidence capture needs")
step("Wheel, click and type, then read the report back")
var st = showcase_build("sc_l")
# Each node_rect call is a full compute_layout, so resolve both points
# in one pass — four separate centre lookups exceed the interpreter's
# 10M-operation budget for a single example.
# Click dispatch is covered by its own example above; this one stays
# lean (one layout, two events) because the report call on top of a
# third dispatch exceeds the interpreter's per-example budget.
val pan = node_rect(st, "sc_l{SC_LINK_SRC}")
st = showcase_apply(st, host_pointer_wheel(pan.x + pan.w / 2, pan.y + pan.h / 2, 2), W, H)
st = showcase_focus(st, "sc_l{SC_PROBE_INPUT}")
st = showcase_apply(st, host_key_down(122, "z", 0), W, H)
val report = showcase_report(st, "2d", 7)

expect(report.host_name).to_equal("2d")
expect(report.frames).to_equal(7)
expect(report.clicks).to_equal(0)
expect(report.typed_text).to_equal("z")
expect(report.left_offset > 0).to_equal(true)
expect(report.right_offset).to_equal(report.left_offset)
expect(report.free_offset).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md`
- **Design:** `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `90d6d8f0b95046c1c36514a19d95f449c5da6a9dbf87dbf20ad78d1e9c3b75f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90d6d8f0b95046c1c36514a19d95f449c5da6a9dbf87dbf20ad78d1e9c3b75f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90d6d8f0b95046c1c36514a19d95f449c5da6a9dbf87dbf20ad78d1e9c3b75f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/showcase_core_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/showcase_core_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/showcase_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/showcase_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/showcase_core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/showcase_core_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a toolbar as the existing menubar widget with five items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/showcase_core_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds two linked scroll panels plus an unlinked control panel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/showcase_core_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds an event probe pane with a focusable text input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
