# wm_focus_zorder_system_spec

> As a WM developer I need proof that focus and z-order are not just booleans

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_focus_zorder_system_spec

As a WM developer I need proof that focus and z-order are not just booleans

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/wm/wm_focus_zorder_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a WM developer I need proof that focus and z-order are not just booleans
that get set and forgotten, but actually change which window's pixels win an
overlap and which window's client receives keyboard input. Every example
below builds two (or three) overlapping windows filled with distinct pinned
probe colours and reads the *composited* pixel buffer to see which window is
really on top, and routes real committed-text keyboard input through
`HostGuiEventRouter` to see which window's session really receives it -- a
compositor that flips the
`focused` flag without actually reordering paint or gating input cannot pass
by declaration.

## Scenarios

### WM focus and z-order

<details>
<summary>Advanced: clicking a background window raises and focuses it</summary>

#### clicking a background window raises and focuses it _(slow)_

- clicking a background window raises and focuses it
- Create two overlapping windows; B was created last so it starts focused/top
   - Expected: before_overlap equals `COLOR_B`
   - Expected: _focused_by_id(compositor, win_b_id) is true
   - Expected: _focused_by_id(compositor, win_a_id) is false
- Click window A's body, away from B's rect, and release
- A is now focused and its colour now owns the overlap pixel
   - Expected: _focused_by_id(compositor, win_a_id) is true
   - Expected: _focused_by_id(compositor, win_b_id) is false
   - Expected: after_overlap equals `COLOR_A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clicking a background window raises and focuses it")
step("Create two overlapping windows; B was created last so it starts focused/top")
var compositor = _zorder_compositor()
val win_a_id = compositor.windows[0].id
val win_b_id = compositor.windows[1].id
compositor.render_frame()
val before = compositor.pure_simple_pixel_buffer()
val before_overlap = _pixel_at(before, compositor.width, OVERLAP_X, OVERLAP_Y)
expect(before_overlap).to_equal(COLOR_B)
expect(_focused_by_id(compositor, win_b_id)).to_equal(true)
expect(_focused_by_id(compositor, win_a_id)).to_equal(false)

step("Click window A's body, away from B's rect, and release")
compositor.handle_mouse_move(CLICK_A_X, CLICK_A_Y)
compositor.handle_left_button(true)
compositor.handle_left_button(false)

step("A is now focused and its colour now owns the overlap pixel")
expect(_focused_by_id(compositor, win_a_id)).to_equal(true)
expect(_focused_by_id(compositor, win_b_id)).to_equal(false)
compositor.render_frame()
val after = compositor.pure_simple_pixel_buffer()
val after_overlap = _pixel_at(after, compositor.width, OVERLAP_X, OVERLAP_Y)
expect(after_overlap).to_equal(COLOR_A)
print "wm_zorder_click_raise before_overlap={before_overlap} after_overlap={after_overlap}"
```

</details>


</details>

<details>
<summary>Advanced: focused window receives keyboard events, unfocused does not</summary>

#### focused window receives keyboard events, unfocused does not _(slow)_

- focused window receives keyboard events, unfocused does not
- Create two overlapping windows and two per-window routers
   - Expected: _focused_by_id(compositor, win_b_id) is true
- Route committed keyboard text through the focused window's router
   - Expected: routed_to_b is true
- The same committed text routed through the unfocused window's router is dropped
   - Expected: routed_to_a is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("focused window receives keyboard events, unfocused does not")
step("Create two overlapping windows and two per-window routers")
val tree = build_tree(column("root", [
    with_height(text_field("name", "", "Name"), 24)
]))
var session = UISession.new(tree)
var compositor = _zorder_compositor()
val win_a_id = compositor.windows[0].id
val win_b_id = compositor.windows[1].id
var router_a = HostGuiEventRouter.new(win_a_id)
var router_b = HostGuiEventRouter.new(win_b_id)
expect(_focused_by_id(compositor, win_b_id)).to_equal(true)

step("Route committed keyboard text through the focused window's router")
var text_event = window_event_none()
text_event.kind = WINDOW_EVENT_TEXT
val routed_to_b = router_b.route(text_event, compositor, session, "hi")
expect(routed_to_b).to_equal(true)

step("The same committed text routed through the unfocused window's router is dropped")
val routed_to_a = router_a.route(text_event, compositor, session, "hi")
expect(routed_to_a).to_equal(false)
print "wm_zorder_key_gate routed_to_focused={routed_to_b} routed_to_unfocused={routed_to_a}"
```

</details>


</details>

<details>
<summary>Advanced: z-order is stable across a damage-only redraw</summary>

#### z-order is stable across a damage-only redraw _(slow)_

- z-order is stable across a damage-only redraw
- Create two overlapping windows and confirm B (top) owns the overlap
   - Expected: _pixel_at(before, compositor.width, OVERLAP_X, OVERLAP_Y) equals `COLOR_B`
- Mark damage on the LOWER window only (repaint A with the same colour)
   - Expected: compositor.skipped_frame_count equals `skipped_before`
- The overlap pixel still belongs to B: a lower-window redraw cannot reorder z-order
   - Expected: _pixel_at(after, compositor.width, OVERLAP_X, OVERLAP_Y) equals `COLOR_B`
- A subsequent no-op frame IS skipped, proving the prior frame really presented
   - Expected: compositor.skipped_frame_count equals `skipped_after_damage + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("z-order is stable across a damage-only redraw")
step("Create two overlapping windows and confirm B (top) owns the overlap")
var compositor = _zorder_compositor()
val win_a_id = compositor.windows[0].id
compositor.render_frame()
val before = compositor.pure_simple_pixel_buffer()
expect(_pixel_at(before, compositor.width, OVERLAP_X, OVERLAP_Y)).to_equal(COLOR_B)
val skipped_before = compositor.skipped_frame_count

step("Mark damage on the LOWER window only (repaint A with the same colour)")
_fill_window(compositor, win_a_id, 300, 300, COLOR_A, 2)
compositor.render_frame()
expect(compositor.skipped_frame_count).to_equal(skipped_before)

step("The overlap pixel still belongs to B: a lower-window redraw cannot reorder z-order")
val after = compositor.pure_simple_pixel_buffer()
expect(_pixel_at(after, compositor.width, OVERLAP_X, OVERLAP_Y)).to_equal(COLOR_B)

step("A subsequent no-op frame IS skipped, proving the prior frame really presented")
val skipped_after_damage = compositor.skipped_frame_count
compositor.render_frame()
expect(compositor.skipped_frame_count).to_equal(skipped_after_damage + 1)
print "wm_zorder_damage_stable overlap_after={_pixel_at(after, compositor.width, OVERLAP_X, OVERLAP_Y)} skipped={compositor.skipped_frame_count}"
```

</details>


</details>

<details>
<summary>Advanced: closing the focused window passes focus to the next in z-order</summary>

#### closing the focused window passes focus to the next in z-order _(slow)_

- closing the focused window passes focus to the next in z-order
- Create A, B, then a third window C on top of both
   - Expected: _focused_by_id(compositor, win_c_id) is true
   - Expected: _focused_by_id(compositor, win_b_id) is false
- Close C, the focused window
   - Expected: compositor.windows.len() equals `2`
- Focus passes to B, the next window in z-order -- not to A
   - Expected: _focused_by_id(compositor, win_b_id) is true
   - Expected: _focused_by_id(compositor, win_a_id) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("closing the focused window passes focus to the next in z-order")
step("Create A, B, then a third window C on top of both")
var compositor = _zorder_compositor()
val win_a_id = compositor.windows[0].id
val win_b_id = compositor.windows[1].id
compositor.apply_bridge_request(
    3, 10, COMP_CREATE_WINDOW.to_i64(), 0, "Window C",
    300, 300, 200, 200, "", 99, "wm.zorder.c"
)
val win_c_id = compositor.windows[2].id
expect(_focused_by_id(compositor, win_c_id)).to_equal(true)
expect(_focused_by_id(compositor, win_b_id)).to_equal(false)

step("Close C, the focused window")
compositor.destroy_window(win_c_id)
expect(compositor.windows.len()).to_equal(2)

step("Focus passes to B, the next window in z-order -- not to A")
expect(_focused_by_id(compositor, win_b_id)).to_equal(true)
expect(_focused_by_id(compositor, win_a_id)).to_equal(false)
print "wm_zorder_close_refocus b_focused={_focused_by_id(compositor, win_b_id)} a_focused={_focused_by_id(compositor, win_a_id)}"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WM-SYS-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3d92ac354fb6dff4694e20f510d15297920c71bd7b2462131c5a0453e09044a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3d92ac354fb6dff4694e20f510d15297920c71bd7b2462131c5a0453e09044a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3d92ac354fb6dff4694e20f510d15297920c71bd7b2462131c5a0453e09044a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/wm/wm_focus_zorder_system_spec.spl
mirror: doc/06_spec/03_system/wm/wm_focus_zorder_system_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/wm/wm_focus_zorder_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/wm/wm_focus_zorder_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/wm/wm_focus_zorder_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/wm/wm_focus_zorder_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/wm/wm_focus_zorder_system_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clicking a background window raises and focuses it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_focus_zorder_system_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'focused window receives keyboard events, unfocused does not' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_focus_zorder_system_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'z-order is stable across a damage-only redraw' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
