# wm_window_lifecycle_system_spec

> As a WM developer I need proof that a window's full lifecycle — create,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_window_lifecycle_system_spec

As a WM developer I need proof that a window's full lifecycle — create,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/wm/wm_window_lifecycle_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a WM developer I need proof that a window's full lifecycle — create,
move, resize, close — actually changes the composited desktop, not just
that the compositor's method calls return without raising. Every example
below fills a window with a pinned probe colour and reads that colour back
out of the real composited pixel buffer (`pure_simple_pixel_buffer()`), so a
compositor that silently drops a window's content, forgets to mark damage,
or keeps presenting stale pixels after a window closes cannot pass by
declaration.

## Scenarios

### WM window lifecycle

<details>
<summary>Advanced: creates a window and the frame gains its pixels</summary>

#### creates a window and the frame gains its pixels _(slow)_

- creates a window and the frame gains its pixels
- Create a 640x600 headless compositor with a pinned-colour window
- Present the frame and probe the composited desktop


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a window and the frame gains its pixels")
step("Create a 640x600 headless compositor with a pinned-colour window")
var compositor = _lifecycle_compositor(640, 600, 208, 196, PROBE_COLOR)

step("Present the frame and probe the composited desktop")
compositor.render_frame()
val desktop = compositor.pure_simple_pixel_buffer()
val probe_count = _count_color(desktop, PROBE_COLOR)
val distinct = _distinct_colors(desktop)
expect(probe_count).to_be_greater_than(0)
expect(distinct).to_be_greater_than(2)
print "wm_lifecycle_create probe_px={probe_count} distinct={distinct}"
```

</details>


</details>

<details>
<summary>Advanced: moves a window and damage follows it</summary>

#### moves a window and damage follows it _(slow)_

- moves a window and damage follows it
- Create and present the initial frame
- Drag the titlebar +100,+50
   - Expected: compositor.windows[0].x equals `win.x + 100`
   - Expected: compositor.windows[0].y equals `win.y + 50`
- Present the moved frame and confirm damage followed the window
   - Expected: compositor.skipped_frame_count equals `before_skipped`
   - Expected: old_only_before equals `PROBE_COLOR`
   - Expected: new_only_after equals `PROBE_COLOR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("moves a window and damage follows it")
step("Create and present the initial frame")
var compositor = _lifecycle_compositor(640, 600, 208, 196, PROBE_COLOR)
compositor.render_frame()
val before = compositor.pure_simple_pixel_buffer()
val before_checksum = _checksum(before)
val before_skipped = compositor.skipped_frame_count
val win = compositor.windows[0]

step("Drag the titlebar +100,+50")
compositor.handle_mouse_move(win.x + 10, win.y + 10)
compositor.handle_left_button(true)
expect(compositor.dragging).to_be(true)
compositor.handle_mouse_move(win.x + 110, win.y + 60)
compositor.handle_left_button(false)
expect(compositor.windows[0].x).to_equal(win.x + 100)
expect(compositor.windows[0].y).to_equal(win.y + 50)

step("Present the moved frame and confirm damage followed the window")
compositor.render_frame()
expect(compositor.skipped_frame_count).to_equal(before_skipped)
val after = compositor.pure_simple_pixel_buffer()
val after_checksum = _checksum(after)
assert_true(after_checksum != before_checksum)
# The 208x196 window only moves +100,+50, so its old and new rects
# overlap; a whole-rect colour count can't tell "vacated" from
# "still covered". Probe two single points chosen to sit inside
# exactly one rect's content area (content offset is x+4,y+32 per
# `shared_wm_scene_window_content_rect_with_titlebar`): a point deep
# in the OLD window's top-left corner that the move leaves fully
# outside the new rect, and a point deep in the NEW window's
# bottom-right corner that was outside the old rect.
val old_only_x = win.x + 6
val old_only_y = win.y + 34
val new_only_x = win.x + win.w + 2
val new_only_y = win.y + win.h + 4
val old_only_before = _pixel_at(before, compositor.width, old_only_x, old_only_y)
val new_only_before = _pixel_at(before, compositor.width, new_only_x, new_only_y)
val old_only_after = _pixel_at(after, compositor.width, old_only_x, old_only_y)
val new_only_after = _pixel_at(after, compositor.width, new_only_x, new_only_y)
expect(old_only_before).to_equal(PROBE_COLOR)
assert_true(new_only_before != PROBE_COLOR)
assert_true(old_only_after != PROBE_COLOR)
expect(new_only_after).to_equal(PROBE_COLOR)
print "wm_lifecycle_move before={before_checksum} after={after_checksum} old_only_before={old_only_before} old_only_after={old_only_after} new_only_before={new_only_before} new_only_after={new_only_after}"
```

</details>


</details>

<details>
<summary>Advanced: resizes a window and content re-lays-out</summary>

#### resizes a window and content re-lays-out _(slow)_

- resizes a window and content re-lays-out
- Create and present the initial frame
- Resize to 300x200 and re-lay-out its content to match
   - Expected: after_count equals `new_content_w * new_content_h`
- Shrink to the 1x1 minimum without crashing
   - Expected: compositor.windows[0].w equals `1`
   - Expected: compositor.windows[0].h equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resizes a window and content re-lays-out")
step("Create and present the initial frame")
var compositor = _lifecycle_compositor(640, 600, 208, 196, PROBE_COLOR)
compositor.render_frame()
val window_id = compositor.windows[0].id
val before = compositor.pure_simple_pixel_buffer()
val before_count = _count_color(before, PROBE_COLOR)
expect(before_count).to_be_greater_than(0)

step("Resize to 300x200 and re-lay-out its content to match")
compositor.apply_wm_action(wm_resize_action(window_id, 300, 200))
val new_content_w = compositor.windows[0].w - 8
val new_content_h = compositor.windows[0].h - 36
expect(compositor.require_external_web_frame(window_id)).to_be(true)
val new_pixels = _solid(new_content_w, new_content_h, PROBE_COLOR)
val new_frame = pixel_surface_content_frame(
    "{window_id}", "", 0, 0, new_content_w, new_content_h,
    new_pixels, 2, 2
)
expect(compositor.set_external_web_frame(window_id, new_frame)).to_be(true)
compositor.render_frame()
val after = compositor.pure_simple_pixel_buffer()
val after_count = _count_color(after, PROBE_COLOR)
expect(after_count).to_equal(new_content_w * new_content_h)
assert_true(after_count != before_count)
print "wm_lifecycle_resize before={before_count} after={after_count} area={new_content_w * new_content_h}"

step("Shrink to the 1x1 minimum without crashing")
compositor.apply_wm_action(wm_resize_action(window_id, 1, 1))
compositor.render_frame()
expect(compositor.windows[0].w).to_equal(1)
expect(compositor.windows[0].h).to_equal(1)
print "wm_lifecycle_resize_min w={compositor.windows[0].w} h={compositor.windows[0].h}"
```

</details>


</details>

<details>
<summary>Advanced: closes a window and its pixels disappear</summary>

#### closes a window and its pixels disappear _(slow)_

- closes a window and its pixels disappear
- Create and present the initial frame
- Close the window and present again
   - Expected: compositor.windows.len() equals `0`
   - Expected: after_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("closes a window and its pixels disappear")
step("Create and present the initial frame")
var compositor = _lifecycle_compositor(640, 600, 208, 196, PROBE_COLOR)
compositor.render_frame()
val before = compositor.pure_simple_pixel_buffer()
val before_checksum = _checksum(before)
val before_count = _count_color(before, PROBE_COLOR)
expect(before_count).to_be_greater_than(0)
val window_id = compositor.windows[0].id

step("Close the window and present again")
compositor.destroy_window(window_id)
expect(compositor.windows.len()).to_equal(0)
compositor.render_frame()
val after = compositor.pure_simple_pixel_buffer()
val after_count = _count_color(after, PROBE_COLOR)
expect(after_count).to_equal(0)
assert_true(_checksum(after) != before_checksum)
print "wm_lifecycle_close before={before_count} after={after_count}"
```

</details>


</details>

<details>
<summary>Advanced: a no-op frame after close skips presentation</summary>

#### a no-op frame after close skips presentation _(slow)_

- a no-op frame after close skips presentation
- Create, present, then close the window
   - Expected: compositor.skipped_frame_count equals `skipped_pre_close_render`
- Present twice more with no state change
   - Expected: compositor.skipped_frame_count equals `skipped_before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a no-op frame after close skips presentation")
step("Create, present, then close the window")
var compositor = _lifecycle_compositor(640, 600, 208, 196, PROBE_COLOR)
compositor.render_frame()
val window_id = compositor.windows[0].id
compositor.destroy_window(window_id)
val skipped_pre_close_render = compositor.skipped_frame_count
compositor.render_frame()
# Both directions (plan section 3.6): the close itself carries real
# damage, so this render must PRESENT, not skip -- a compositor that
# skips unconditionally would satisfy the no-op assertion below by
# accident.
expect(compositor.skipped_frame_count).to_equal(skipped_pre_close_render)

step("Present twice more with no state change")
val skipped_before = compositor.skipped_frame_count
compositor.render_frame()
expect(compositor.skipped_frame_count).to_equal(skipped_before + 1)
print "wm_lifecycle_noop skipped={compositor.skipped_frame_count}"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WM-SYS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `248d2b524fb055d02c9bf608d96ff9a0c54ad3e4bbd48fb03c96b99b4ef100e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `248d2b524fb055d02c9bf608d96ff9a0c54ad3e4bbd48fb03c96b99b4ef100e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `248d2b524fb055d02c9bf608d96ff9a0c54ad3e4bbd48fb03c96b99b4ef100e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/wm/wm_window_lifecycle_system_spec.spl
mirror: doc/06_spec/03_system/wm/wm_window_lifecycle_system_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/wm/wm_window_lifecycle_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/wm/wm_window_lifecycle_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/wm/wm_window_lifecycle_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/wm/wm_window_lifecycle_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/wm/wm_window_lifecycle_system_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a window and the frame gains its pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_window_lifecycle_system_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'moves a window and damage follows it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_window_lifecycle_system_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resizes a window and content re-lays-out' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
