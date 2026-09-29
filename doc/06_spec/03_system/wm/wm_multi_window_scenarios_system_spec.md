# wm_multi_window_scenarios_system_spec

> As a WM developer I need proof that the compositor holds up under *multiple*

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_multi_window_scenarios_system_spec

As a WM developer I need proof that the compositor holds up under *multiple*

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/wm/wm_multi_window_scenarios_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a WM developer I need proof that the compositor holds up under *multiple*
windows and *bursts* of window operations, not just the single-window
lifecycle covered by `wm_window_lifecycle_system_spec.spl`. Every example
below drives a real headless `HostCompositor` with several pinned-colour
windows at once -- an eight-window tile, a rapid 20-window create/close
burst, a three-window overlap chain, and a ten-resize storm -- and reads the
result back out of the real composited pixel buffer
(`pure_simple_pixel_buffer()`) and the compositor's own damage bookkeeping
(`skipped_frame_count`), never against "the calls didn't crash".

## Scenarios

### WM multi-window scenarios

<details>
<summary>Advanced: eight windows tile without pixel bleed between content rects</summary>

#### eight windows tile without pixel bleed between content rects _(slow)_

- eight windows tile without pixel bleed between content rects
- Create a 4x2 grid of 8 non-overlapping, distinctly-coloured windows
- Present and probe every window's content area for its own colour only
   - Expected: n equals `content_area`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("eight windows tile without pixel bleed between content rects")
step("Create a 4x2 grid of 8 non-overlapping, distinctly-coloured windows")
# Desktop chrome always paints a top command lane (~46px, drawn
# before window content so windows overpaint it) and a taskbar dock
# near the bottom (painted AFTER window content, so anything under
# it would be overpainted). The grid below starts at y=60 (clear of
# the top lane) and its second row bottom edge (380) sits far above
# a 900-tall desktop's taskbar band (starts at height-56=844), so no
# window's pinned content is ever legitimately overpainted by chrome.
var compositor = HostCompositor.new_headless(Size.wh(900, 900))
val colors: [u32] = [
    0xFFE6194Bu32, 0xFF3CB44Bu32, 0xFFFFE119u32, 0xFF4363D8u32,
    0xFFF58231u32, 0xFF911EB4u32, 0xFF46F0F0u32, 0xFFF032E6u32
]
val cols = 4
val win_w = 180
val win_h = 150
val gap = 20
val top_clear = 60
var i = 0
while i < 8:
    val col = i % cols
    val row = i / cols
    val x = col * (win_w + gap)
    val y = top_clear + row * (win_h + gap)
    val window_id = _create_window(
        compositor, (i + 1) as i64, "Tile {i}", x, y, win_w, win_h, "wm.tile.{i}"
    )
    _fill_window(compositor, window_id, win_w, win_h, colors[i], 1)
    i = i + 1

step("Present and probe every window's content area for its own colour only")
compositor.render_frame()
val desktop = compositor.pure_simple_pixel_buffer()
val content_w = win_w - 8
val content_h = win_h - 36
val content_area = content_w * content_h
var j = 0
while j < 8:
    val n = _count_color(desktop, colors[j])
    expect(n).to_equal(content_area)
    j = j + 1
print "wm_multi_tile content_area={content_area} windows=8"
```

</details>


</details>

<details>
<summary>Advanced: rapid create/close of 20 windows leaves a clean desktop</summary>

#### rapid create/close of 20 windows leaves a clean desktop _(slow)_

- rapid create/close of 20 windows leaves a clean desktop
- Present an empty desktop and record its baseline pixels
- Create and immediately close 20 windows without presenting between them
   - Expected: compositor.windows.len() equals `0`
- Present once: the burst carried real damage, so this frame must present
   - Expected: compositor.skipped_frame_count equals `before_skipped`
   - Expected: _checksum(after) equals `baseline_checksum`
   - Expected: _distinct_colors(after) equals `baseline_distinct`
- A further no-op present now correctly skips
   - Expected: compositor.skipped_frame_count equals `skipped_before_noop + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rapid create/close of 20 windows leaves a clean desktop")
step("Present an empty desktop and record its baseline pixels")
var compositor = HostCompositor.new_headless(Size.wh(640, 480))
compositor.render_frame()
val baseline = compositor.pure_simple_pixel_buffer()
val baseline_checksum = _checksum(baseline)
val baseline_distinct = _distinct_colors(baseline)
val before_skipped = compositor.skipped_frame_count

step("Create and immediately close 20 windows without presenting between them")
var k = 0
while k < 20:
    val window_id = _create_window(
        compositor, (k + 1) as i64, "Burst {k}", 40, 40, 160, 140, "wm.burst.{k}"
    )
    _fill_window(compositor, window_id, 160, 140, 0xFF00FF00u32, 1)
    compositor.destroy_window(window_id)
    k = k + 1
expect(compositor.windows.len()).to_equal(0)

step("Present once: the burst carried real damage, so this frame must present")
compositor.render_frame()
expect(compositor.skipped_frame_count).to_equal(before_skipped)
val after = compositor.pure_simple_pixel_buffer()
expect(_checksum(after)).to_equal(baseline_checksum)
expect(_distinct_colors(after)).to_equal(baseline_distinct)

step("A further no-op present now correctly skips")
val skipped_before_noop = compositor.skipped_frame_count
compositor.render_frame()
expect(compositor.skipped_frame_count).to_equal(skipped_before_noop + 1)
print "wm_multi_burst windows={compositor.windows.len()} baseline_distinct={baseline_distinct} after_distinct={_distinct_colors(after)}"
```

</details>


</details>

<details>
<summary>Advanced: overlap chains render in creation order then in raise order</summary>

#### overlap chains render in creation order then in raise order _(slow)_

- overlap chains render in creation order then in raise order
- Create three overlapping windows A, B, C in that order; C is created last
- Present: the triple-overlap point is owned by C, the last window created
   - Expected: _pixel_at(before, compositor.width, overlap_x, overlap_y) equals `color_c`
- Click a point that only A covers, below A's titlebar, to raise and focus A
- A is now on top: the triple-overlap point flips from C's colour to A's
   - Expected: after_overlap equals `color_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overlap chains render in creation order then in raise order")
step("Create three overlapping windows A, B, C in that order; C is created last")
var compositor = HostCompositor.new_headless(Size.wh(640, 600))
val color_a: u32 = 0xFFE6194Bu32
val color_b: u32 = 0xFF4363D8u32
val color_c: u32 = 0xFF3CB44Bu32
val a_id = _create_window(compositor, 1, "Chain A", 20, 20, 300, 300, "wm.chain.a")
_fill_window(compositor, a_id, 300, 300, color_a, 1)
val b_id = _create_window(compositor, 2, "Chain B", 80, 80, 300, 300, "wm.chain.b")
_fill_window(compositor, b_id, 300, 300, color_b, 1)
val c_id = _create_window(compositor, 3, "Chain C", 140, 140, 300, 300, "wm.chain.c")
_fill_window(compositor, c_id, 300, 300, color_c, 1)

step("Present: the triple-overlap point is owned by C, the last window created")
compositor.render_frame()
val overlap_x = 200
val overlap_y = 200
val before = compositor.pure_simple_pixel_buffer()
expect(_pixel_at(before, compositor.width, overlap_x, overlap_y)).to_equal(color_c)

step("Click a point that only A covers, below A's titlebar, to raise and focus A")
compositor.handle_mouse_move(40, 70)
compositor.handle_left_button(true)
compositor.handle_left_button(false)
compositor.render_frame()

step("A is now on top: the triple-overlap point flips from C's colour to A's")
val after = compositor.pure_simple_pixel_buffer()
val after_overlap = _pixel_at(after, compositor.width, overlap_x, overlap_y)
expect(after_overlap).to_equal(color_a)
assert_true(after_overlap != color_c)
print "wm_multi_chain before={_pixel_at(before, compositor.width, overlap_x, overlap_y)} after={after_overlap}"
```

</details>


</details>

<details>
<summary>Advanced: resize storms coalesce damage without dropping the final geometry</summary>

#### resize storms coalesce damage without dropping the final geometry _(slow)_

- resize storms coalesce damage without dropping the final geometry
- Create and present a single window at its initial size
- Apply 10 resizes back-to-back with no presentation between them
   - Expected: compositor.windows[0].w equals `final_w`
   - Expected: compositor.windows[0].h equals `final_h`
- Match content to the final geometry and present exactly once
- The coalesced storm still carried damage, so this frame presented, not skipped
   - Expected: compositor.skipped_frame_count equals `before_skipped`
   - Expected: final_count equals `final_content_w * final_content_h`
   - Expected: compositor.windows[0].w equals `final_w`
   - Expected: compositor.windows[0].h equals `final_h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resize storms coalesce damage without dropping the final geometry")
step("Create and present a single window at its initial size")
var compositor = HostCompositor.new_headless(Size.wh(640, 600))
val probe_color: u32 = 0xFFF58231u32
val window_id = _create_window(compositor, 1, "Resize Storm", 20, 20, 208, 196, "wm.storm")
_fill_window(compositor, window_id, 208, 196, probe_color, 1)
compositor.render_frame()
val before_skipped = compositor.skipped_frame_count

step("Apply 10 resizes back-to-back with no presentation between them")
val widths: [i32] = [220, 300, 180, 260, 150, 240, 200, 280, 170, 300]
val heights: [i32] = [200, 260, 220, 300, 180, 220, 260, 240, 190, 220]
var r = 0
while r < 10:
    compositor.apply_wm_action(wm_resize_action(window_id, widths[r], heights[r]))
    r = r + 1
val final_w = widths[9]
val final_h = heights[9]
expect(compositor.windows[0].w).to_equal(final_w)
expect(compositor.windows[0].h).to_equal(final_h)

step("Match content to the final geometry and present exactly once")
val final_content_w = final_w - 8
val final_content_h = final_h - 36
expect(compositor.require_external_web_frame(window_id)).to_be(true)
_fill_window(compositor, window_id, final_w, final_h, probe_color, 2)
compositor.render_frame()

step("The coalesced storm still carried damage, so this frame presented, not skipped")
expect(compositor.skipped_frame_count).to_equal(before_skipped)
val after = compositor.pure_simple_pixel_buffer()
val final_count = _count_color(after, probe_color)
expect(final_count).to_equal(final_content_w * final_content_h)
expect(compositor.windows[0].w).to_equal(final_w)
expect(compositor.windows[0].h).to_equal(final_h)
print "wm_multi_resize_storm final_w={final_w} final_h={final_h} final_count={final_count}"
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
- `REQ-WM-SYS-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1e1fc3ab445e7cff3fdf650321a768dd2b3af0954021cb07001d89f274017131`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e1fc3ab445e7cff3fdf650321a768dd2b3af0954021cb07001d89f274017131`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e1fc3ab445e7cff3fdf650321a768dd2b3af0954021cb07001d89f274017131`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/wm/wm_multi_window_scenarios_system_spec.spl
mirror: doc/06_spec/03_system/wm/wm_multi_window_scenarios_system_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/wm/wm_multi_window_scenarios_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/wm/wm_multi_window_scenarios_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/wm/wm_multi_window_scenarios_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/wm/wm_multi_window_scenarios_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/wm/wm_multi_window_scenarios_system_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'eight windows tile without pixel bleed between content rects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_multi_window_scenarios_system_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rapid create/close of 20 windows leaves a clean desktop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_multi_window_scenarios_system_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overlap chains render in creation order then in raise order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
