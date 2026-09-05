# wm_damage_present_skip_system_spec

> As a WM developer I need proof that the compositor's damage/present-skip

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_damage_present_skip_system_spec

As a WM developer I need proof that the compositor's damage/present-skip

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/wm/wm_damage_present_skip_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a WM developer I need proof that the compositor's damage/present-skip
mechanics (`host_compositor_core.spl:1698-1713`) actually gate presentation
on real accumulated damage, not just that `render_frame()` returns without
raising. Every example below reads the real composited pixel buffer
(`pure_simple_pixel_buffer()`) and the compositor's own
`skipped_frame_count` bookkeeping, so an implementation that always
presents, always skips, or lets damage in one window bleed a redundant
redraw into another window's untouched pixels cannot pass by declaration.

## Scenarios

### WM damage present skip

<details>
<summary>Advanced: a frame with reported damage presents and clears had_damage</summary>

#### a frame with reported damage presents and clears had_damage _(slow)_

- a frame with reported damage presents and clears had_damage
- Create a compositor with one pinned-colour window (creation itself is damage)
- Present the damaged frame
- The frame presented: pixels are visible and the skip counter did not move
   - Expected: compositor.skipped_frame_count equals `skipped_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a frame with reported damage presents and clears had_damage")
step("Create a compositor with one pinned-colour window (creation itself is damage)")
var compositor = _single_window_compositor(640, 600, 208, 196)
val skipped_before = compositor.skipped_frame_count

step("Present the damaged frame")
compositor.render_frame()
val desktop = compositor.pure_simple_pixel_buffer()
val probe_count = _count_color(desktop, PROBE_COLOR_A)

step("The frame presented: pixels are visible and the skip counter did not move")
expect(probe_count).to_be_greater_than(0)
expect(compositor.skipped_frame_count).to_equal(skipped_before)
print "wm_damage_present probe_px={probe_count} skipped={compositor.skipped_frame_count}"
```

</details>


</details>

<details>
<summary>Advanced: a frame with no damage is skipped and skipped_frame_count increments</summary>

#### a frame with no damage is skipped and skipped_frame_count increments _(slow)_

- a frame with no damage is skipped and skipped_frame_count increments
- Create and present the initial (damaged) frame
- Present again with no state change
- The no-op frame was skipped: the counter incremented by exactly one
   - Expected: compositor.skipped_frame_count equals `skipped_before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a frame with no damage is skipped and skipped_frame_count increments")
step("Create and present the initial (damaged) frame")
var compositor = _single_window_compositor(640, 600, 208, 196)
compositor.render_frame()
val skipped_before = compositor.skipped_frame_count

step("Present again with no state change")
compositor.render_frame()

step("The no-op frame was skipped: the counter incremented by exactly one")
expect(compositor.skipped_frame_count).to_equal(skipped_before + 1)
print "wm_damage_noop_skip skipped={compositor.skipped_frame_count}"
```

</details>


</details>

<details>
<summary>Advanced: damage in one window does not force redraw pixels of another</summary>

#### damage in one window does not force redraw pixels of another _(slow)_

- damage in one window does not force redraw pixels of another
- Create two non-overlapping windows and present the initial frame
- Move window A only, damaging just its rect
- Window B's content-rect pixels are byte-identical across the present
   - Expected: after_b_checksum equals `before_b_checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("damage in one window does not force redraw pixels of another")
step("Create two non-overlapping windows and present the initial frame")
var compositor = _two_window_compositor(640, 600, 208, 196)
compositor.render_frame()
val win_b = compositor.windows[1]
val before = compositor.pure_simple_pixel_buffer()
val before_b_checksum = _content_checksum(before, compositor.width, win_b.x, win_b.y, win_b.w, win_b.h)

step("Move window A only, damaging just its rect")
val win_a = compositor.windows[0]
compositor.apply_wm_action(wm_move_action(win_a.id, win_a.x + 40, win_a.y + 20))
compositor.render_frame()

step("Window B's content-rect pixels are byte-identical across the present")
val after = compositor.pure_simple_pixel_buffer()
val after_b_checksum = _content_checksum(after, compositor.width, win_b.x, win_b.y, win_b.w, win_b.h)
expect(after_b_checksum).to_equal(before_b_checksum)
# Sanity: A's own move really did change the desktop, otherwise this
# example would pass vacuously because nothing moved at all.
val before_a_checksum = _content_checksum(before, compositor.width, win_a.x, win_a.y, win_a.w, win_a.h)
val after_a_checksum = _content_checksum(after, compositor.width, win_a.x, win_a.y, win_a.w, win_a.h)
assert_true(before_a_checksum != after_a_checksum)
print "wm_damage_isolated b_before={before_b_checksum} b_after={after_b_checksum} a_before={before_a_checksum} a_after={after_a_checksum}"
```

</details>


</details>

<details>
<summary>Advanced: skipped_frame_count stops incrementing once damage arrives</summary>

#### skipped_frame_count stops incrementing once damage arrives _(slow)_

- skipped_frame_count stops incrementing once damage arrives
- Create and present the initial (damaged) frame
- Present twice more with no state change: the counter climbs by two
- Move the window, then present: damage arrived, so the counter must not move
   - Expected: compositor.skipped_frame_count equals `skipped_after_noops`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skipped_frame_count stops incrementing once damage arrives")
step("Create and present the initial (damaged) frame")
var compositor = _single_window_compositor(640, 600, 208, 196)
compositor.render_frame()

step("Present twice more with no state change: the counter climbs by two")
compositor.render_frame()
compositor.render_frame()
val skipped_after_noops = compositor.skipped_frame_count
expect(skipped_after_noops).to_be_greater_than(0)

step("Move the window, then present: damage arrived, so the counter must not move")
val win = compositor.windows[0]
compositor.apply_wm_action(wm_move_action(win.id, win.x + 30, win.y + 15))
compositor.render_frame()
expect(compositor.skipped_frame_count).to_equal(skipped_after_noops)
print "wm_damage_stops_skipping skipped={compositor.skipped_frame_count}"
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
- `REQ-WM-SYS-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `769eb04da138b854413b02bf55defcf370233f1116e12c2d9a8800890656b902`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `769eb04da138b854413b02bf55defcf370233f1116e12c2d9a8800890656b902`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `769eb04da138b854413b02bf55defcf370233f1116e12c2d9a8800890656b902`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/wm/wm_damage_present_skip_system_spec.spl
mirror: doc/06_spec/03_system/wm/wm_damage_present_skip_system_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/wm/wm_damage_present_skip_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/wm/wm_damage_present_skip_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/wm/wm_damage_present_skip_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/wm/wm_damage_present_skip_system_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a frame with reported damage presents and clears had_damage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_damage_present_skip_system_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a frame with no damage is skipped and skipped_frame_count increments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/wm/wm_damage_present_skip_system_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'damage in one window does not force redraw pixels of another' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
