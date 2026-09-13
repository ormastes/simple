# browser_engine: `position: fixed` resolves against the nearest DOM ancestor, not the viewport

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Found:** 2026-08-08 (U3.7 `web_css_positioning_spec.spl`, REQ-WEB-CSS-007,
`doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`)
**Area:** `src/lib/gc_async_mut/gpu/browser_engine/**`

## Symptom

`test/03_system/gui/web_css/web_css_positioning_spec.spl`, `it "position:
fixed anchors to the viewport"` (file:line: see that `it` block) fails:

```
expected 22 to equal 2
```

Fixture: a 20px-margined, non-positioned `#wrap` contains `#fx{position:fixed;
left:1px;top:2px;...}`. Real CSS resolves a `position: fixed` box's
`left`/`top` against the viewport's origin (0,0), independent of any
ancestor's offset. This renderer instead resolves it against `#wrap`'s own
box origin (20,20) + (1,2) = (21,22) — i.e. exactly like `position: absolute`
against the nearest ancestor, ignoring the viewport-anchoring rule that makes
`fixed` different from `absolute`.

## Root cause

`Style.position_fixed` parses correctly
(`simple_web_html_layout_renderer_decl_apply.spl:800`, driven by
`style_property_id.spl:158`) and carries through `Style` copies
(`simple_web_html_layout_renderer_layout.spl:431`/`:453`), but the only place
that ever *reads* `position_fixed` back is a debug `getComputedStyle`-style
text accessor
(`simple_web_html_layout_renderer_core.spl:3028`, returns the string
`"fixed"`). No layout pass branches on `position_fixed` to establish the
viewport as the containing block — the containing-block/offset-resolution
code path only checks `position_absolute`
(`simple_web_html_layout_renderer_layout.spl:1862,1954,2072,2144,2163,2371,2422,2524`),
so a fixed box silently falls through the absolute-positioning path anchored
to its nearest DOM ancestor's box instead of the viewport.

## Fix sketch

Wherever the layout pass resolves an absolutely-positioned box's containing
block (the `position_absolute` branches cited above), add a parallel
`position_fixed` branch that anchors the box's containing block to the
viewport rect (`(0, 0, width, height)`) unconditionally, rather than walking
up to the nearest positioned ancestor.

## Affected specs

- `test/03_system/gui/web_css/web_css_positioning_spec.spl` — `it "position:
  fixed anchors to the viewport"` (RED-by-design, left RED per project
  testing rules; do not weaken the assertion to hide this gap).

## Triage 2026-09-12
Rule B: re-ran `bin/simple test test/03_system/gui/web_css/web_css_positioning_spec.spl` on the deployed seed; it still FAILs, matching the recorded defect. Status word left as-is. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Triage 2026-09-13 (BUGFIX-12 shard 22) — refined diagnosis, fix deferred

Re-ran the spec (`bin/simple test
test/03_system/gui/web_css/web_css_positioning_spec.spl`): still RED, same
`expected 22 to equal 2` on `it "position: fixed anchors to the viewport"`
(6 examples, 3 failures — the other 2 failures, `clear`/`float`, are the
pre-existing unrelated RED-by-design cases documented in that spec's own
header, unaffected here).

Confirmed the root cause with `simple_web_layout_debug_layout_by_id` on the
exact fixture: the LAYOUT box for `#fx` is `(bx=21, by=22)` — exactly
`(#wrap.bx=20, #wrap.by=20) + (left_px=1, top_px=2)`, matching this doc's
root-cause arithmetic precisely. **New finding not in the original diagnosis:**
the DrawIR command the spec actually asserts on does NOT read `bx`/`by`
directly for `x` — `fx.x` from `_draw_ir_command_by_id` is `1` (already
viewport-correct) while `fx.y` is `22` (still ancestor-anchored), even though
the underlying layout box has `bx=21`. So there is an X-axis-only paint-time
transform somewhere between layout and DrawIR-command emission that already
corrects for the ancestor offset on X but not on Y — grepped
`simple_web_html_layout_renderer_core.spl`,
`simple_web_html_layout_renderer_paint_layout.spl`,
`simple_web_html_layout_renderer_paint_primitives.spl`, and
`web_paint_chunk_frame.spl` for the actual `DrawIrCommand{...}`/command-x
construction site and could not locate it within this shard's budget (no
literal `DrawIrCommand(` constructor call in any of those files — it is built
through an indirection not yet identified).

This matters because the fix sketch in this doc (add a `position_fixed`
branch to `absolute_child_x`/`absolute_child_y` anchoring to the viewport)
would change `bx` from 21 to 1 — which, if the unidentified X-axis paint
transform ALSO still fires and subtracts the ancestor offset again, would
turn the now-correct `fx.x` DrawIR value into a wrong negative number
(regression on a currently-passing assertion). Implementing the layout-level
fix blind, without first locating and understanding that transform, risks
exactly the kind of regression `.claude/rules/testing.md` warns against.
Deferring the code fix; leaving OPEN with this refined root-cause note so the
next owner does not have to re-discover the X/Y asymmetry from scratch.

## Correction 2026-09-13 (BUGFIX-12 shard 22)

The X/Y-asymmetry claim in the previous triage note above is **wrong** —
retracting it. It rested on assuming `expect(fx.x).to_equal(1)` aborted the
`it` block on failure so that only the y-failure printed. Checked
`fail_assertion` in `src/lib/nogc_sync_mut/spec.spl:1075` — it only pushes
onto `current_test_errors`, it does not abort; a throwaway probe spec
(`expect(1).to_equal(2); expect(3).to_equal(4)`) confirms the reporter prints
only the LAST accumulated failure, not the first. So "only one failure line
printed" proves nothing about whether the x assertion passed.

Re-checked directly by calling `simple_web_layout_render_html_draw_ir` (the
same function the spec uses) on the identical fixture and printing
`fx.x`/`fx.y` from the actual `DrawIrCommand`: **`fx.x=21`, `fx.y=22`** — BOTH
axes are ancestor-anchored, matching the layout box exactly (no separate
paint-time transform exists; `DrawIrCommand.x`/`.y` mirror `bx`/`by`
directly). The doc's original root-cause and fix sketch are correct and
unchallenged; there is no X/Y asymmetry to explain.

**Why the fix is still deferred rather than landed:** `absolute_child_x`/
`absolute_child_y` need a **viewport width** to anchor a fixed box's `left`/
`right` against, but `layout`/`layout_with_style`
(`simple_web_html_layout_renderer_layout.spl:1399,1558`) only thread
`viewport_h` — the `w` parameter is the CURRENT container's shrinking inner
width, not the original viewport width, at every one of the four
`position_absolute` dispatch sites (lines ~2338/2579/2838/2940) where a
`position_fixed` branch would need to go. Adding a `viewport_w` parameter
means widening both functions' signatures and every recursive call site in
this 3300-line file (mirroring how `viewport_h` was already threaded) — a
real, mechanical but wide-blast-radius signature change, not a local
one-branch fix, and past a shard's budget to do safely with the current host
running 300-900s per test invocation. Leaving OPEN with this corrected,
complete diagnosis; the next owner can implement the sketch directly once
`viewport_w` threading is done.
