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
