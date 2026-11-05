# browser_engine: CSS `contain: size` parses but is never consulted by the sizing pass

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Found:** 2026-08-08 (U3.6 `web_css_visibility_containment_spec.spl`,
`doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`)
**Area:** `src/lib/gc_async_mut/gpu/browser_engine/containment.spl`,
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`

## Symptom

`test/03_system/gui/web_css/web_css_visibility_containment_spec.spl`,
`it "contain: size sizes the box independent of content"`, is RED by design:

```
expected 40 to equal 5
```

Repro HTML:

```html
<div id="s" style="display:block;width:20px;contain:size;
                    contain-intrinsic-size:20px 5px">
  <div id="inner" style="display:block;width:10px;height:40px"></div>
</div>
```

Per CSS `contain: size` + `contain-intrinsic-size: 20px 5px`, `#s`'s own box
height must be `5px` regardless of its child's content height — the whole
point of `contain: size` is that the box's size does not depend on its
contents. The renderer instead sizes `#s` to its child's content height
(`40px`): `contain: size` is accepted as a token by
`containment.spl`'s attribute parsing but the sizing pass in
`simple_web_html_layout_renderer_layout.spl`'s `layout()` never consults it
(and `contain-intrinsic-size` is not read at all).

## Assessment

This is a known, deliberately-scoped gap, not a regression. The header
comment in `containment.spl` (lines 1-11, present since the 2026-08-06
containment landing) states explicitly:

> `contain: size` is explicitly OUT of scope — it requires intrinsic-sizing
> machinery (a box's size must not depend on its contents, which needs a
> separate "measure without laying out" pass) that this codebase's layout
> engine (`simple_web_html_layout_renderer_layout.spl`'s array/index-based
> `layout()`) does not have; faking it would silently produce wrong sizes
> instead of skipping work, which is worse than not implementing it.

`contain: layout`, `contain: paint`, and `contain: style` are implemented and
covered (unit specs `containment_layout_contain_wired_spec.spl`,
`containment_paint_contain_wired_spec.spl`, `containment_contain_spec.spl`;
system coverage added in the same change as this bug doc, U3.6). `contain:
size` remains unimplemented.

## Unblock condition

Add a "measure without laying out" pass (or a documented approximation) to
`simple_web_html_layout_renderer_layout.spl`'s `layout()` so a `contain:
size` box can be sized from `contain-intrinsic-size` (or its own explicit
width/height) independent of a full content measurement pass, then flip the
spec assertion from documenting the gap to asserting the real value.

## Minimal repro

```
bin/simple test test/03_system/gui/web_css/web_css_visibility_containment_spec.spl --no-session-daemon --sequential
```

## Affected specs

- `test/03_system/gui/web_css/web_css_visibility_containment_spec.spl`
  (`it "contain: size sizes the box independent of content"`, RED by design)

## Evidence — fixed 2026-11-05 (branch work/libbug-std-csscontain-20261105)

Root cause: a stylesheet-declared `contain: size` never reaches the layout
engine's attribute-text reads (`attrs_raw` only holds raw HTML tag text), and
the sizing pass in `layout_with_style` had no other channel for it — so an
auto-height block with `contain: size` was always sized by its laid-out
contents. `contain-intrinsic-size` was parsed by nothing at all.

Fix: the `contain` declaration (token `size`, or `strict`) and
`contain-intrinsic-size` are now parsed into new `Style` fields
(`contain_size`, `contain_intrinsic_w_px`, `contain_intrinsic_h_px`) in
`simple_web_html_layout_renderer_decl_apply.spl`, and the block-path height
finalisation in `simple_web_html_layout_renderer_layout_engine.spl` sizes a
`contain: size` box from `contain-intrinsic-size` (content-box, like an
explicit height) — or padding+border only when no intrinsic size is given —
whenever no explicit height wins. Explicit height still wins; min/max-height
clamps still apply; following siblings advance by the content-independent
height. Children are still laid out (their own paint/clip is unaffected).
The used-value clones (`style_with_height` / `style_with_width` /
`tag_defaults`) preserve the new fields.

TDD evidence (seed binary
`/home/yoon/dev/simple/build/phase_snapshots/phase1_1793422538/simple`,
`--mode=interpreter`, cwd = worktree root):

- RED — new unit spec
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/containment_size_contain_wired_spec.spl`
  (4 cases): 1 passed, 3 failed —
  `expected 40 to equal 5` (intrinsic size ignored),
  `expected 42 to equal 2` (padding-only collapse ignored),
  `expected 50 to equal 15` (sibling advance used content height).
- RED — existing system spec
  `test/03_system/gui/web_css/web_css_visibility_containment_spec.spl`:
  6 passed, 1 failed (`expected 40 to equal 5`).
- GREEN — after the fix: unit spec 4/4; system spec 7/7.
- Regression sweep, all GREEN: containment_{coverage_closure,
  layout_contain_wired,paint_contain_wired} specs;
  web_css_{box_model,flex,grid,text_layout,background_border,
  visibility_containment} specs. Pre-existing failures (unchanged with the
  fix stashed, verified via `git stash` re-run):
  containment_contain_spec.spl (2/3), web_css_positioning_spec.spl (4/6),
  web_css_table_replaced_forms_spec.spl (5/6).
