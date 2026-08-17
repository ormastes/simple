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
