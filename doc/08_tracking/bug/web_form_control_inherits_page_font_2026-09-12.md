# Form controls inherit the page font instead of the UA font (2026-09-12)

**Status:** FIXED (this change).
**Component:** pure-Simple web renderer, UA default stylesheet.
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`
(`_tag_defaults_without_metadata`, the `input` / `button` branches).

## Symptom

Every `<button>`, `<input>`, `<select>` and `<textarea>` on the shared catalog is
about 9 px too tall, and correspondingly too wide.

Chrome's UA stylesheet does NOT let form controls inherit `font` from their
ancestors: it sets `font: 400 13.3333px <system>` and `line-height: normal` on
them. Simple's `tag_defaults` set padding, display and text-align for `button`
and `input` but never touched `font_size` / `line_height_px`, so a control
inside `body { font: 16px/1.5 sans-serif }` got font-size 16 and a 24 px line
box instead of 13 px and a ~15 px one.

## Evidence

Chrome, `examples/06_io/ui/web_catalog/tab-bar.html` at 900x760, via
`--headless=new --dump-dom --virtual-time-budget=3000` with an injected
`getBoundingClientRect()` + `getComputedStyle()` walk:

```
main                 top=0.00  h=101.00           pt=24px pb=24px
nav.tabs             top=24.00 h=53.00            pt=10px pb=10px
button#tab-overview  top=34.00 h=33.00 w=73.56    fs=13.3333px lh=normal
```

Simple, same page, same size, via the layout-box dump:

```
main   y=0  h=113
nav    y=24 h=65                      <- +12
button y=34 h=42 w=80  fs=16 lh=-15   <- +9 tall, inherited 16px/1.5
```

`h = 42` decomposes exactly as `8 + 8` padding `+ 1 + 1` border `+ 24` line box;
Chrome's `33` is the same box with a 15 px line box. The inherited-font
hypothesis is fully determined by the dump: `fs=16 lh=-15` (the unitless-1.5
sentinel) is the body's `font: 16px/1.5`, reaching the control unchanged.

## Fix

Give `button` / `input` / `select` / `textarea` the UA font in
`_tag_defaults_without_metadata`: font-size 13 (Chrome's 13.3333 rounded to the
engine's integer px) and a 1.2 line-height ratio, which resolves to the 15 px
line box Chrome reports. `textarea` additionally takes the monospace family, as
in Chrome's `html.css`.

The 1.2 ratio sentinel is used rather than the `normal` sentinel (0) on purpose:
`style_line_h`'s `normal` fallback is `line_h(fs) = 9 * (fs / 8)`, which at
fs=13 yields **9 px**, not 15. Fixing that general fallback is a separate,
wider change; this record names it rather than silently relying on it.

## Relation to the +12 % block advance

This is one of the two independent causes behind
`doc/08_tracking/bug/web_block_vertical_advance_12pct_2026-09-12.md`. That record
excluded the block-advance rule, margin collapsing, explicit `line-height` and
the default line-box height, and correctly concluded the cause was
element-specific. It is: form controls here, and auto-width flex items in
`doc/08_tracking/bug/web_flex_wrap_auto_width_item_fills_line_2026-09-12.md`.
There is no single "+12 % block advance" defect.

## Spec

`test/01_unit/browser_engine/form_control_ua_font_spec.spl` — absolute Chrome
oracles: button `h == 33`, strip `h == 53`, strip `y == 24`, button `y == 34`.
