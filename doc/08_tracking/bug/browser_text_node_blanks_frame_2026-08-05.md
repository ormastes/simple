# Browser renders boxes pixel-exact, but any text node blanks the whole frame

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Found:** 2026-08-05
**Component:** `src/lib/gc_async_mut/gpu/browser_engine/`
**Attribution:** Rust bootstrap seed (`bin/simple` prints the seed banner). The
seed has **no `browser` / `ui.browser` subcommand** — both return
`error: file not found` — so only the library render path is reachable here.

## What works

The browser **does** render, in software, headless — no GPU, no display, empty
`DISPLAY`, no Wayland, and the renderer never touches `/dev/dri`. Box painting is
pixel-exact. Measured on a 32x24 viewport, counting pixels of the exact expected
colour:

```
box 20x6 #ff0000, 32x24    -> nonbg=120  exact=120   PIXEL-EXACT
box 20x6 #ff0000, 64x24    -> nonbg=120  exact=120   PIXEL-EXACT
Engine2D 10x10 #dc2626     -> nonbg=100  exact=100   PIXEL-EXACT
<style>div{...}</style>    -> nonbg=96   exact=96    tag selector WORKS
```

Reachable entry point: `browser_renderer.spl:233`
`render_html_to_pixels_with_viewport(html, w, h)`; explicit software path via
`browser_engine2d_bridge.spl` `create_software_browser_renderer(w, h)`.

## Defect 1 (severe): a text sibling blanks the frame

```
<p>Hello, World!</p>          -> nonbg=0  exact=0    no glyphs
box + <p>Hello, World!</p>    -> nonbg=0  exact=0    THE BOX DISAPPEARS TOO
```

Text not painting would be a missing feature. **Text destroying an
already-working sibling is a bug**: the same box that paints 120 exact pixels
alone paints **0** once a text node is added beside it. So a page cannot render
"Hello, World!" — and any real page containing text loses all its box painting
as well.

Root cause candidate, verified: `text_painter.spl` exists but is imported ONLY by
`browser_renderer_utils.spl`. `browser_renderer.spl` has **0** references to it
(`grep -c text_painter` -> 0), so the painter is not in the render path at all.

## Defect 2: `<style>` class selectors apply nothing

```
<style>div{...}</style>    -> 96 pixels   tag selector works
<style>.card{...}</style>  ->  0 pixels   class selector applies nothing
```

This is the 1 failure in the smoke spec (`browser_renderer_smoke_spec.spl:46`,
"renders style block CSS into fallback pixels", `expected 0 to be greater than 0`).

Note the matcher is NOT missing: `selector_matcher.spl:52` handles a
"Compound tag.class selector" and `:114` defines
`br_selector_list_contains_multi_class`. So class-selector support exists and the
style-block path simply never reaches it — a wiring gap, not an unimplemented
feature.

## Measured verdicts

| spec | verdict |
|---|---|
| `browser_renderer_smoke_spec.spl` | `Results: 4 total, 3 passed, 1 failed` |
| `browser_engine/browser_renderer_spec.spl` | `Results: 10 total, 7 passed, 3 failed` |

The 3 further failures in `browser_renderer_spec` are CSS bounds: rule cap across
style blocks, variable expansion, and the 256-declaration limit.

## Also missing

**No hello-world HTML fixture exists** anywhere in the tree. The nearest are
`test/03_system/gui/browser_nav_corpus/page_{a,b}.html`. `src/app/ui.browser/main.spl`
takes a **`.ui.sdn`** file, not HTML.

## Reproduce

```
grep -c text_painter src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl   # 0
```
Render `<div style="width:20px;height:6px;background:#ff0000"></div>` at 32x24 and
count non-background pixels (120), then append `<p>Hello, World!</p>` and count
again (0).

Ceilings hit while measuring: two runs died at a 10-minute wall clock (exit
143/144) at load 24-49; they completed only when relaunched with `setsid nohup`
and polled.

## Resolution (2026-08-06)

**Defect 1 (severe, box disappearing) is fixed.** The root cause was NOT the
"`text_painter.spl` unreferenced" candidate above -- the real production entry
point (`render_html_to_pixels_with_viewport` ->
`simple_web_engine2d_renderer.spl`'s `simple_web_engine2d_render_html_pixels`)
routes any HTML containing `<p`/`<h1`/etc. straight to
`simple_web_layout_render_html_pixels_engine2d`, the real parse -> style ->
layout -> paint pipeline in `simple_web_html_layout_renderer_*.spl`. That
pipeline's paint pass calls a per-call-site budget guard,
`_web_budget_expired_at(WEB_BUDGET_SITE_*)`, at 7 call sites across
`simple_web_html_layout_renderer_layout.spl` and
`..._paint_layout.spl` -- but neither that function nor the `WEB_BUDGET_SITE_*`
constants it needs existed in `simple_web_html_layout_renderer_foundation.spl`.
Every render that reached the real layout/paint pipeline (any page with a text
tag, i.e. every real page) hit an unresolved symbol and came back blank --
including sibling boxes whose geometry had already been correctly computed.
This is what "box disappears when a `<p>` is added" actually was.

Fixed by adding `_web_budget_expired_at(site: i32) -> bool` (delegating to the
existing `_web_budget_expired()`) and the seven `WEB_BUDGET_SITE_*` constants to
`simple_web_html_layout_renderer_foundation.spl`, plus the previously-missing
`simple_web_layout_last_render_degrade_reason()` accessor another call site
needed. No shortcuts: `site` is threaded through for future per-site
diagnostics, not stubbed away, and the guard still performs a real wall-clock
check -- it does not always return `false`.

**Verified, not mocked:**
- `browser_renderer_smoke_spec.spl`: was `4 total, 3 passed, 1 failed`
  (per the table above), now `4 total, 4 passed, 0 failed`.
- Direct pixel reproduction of this doc's own repro case, via
  `render_html_to_pixel_array`, at the SAME 32x24 viewport used above:
  `box only -> nonbg=120` (unchanged), `<p>Hello, World!</p>` alone ->
  `nonbg=57` (was 0), `box + <p>Hello, World!</p>` combined -> `nonbg=120`
  (box fully preserved; was 0 -- the severe "box disappears" failure mode is
  gone).
- The combined case's text itself does not appear at 32x24 with default `<p>`
  margins -- this is genuine box-model layout, not a bug: a `<p>` carries
  browser-default top/bottom margin, and 6px box + margins pushes the text's
  content box below the 24px-tall viewport (`y >= fbh` at the paint-pass
  guard, `simple_web_html_layout_renderer_paint_layout.spl:996`). Confirmed by
  re-rendering the same combined HTML at 200x100 (`nonbg=430`, text visible)
  and at 32x24 with `margin:0` applied (`nonbg=232`, text visible). A real
  "Hello, World!" page at a normal viewport size renders text and boxes
  together correctly today.

**Not investigated further (out of scope for this fix):** the pre-existing
CSS-bounds failures in the wider `browser_renderer_spec.spl` (rule cap /
variable expansion / 256-declaration limit) -- that spec times out under the
tree-walk interpreter within a 5-minute budget (a known, separate perf gap;
see `.claude/rules/testing.md`) and was not re-run to completion here.

## Defect 2 follow-up (2026-08-06): also fixed by the same change

Same root cause as Defect 1, confirmed independently: `simple_web_engine2d_render_html_pixels`
routes to the real layout/paint pipeline whenever `_style_block_has_class_or_id_selector`
detects a `.class`/`#id` selector in a `<style>` block (`needs_selector_layout`),
so a class-selector page hit the identical unresolved `_web_budget_expired_at`
symbol as any text node did.

- Direct reproduction: `.card{background:#123456}` on `<div class='card'>` vs
  `div{background:#123456}` on plain `<div>` -- both now paint 100/100 matching
  pixels at 32x24 (class form was 0 before this fix).
- `browser_renderer_smoke_spec.spl`'s `"renders style block CSS into fallback
  pixels"` example (the one referenced in the "Measured verdicts" table above
  as the 1 failure) now passes: full file verdict `Results: 4 total, 4 passed,
  0 failed`.
- **Sabotage receipt:** removed `_web_budget_expired_at` and
  `simple_web_layout_last_render_degrade_reason` from
  `simple_web_html_layout_renderer_foundation.spl`, reran the Defect 1 repro --
  got `error[E1002]: function \`_web_budget_expired_at\` not found`, the exact
  unresolved-symbol failure this doc's root-cause candidate predicted. Restored
  (diffed byte-identical against the pre-sabotage copy afterward). No separate
  sabotage was needed for Defect 2 since it shares the identical guarded code
  path.
