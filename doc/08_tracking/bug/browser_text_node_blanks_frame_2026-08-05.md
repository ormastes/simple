# Browser renders boxes pixel-exact, but any text node blanks the whole frame

**Status:** OPEN
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
