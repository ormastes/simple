# Office three-host rendering: residual divergences after empty-block margin fix

**Date:** 2026-08-19
**Area:** rendering / pure-Simple web lane vs Electron (Chromium) vs Tauri2 (WebKitGTK)
**Status:** FIXED — 2026-11-11 (lane ne18); all three residual items resolved or
closed-out (OPEN 1 margin-collapse-through-wrapper implemented + spec-pinned;
OPEN 2 font rasterization is a permanent no-action class per this doc; OPEN 3
heuristic fake deleted 2026-10-05). Code now lives under
`src/lib/gc_async_mut/gpu/browser_engine/`.

## Context

The same office document (markdown WYSIWYG preview HTML from
`app.office.md_wysiwyg.wysiwyg_preview_pane`, doc: `build/office_parity/doc.md`)
was captured at 640x480 through three hosts:

- pure-Simple: `simple_web_render_html_to_pixels_with_engine2d_backend(..., "cpu_simd")`
  -> `build/office_parity/simple.ppm`
- Electron 38 (real Chromium, npx-installed, `--no-sandbox --disable-gpu` on
  DISPLAY=:99) via `tools/electron-live-bitmap/capture_html_argb.js`
  -> `build/office_parity/electron.ppm`
- Tauri2 engine proxy: Playwright WebKit 26.4 (the same WebKit engine that
  `libwebkit2gtk-4.1.so` wraps — Tauri2's webview on Linux) via
  `tools/pixel_compare/capture_webkit_argb.js`
  -> `build/office_parity/tauri_webkit.ppm`

Diffed with `common.imaging.capture_align.align_buffers` +
`os.compositor.screenshot_compare.find_diff_regions`
(`build/office_parity/diff_pair.spl`).

## FIXED in this change

Missing CSS 2.2 §8.3.1 **self-collapsing empty-block margins**: every blank
markdown line becomes an empty `<p>` with 1em margins; the pure-Simple lane
gave it a 1px box plus BOTH margins, pushing each later block ~17-20px lower
than Chromium/WebKitGTK (cumulative: last block 87px low). Fixed in
`src/std/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
(block child loop). Reproduce spec (failing pre-fix, green post-fix):
`test/02_integration/rendering/empty_block_margin_self_collapse_spec.spl`
(+ `test/integration/rendering/` mirror). Content bands moved from
31/104/159/223/257/308 to 31/87/125/172/206/240 (electron: 15/68/109/154/188/221).

## OPEN 1: first-child margin does not collapse through a wrapper block

Browsers collapse a first child's margin-top through any ancestor chain of
blocks with no top border/padding (body -> div -> h1: h1's margin escapes to
the body level; final top offset = max(body 8, h1 21) = 21). The Simple lane
only implements this for the direct children of `body`
(`simple_web_html_layout_renderer_layout.spl`, `nodes[i].tag == "body"`
special case), so the office preview's `<div class="wysiwyg-preview">`
wrapper adds body-margin + child-margin additively: a constant ~8px extra
top offset (measured minimal case `build/office_parity/case_b.html`: first
ink row simple y=29 vs electron y=23). A general fix must propagate the
escaped margin to the consumer level AND suppress it inside the wrapper,
without breaking flex/overflow contexts (flex items establish a new BFC and
must NOT collapse) — deferred rather than half-done.

## OPEN 2: remaining pixel diff is font rasterization

Post-fix pairwise diff at threshold 32: simple vs electron 10,074/307,200 px
(96.7% match), simple vs webkit 10,776 (96.5%), electron vs webkit 11,923
(96.1%). All diff regions sit on text glyphs (the two real browsers differ
from each other by the same magnitude). Not a Simple-side defect class beyond
font metrics/hinting; no action beyond the existing font parity lanes.

## OPEN 3 (found while reproducing): heuristic surface renders tag-gated nonsense

`simple_web_engine2d_render_html_pixels`
(`src/std/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:1062`)
routes HTML with no `<p>/<h1>/.../<a>` tag to `SimpleWebHeuristicSurface`, a
string-matching fake that guesses one or two blocks from the raw HTML text. A
plain two-`<div>` page (both with `background:#...`) renders the first div at
the wrong size (240 px instead of 400) and drops the second div entirely,
while the real layout path (`simple_web_render_html_to_pixels`, and the same
page with a `<p>` present) renders both correctly. Any host-parity capture of
div-only HTML through the engine2d entrypoint silently compares against the
heuristic, not the layout engine.

## Environment notes

- Real `cargo tauri` shell (`tools/tauri-shell`) was NOT built: no cached
  target dir (full cold build of the Tauri crate graph), and its capture
  scripts (`tools/tauri-live-bitmap/*.swift`, `capture-all.command`) are
  macOS-only. WebKitGTK-via-Playwright is the engine-accurate Linux proxy;
  `cargo tauri-cli 2.10.1` and `libwebkit2gtk-4.1` are installed if a full
  shell lane is wanted later.
- Electron pixel capture works headlessly on this box via
  `~/.npm/_npx/.../electron/dist/electron --no-sandbox` (the repo tool's
  documented invocation); no system electron package exists.

## Addendum 2026-11-11 (lane ne18) — FIXED, per-item evidence

Triage verdict: **FIXED** (all three residual items). The renderer also moved:
`src/std/gc_async_mut/gpu/browser_engine/` → `src/lib/gc_async_mut/gpu/browser_engine/`
(this doc's paths are stale).

- **OPEN 1 — FIXED.** First-child margin-top now collapses through ANY
  transparent ancestor chain, not just `body`: the block child loop
  (`simple_web_html_layout_renderer_layout_engine.spl:2060-2090`) collapses
  the child's declared margin-top with `child.leading_margin_t` (whatever
  escaped through the child's own top edge), `block_top_margin_collapses_through`
  decides per-block, and an escaping margin is re-published as this block's
  `leading_margin_t` for its parent — the deferred "propagate AND suppress"
  pair from this doc. Pinned by
  `test/01_unit/browser_engine/first_child_top_margin_collapse_spec.spl`
  (Chrome-oracle fixtures, REQ-BROWSER-ENGINE-MARGIN-COLLAPSE-003; dedicated
  bug doc `web_first_child_top_margin_never_collapses_through_2026-09-13.md`).
  Verified in this lane (seed-smoke, fresh seed 46fe8f6b6def, interpreter
  mode, `--no-cache`): **10 total, 10 passed, 0 failed**.
- **OPEN 2 — CLOSED, no action (by this doc's own ruling).** The remaining
  diff is font rasterization/hinting, present browser-to-browser at the same
  magnitude; "no action beyond the existing font parity lanes."
- **OPEN 3 — FIXED 2026-10-05.** `SimpleWebHeuristicSurface` and the
  tag-gated routing are deleted; every document goes through the real
  parse→cascade→layout→paint engine
  (`simple_web_engine2d_renderer.spl:973-988`). Recorded as FIXED in
  `browser_static_lane_heuristic_fake_2026-10-05.md` with replacement spec
  `test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl`. Verified in
  this lane (seed-smoke): that spec runs 7 examples — the heuristic-fake
  replacement case "lays out a styled page without text-document tags for
  real" PASSES, as do both pixel-fake regression cases. The single failure
  ("keeps native backend aliases…", expected metal/cuda/rocm) is an
  unrelated host-capability probe: this GPU-less Windows lane resolves
  preferred backends to `software`; it is not a residual of this bug.
