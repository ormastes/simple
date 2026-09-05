# web_render_file_gui: window presents small pages but stalls on google.com page

- **Status:** Fixed (CPU busy-spin) + open blockers (renderer degradation, cli_get_args)
- **Date:** 2026-07-11
- **Area:** examples / ui (web_render_file_gui.spl present loop) + web software renderer
- **Severity:** P2 (live-window lane unusable for real-world pages)

## Symptom (as reported)

`scripts/gui/macos-gui-run.shs` + `web_render_file_gui.spl` (constants bumped
to 480x360):

- `hello_world.html` (small page): renders and PRESENTS on screen correctly.
- live `google.com` HTML (82KB): app logs
  `Rendered 172800 px via requested backend 'cpu_simd'`, but the window stays
  WHITE; process burns 90-98% CPU for many minutes with no frame ever
  composited.

## Root cause (diagnosed 2026-07-11)

The "present stall" premise was WRONG. Two independent defects, neither in the
present path:

### 1. The white window is FAITHFUL — the renderer produces all-white pixels

Headless render of the same three pages through the SAME entry
(`simple_web_render_html_to_pixels_with_engine2d_backend`, 480x360, cpu_simd):

| page | bytes | white px | colored px |
|------|-------|----------|-----------|
| simple_colored.html | 297 | 150904 | **21572** |
| examples/06_io/ui/sample_page.html | 4324 | 0 | **172800** |
| **google_live.html** | 81970 | **172800** | **0** |

So the present path is fine (small/colored pages composite); the google buffer
is genuinely 172800 white pixels, 0 colored. The window shows white because the
pixels ARE white.

Why white: google routes through the cpu_simd `<a>/<p>/<span>…` fast-path into
`simple_web_layout_render_html_software_pixels`
(`simple_web_html_layout_renderer.spl`). That renderer arms a **10s wall-clock
budget** (`WEB_RENDER_BUDGET_MS = 10000`). google inlines a huge minified
`<style>` block; the CSS extract/cascade
(`extract_css_vw` / `compute_styles`) blows the budget — `parse_html` returns
in 183ms with only 82 nodes, then the CSS phases run for ~10s+ (total wall ~20s)
and `simple_web_layout_last_render_degraded()` returns **true**. On budget
expiry the phases stop at a loop boundary (by design — never a panic, never an
empty buffer, see the guard comment at renderer.spl:41-46) and the untouched
white base framebuffer is returned. Result: an all-white "graceful degradation"
frame.

This is the renderer's designed fallback, not a present bug. Making google
content actually paint is a SEPARATE, out-of-scope effort — see blockers below.

### 2. The 90-98% CPU burn — busy-spin present loop (FIXED)

The example's post-render poll loop was a tight busy-spin:

```
while running and iters < 2000000:
    if winit_poll_close_requested(lp): running = false
    if iters % 200 == 0: winit_present_rgba(win, RW, RH, packed)
    iters = iters + 1
```

No sleep/yield. At ~40 iters/s (each loop re-presents 172800 px every 200
iters, interpreted) the 2,000,000-iteration cap is ~14 HOURS of one core pegged
— the "burns CPU indefinitely" symptom. This is size-independent: the hello
case has the same loop; it just gets closed sooner.

**Empirically disproved the "never sleep on macOS" caution for this present
path:** with a 16ms per-frame `thread_sleep` the window still composites (colored
probe verified on screen 2026-07-11), and re-presenting the CACHED buffer only
every ~15 frames keeps the surface alive at ~15% CPU.

## Fix (examples/06_io/ui/web_render_file_gui.spl)

- Rewrote the poll loop: render once, present the cached buffer once, then loop
  bounded by a 60s wall-clock deadline (matching sibling
  `examples/06_io/ui/web_engine2d_gui.spl`), polling close every frame,
  `thread_sleep(16)` per frame, and re-presenting the cached buffer only every
  ~15 frames. New imports: `thread_sleep`
  (`std.nogc_sync_mut.concurrent.thread`), `time_now_unix_micros`
  (`std.nogc_sync_mut.io.time_ops`).
- Fixed a STALE fallback path: `examples/ui/sample_web_renderer_sanity.html`
  → `examples/06_io/ui/sample_web_renderer_sanity.html` (the old path no longer
  exists, so every GUI-driver launch — where `cli_get_args` is stubbed and the
  fallback is always used — exited with "HTML file not found" before ever
  reaching the loop). Also corrected the header run-example comment.

### Verification (2026-07-11)

- Probe with the identical new loop (`tools/pixel_compare/gui_sleep_probe.spl`,
  480x360, colored page) via the .app bundle: window composites the content
  (Hello Render title + blue/red boxes captured on screen), CPU **16.8%**
  (down from **100%**), loop exits cleanly at the deadline.
- Original example headless from repo root: renders the widget page (4800 px at
  80x60) and returns cleanly — new imports compile, fixed path resolves.

## Open blockers (NOT fixed — out of tight scope)

- **google content never appears in-window.** Requires ALL of: (a) a render
  budget large enough to complete layout+paint of an 82KB page, (b) fixing an
  interpreter builtin gap — a full-budget render crashes with
  `Function 'str.ord' not found` at ~51s (`.ord()` on a char, used in the
  renderer's hex-color parse at simple_web_html_layout_renderer.spl:593-597;
  the 10s-budget path degrades to white before reaching it), and (c) tolerating
  a multi-minute interpreted render. Note google is mostly-white with an image
  logo the software renderer likely won't paint anyway, so even a completed
  render may be sparse. Do NOT simply raise `WEB_RENDER_BUDGET_MS`: with the
  `str.ord` crash a larger budget converts "white window" into "crash" (strictly
  worse). File the budget-vs-completeness and `str.ord` items separately.
- **GUI driver stubs `cli_get_args`** (`[STUB] cli_get_args not available
  without Rust SFFI`). `.app`-bundle launches cannot pass a file argument, and
  their cwd is a temp dir, so no relative fallback can resolve either — the
  example's live-window lane is only usable once `cli_get_args` works (or an
  absolute path can be injected some other way). Worth a bug/feature of its own.

## Notes

- Trace-vs-untraced timing discrepancy seen during diagnosis (traced render
  >300s vs untraced ~20s on identical work) is attributed to shared-machine load
  during the traced run, not a code path difference.
