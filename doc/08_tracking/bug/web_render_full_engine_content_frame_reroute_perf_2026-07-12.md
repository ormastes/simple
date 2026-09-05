# Full HTML layout engine ~55-60x slower than tag-strip fallback per actual content-frame re-render

## Status

Open (perf-only; not blocking). Filed alongside the routing fix that made this cost reachable in production (see below).

## Context

`os.compositor.simple_web_window_renderer._simple_web_content_frame_cached_impl`
(backing `simple_web_content_frame_cached` / `simple_web_child_content_frame_cached`,
called from `host_compositor_core.spl:778` and `shell.spl:863`) previously
defaulted every desktop window's content-frame paint to
`WebRenderPixelArtifactCache.request_to_native_safe_pixel_artifact` — a
degraded tag-stripping/5x7-bitmap-glyph renderer
(`web_render_pixel_software_backend._native_safe_wm_pixels`) that was meant
only as an explicit crash-recovery fallback, not the default. That routing
bug is fixed in this change (swapped to `request_to_pixel_artifact`, the
full HTML/CSS layout engine at
`simple_web_html_layout_renderer.simple_web_layout_render_html_software_pixels`).

## Measurement

Probe: `WebRenderPixelArtifactCache.request_to_native_safe_pixel_artifact` vs
`.request_to_pixel_artifact`, 640x480, 10 iterations, forcing a cache MISS
every call (distinct HTML per call) to isolate actual re-render cost from
one-time module-load. Run via
`src/compiler_rust/target/bootstrap/simple run <probe>.spl` (bootstrap seed,
tree-walking interpreter — SIMPLE_EXECUTION_MODE default).

| Path | call 0 (incl. module load) | steady miss avg (calls 1-9) |
|---|---|---|
| `request_to_native_safe_pixel_artifact` (tag-strip) | ~71-82ms | ~72-84ms |
| `request_to_pixel_artifact` (full engine) | ~4025-5387ms | ~4009-4679ms |

Ratio: **~55-60x slower per actual re-render** under the interpreted seed.

Warm-cache (unchanged content, cache HIT — the steady-state case for a
window whose content isn't actively changing) is NOT affected: both paths
return in comparable time (~40-60ms), since a hit short-circuits before
touching the render engine at all. The per-call ~700-770ms overhead
observed in the full `simple_web_content_frame_cached` wrapper on a cache
hit is `common.ui.window_scene.wm_content_frame_checksum` iterating the
full pixel buffer (307,200 u32 for 640x480) every call under the
interpreter — present identically before and after this routing fix, not
introduced by it.

## Impact

Every real content change (keystroke in an editor/terminal window, live
state update) now re-renders through the full layout engine instead of the
tag-strip scanner. Under the interpreted seed this is ~4s per re-render;
the self-hosted compiled binary (the actual deployed tool per
`.claude/rules/bootstrap.md`) was not separately measured here and should
be materially faster, but the relative algorithmic gap (full HTML/CSS
layout+paint vs. a linear tag-strip+bitmap-glyph scan) is real and will
persist at some ratio in compiled code too.

## Not done here (over-engineering / out of scope for the routing fix)

- Profiling/optimizing `simple_web_layout_render_html_software_pixels`
  internals (9,567-line file) — a rewrite, not a routing fix.
- Debouncing/throttling content-revision-triggered re-renders at the
  compositor frame-loop level.
- Re-measuring under the self-hosted release binary (`bin/simple`) rather
  than the bootstrap seed.

## Suggested follow-up

- Re-run this probe against `bin/release/aarch64-apple-darwin/simple` (or
  `bin/simple`, the self-hosted deployed tool) to get a real steady-state
  number, since the interpreted seed is known to have large constant-factor
  overhead unrelated to the renderer's own algorithmic cost.
- If the compiled-binary number is still too slow for interactive typing
  (e.g. terminal echo), consider debouncing content_revision-triggered
  re-renders (coalesce rapid successive content changes within one frame
  tick) rather than reverting to the tag-strip fallback.
