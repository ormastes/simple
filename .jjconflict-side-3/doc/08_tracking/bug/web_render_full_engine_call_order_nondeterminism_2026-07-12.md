# Full HTML layout engine produces different pixels for identical input depending on call order

## Status

Open. Discovered while regression-testing the content-frame routing fix
(see `web_render_full_engine_content_frame_reroute_perf_2026-07-12.md`);
not introduced by that fix — pre-existing in
`simple_web_html_layout_renderer.simple_web_layout_render_html_software_pixels`,
just never previously exercised by this spec because the content-frame path
used the (trivially deterministic) tag-strip fallback until now.

## Reproduction

`test/01_unit/os/compositor/simple_web_window_renderer_spec.spl`, test
"keeps unchanged content identity stable and changes it on mutation":

```text
val first_cache = web_render_pixel_artifact_cache(96, 48, "software")
val second_cache = web_render_pixel_artifact_cache(96, 48, "software")
...
val first = simple_web_content_frame_cached(first_cache, "w", 1, stable_revision, "glass_dark", "动态 title", "<b>same pixels</b>", 96, 48, 0)
val second = simple_web_content_frame_cached(second_cache, "w", 2, repeated_revision, "glass_dark", "动态 title", "<b>same pixels</b>", 96, 48, 0)
expect(first.checksum).to_equal(second.checksum)   # FAILS
```

`first` and `second` render byte-identical inputs (same theme, title, body
HTML, width, height, scroll) through two freshly-constructed, independent
`WebRenderPixelArtifactCache` instances (no shared state). Expected: same
checksum. Actual (bootstrap seed,
`bin/release/aarch64-apple-darwin/simple_seed`):

```
expected 2172276232890085205 to equal 2172276232889594837
```

Reproduced identically across repeated process runs (same two checksum
values both times) — this rules out wall-clock/GC-timing jitter as the
cause; it is deterministic given the same *call order/count* within a
process, but differs between the first render call and a structurally
identical second render call. The delta is small relative to the checksum
magnitude, consistent with a handful of differing pixels rather than a
wholesale degraded/truncated render.

## Likely cause (not confirmed)

`simple_web_html_layout_renderer.spl` has a wall-clock render budget
(`WEB_RENDER_BUDGET_MS = 10000`, `_web_budget_begin`/`_web_budget_expired`
using a module-level `_web_render_deadline_us`) but 10s is far larger than
the observed ~4-5s single-render cost under the interpreted seed, so budget
expiry during a single render is unlikely to be the direct cause. More
likely candidates (unconfirmed): a process-lifetime counter or
non-deterministically-ordered map/cache (e.g. a font/glyph cache, arena
slot allocator, or `SimpleWebEngine2DStaticPixelCache`-adjacent state) whose
first-vs-second-touch behavior differs between the first and second call in
a process even with fresh cache objects and identical input.

## Not done here (out of scope for the content-frame routing fix)

Diagnosing the exact non-determinism source inside the ~9,567-line
`simple_web_html_layout_renderer.spl` is a renderer-internals
investigation, not a routing fix, and was explicitly out of scope for the
task that surfaced this (see sibling perf bug doc). Left the assertion
failing (not skipped/weakened) per repo testing rules — do not disable or
convert to NOTE without approval.

## Suggested follow-up

- Bisect `simple_web_layout_render_html_software_pixels` stages
  (style -> layout -> paint, per the budget-stage comments) to find which
  stage's output differs between the two calls.
- Check for any module-level `var`/static registry read or mutated during
  rendering that isn't reset per-call or per-cache-instance.
