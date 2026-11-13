# Hosted worker: absolutely positioned full-viewport main renders white at (0,0)

- **ID:** hosted_worker_absolute_main_renders_white_perf_pixels_2026-11-13
- **Status:** OPEN
- **Severity:** P3
- **Found by:** lane p3-browserrev while fixing
  `browser_composition_revision_counters_never_increment_2026-08-19`

## Evidence

`test/05_perf/browser/hosted_browser_revision_wire_perf_spec.spl` renders
`<main style='position:absolute;left:0;top:0;width:64px;height:64px;background:#dc2626'></main>`
(alternating with `#2563eb`) through `HostedBrowserRendererWorkerSession`
and the software `Engine2dCompositorBackend`, and expects every one of the
4096 pixels to be the main's colour. On release/1.0.0 (Rust seed) every
changed and unchanged frame has `pixels[0] == 0xFFFFFFFF` (white page
canvas), so `mismatches == 11` of 11 pairs. Revisions and reuse are correct
in the same run (`render_count=12 reuse_count=14`).

For comparison, the static-position main in
`test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl`
lays out at `x=8 y=8` (default body margin) in the decoded DrawIR, which is
correct for static flow.

## Hypothesis (unverified)

`position:absolute; left:0; top:0` is not honoured on this path, so the main
still sits at the body-margin offset and (0,0) shows the white canvas.
Alternatively the spec's whole-viewport colour expectation is too strict.
Either needs a layout-owner check: dump the decoded DrawIR `main_*` rect for
the perf HTML and compare with the expected `x=0 y=0 width=64 height=64`.
