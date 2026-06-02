# Production GUI Web Renderer Parity Hardening Agent Tasks

## Parallel Audit Completed

- Renderer infrastructure audit: identify real pixel comparison harnesses,
  dummy/sentinel tests, and production parity gaps.
- Web/widget renderer audit: identify heuristic routing, exact fixture
  branches, CSS/layout gaps, and generated HTML escaping risks.
- SPipe artifact audit: identify requirement, architecture, design, spec, and
  manual paths.

## Current Implementation Slice

- Add marker-free generated GUI widget parity harness.
- Route generated widget HTML through the generic layout renderer.
- Add generic image fallback rendering in the layout renderer.
- Add executable SPipe system spec for software, CPU SIMD, and Metal exact
  backend parity.
- Add live Electron generated-GUI HTML evidence that compares Electron capture
  pixels against Simple CPU SIMD expected pixels and records the current
  divergence.

## Next Agent Tasks

- Convert the live Electron generated-GUI divergence into passing parity by
  aligning viewport/base offset, CSS defaults, image replacement behavior, and
  text rasterization policy.
- Add a canonical Electron/WebKit capture manifest and exact pixel runner.
- Add CPU SIMD counter evidence to the parity report.
- Add Metal GPU-readback provenance to reject CPU mirror fallback.
- Expand CSS/layout matrix for width, height, margin, padding, border, flex,
  gap, and nested selectors.

## Verified Diagnostics — Claude (2026-06-02)

Independent verification of the Electron capture path on macOS arm64 (Retina).
Read-only probes; no hot-path files touched (concurrent agent owns
`exact_fixture.js`, the `.shs`, `production_gui_web_renderer_parity.spl`,
`generated_gui_web_parity_expected.spl`, and the renderer modules).

### CRITICAL: Electron capture is 2× on Retina — all parity numbers are invalid

`BrowserWindow.capturePage({width:96,height:72})` returns an image whose
`image.getSize()` is **192×144**, and `image.toBitmap()` is
`110592 bytes = 192×144×4`. The screen `scaleFactor` is 2, and
`--force-device-scale-factor=1` does **not** change the capture backing size.

`tools/electron-live-bitmap/exact_fixture.js` reads that 192-wide BGRA buffer as
if it were 96 wide, so the "captured" 96×72 ARGB JSON is actually the **top-left
192×36 slice mislabeled 96×72** — the horizontal-scanline garbage visible when
the buffer is rendered to PNG. Consequence: **every Electron parity
`mismatch_count` / `checksum` on a Retina Mac is a stride-misalignment artifact,
not a rendering-fidelity measurement.** This is separate from, and not fixed by,
the transparent-black document-wrapper change in progress.

Verified via `build/cap_probe/getsize_probe.js`:
`getSize={192,144}, bitmapBytes=110592, scaleFactor_screen=2`.

### Verified fix recipe (box-downsample native → logical)

Capture, then box-average the native `image.getSize()` buffer down to the
requested logical W×H before comparison:

```
const sz = img.getSize();              // 192×144 on 2× displays
const bm = img.toBitmap({scaleFactor:1}); // BGRA at sz.width×sz.height
const kx = sz.width / W, ky = sz.height / H;
// average each kx×ky native block into one logical pixel (ARGB-u32)
```

Verified via `build/cap_probe/downscale_probe.js`: the downsampled 96×72 frame
has **386 distinct colors** (proper Chromium AA) and renders as a correct widget
layout — crisp "AB CD"/"EF" text, green image placeholder, blue RUN button with
orange icon, dark border, white AA text (see `build/cap_probe/electron_fixed_6x.png`).

Equivalent alternatives: capture at native size and compare against a Simple
render upscaled to native (worse — Simple has no AA), or run Electron under an
`scaleFactor=1` display. Box-downsample is the least invasive and is what the
node reference path already assumes.

### Implication for the parity gate

After both fixes (document wrapper + 2× downsample), Simple (6–8 flat colors,
5×7 bitmap font) still will not pixel-match Chromium (386 AA colors). That is
expected and acceptable per NFR-006: **record** mismatch %, viewport, color
format, and both artifact PNGs as documented divergence; do not assert `==0`.
Closing the fidelity gap (AA/gamma/LCD text) is the long-tail "production level"
work tracked in `doc/03_plan/gui_hardening_current_plan_2026-06-01.md`.

### Convert layer — LANDED (commit 9a1b094a)

A native→logical resolution convert layer was added to
`tools/electron-live-bitmap/exact_fixture.js` (`bitmapToLogicalBgra`): it reads
`image.getSize()`, box-averages each native block into one logical pixel, and
feeds the logical buffer to the existing checksum/compare/write path. The proof
JSON + stdout now record `capture_native_width/height` and `capture_downsampled`
provenance. Comparison is now **resolution-agnostic** — any capture scaleFactor
is normalized to the logical comparison resolution.

Verified on macOS arm64 (scaleFactor=2) across three logical resolutions; each
detects native = 2× and downsamples to a correct 384-color AA render (was
scanline garbage):

| logical | native  | captured px | distinct colors |
|---------|---------|-------------|-----------------|
| 96×72   | 192×144 | 6912        | 384             |
| 128×96  | 256×192 | 12288       | 384             |
| 160×100 | 320×200 | 16000       | 384             |

Note: the commit also carries the concurrent agent's in-flight readiness-
detection hunks (font/image load wait) in disjoint regions of the same file —
`jj commit <path>` cannot split a single file. Saved to project memory as
`bug-electron-capture-2x-retina`. Probes: `build/cap_probe/{getsize,downscale}_probe.js`,
`patched_6x.png` (corrected reference from the production tool).

**Still open (concurrent agent):** transparent-black for *unstyled* generated
HTML is a separate bug — the document-wrapper fix (`generated_gui_web_page_html`
with background + `generate_css`) lives in `production_gui_web_renderer_parity.spl`
and is in-flight. After both land, Simple (6–8 flat colors) still won't
pixel-match Chromium (384 AA colors); record the divergence per NFR-006.
