# Web-render JS oracle painted the WM compositor's chrome for an engine2d scene

- Date: 2026-09-06
- Status: FIXED (oracle), residual measured and open (text)
- Component: `tools/node-render-bitmap/simple_web_engine2d_fixture.js`
- Affected gates: `check-simple-web-engine2d-js-bitmap-evidence.shs` and every
  leaf that sets `SIMPLE_WEB_ENGINE2D_SCENE=simple-web-engine2d-image-taskbar-command`
  (`check-bun-…`, `check-electron-…`), plus the budgeted scene-matrix gates above them.

## Defect

`renderHtmlToPixels()` dispatched 15 scene names and let anything else fall through
to a hardcoded frame. Scene `simple-web-engine2d-image-taskbar-command` — the
default, and a real gate scene — had **no dispatch case**, so it took that
fallthrough, which painted:

```js
pixels.fill(0xFF112233);                             // body background
rect(pixels, 8, 8, 80, 40, 0xFF445566);              // titlebar
rect(pixels, 0, 0, width, 24, 0xFF2050A0);           // covers the whole canvas ...
rect(pixels, 0, 24, width, height - 24, 0xFF182230); // ... top and bottom
```

Two independent faults:

1. **Dead stores.** The last two rects tile the entire canvas, so the body
   background and the titlebar were overwritten before readback. Output was two
   colors; neither `#112233` nor `#445566` appeared in a single pixel.
2. **Wrong renderer's palette.** `#2050a0` over `#182230` with a full-width 24px
   titlebar is the WM *compositor* chrome from
   `src/os/compositor/hosted_wm_capture_evidence.spl:142,155-158` — a different
   renderer and a different scene. The engine2d path deleted its `wm-app`
   substring heuristic (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:1157-1160`,
   "The former substring heuristic painted a fixed blue/slate demo palette over
   the fully resolved Aetheric document") and now routes this HTML through the
   real CSS layout/paint engine. The oracle was never updated.

The comparison is exact-bitmap (`mismatch_count` must be 0), so the gate could
only ever have been red. It was never observed because every leaf ERRORs before
comparing on any host without a self-hosted binary — see the host note below.

## Measurement

Scene HTML is the `main()` default in `check-simple-web-engine2d-js-bitmap-evidence.shs:172`.
Simple side rendered through the gate's own call path,
`SimpleWebEngine2DStaticPixelCache.create(96, 64, "software").pixels_for_html(html)`,
run under the **Rust seed interpreter** (aarch64 Linux; no self-hosted binary
exists for this triple). Seed-interpreted, not self-hosted — this is a defect
measurement, not a gate PASS.

Simple output (96x64, 6144 px): `#112233` x2773, `#445566` x3200 at (8,8)-(87,47)
— exactly the declared 80x40 box at the default 8px body margin — plus 171 px of
antialiased glyphs for the `main` text. checksum 26302749665251.

| | JS `#445566` px | JS `#112233` px | mismatch vs Simple | JS checksum |
|---|---|---|---|---|
| before | 0 | 0 | **6144 / 6144** | 26296152649728 |
| after  | 3200 | 5973 | **171 / 6144** | 26302836163968 |

All 171 residual mismatches lie in bbox (8,49)-(49,61) and every one is
`Simple=<antialiased glyph shade> -> JS=0xFF112233`.

## Fix

Added `renderImageTaskbarCommand()` (body fill + the 80x40 titlebar box, authored
from the fixture HTML) and made the fallthrough `throw new Error("unsupported
scene: …")`. A scene this oracle does not model is now absence of evidence, not a
fabricated frame. All 16 scene names still render (0 broken); an unknown scene
exits 1.

## Residual (open, not papered over)

The 171 text pixels cannot be closed by a hand-authored JS oracle: the Simple side
rasterizes real TTF glyphs with antialiasing (13 distinct shades). Reproducing them
in JS would either be a different font — a larger mismatch — or a transcription of
the Simple output, which is the tautological baseline the gate deliberately rejects
via `baseline_source`. Either this scene needs a text-free variant, or it needs the
`SIMPLE_WEB_ENGINE2D_BASELINE_ARGB_IN` transport that the six layout scenes use,
which trades exactness for non-independence. Left red and honest.

## Host note (why this went unseen)

`aarch64-unknown-linux-gnu`. Measured 2026-09-06:

- `bin/release/aarch64-unknown-linux-gnu/simple --version` -> "this Rust-built
  Simple binary is a bootstrap seed only", so `is_rust_seed_simple` classifies it
  forbidden. That verdict is **correct**, not a false negative.
- All tracked stage binaries are Mach-O arm64 (macOS):
  `./bootstrap/stage3/simple --version` -> rc=126, "cannot execute binary file:
  Exec format error".
- `command -v bun chromium google-chrome electron xvfb-run Xvfb` -> all empty.
  `node` is present.
- `sh scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs` ->
  `ERROR — nothing was checked (simple-bin-forbidden)` (rc=2).

So the browser-backed and self-hosted lanes are genuinely unrunnable here; the
missing capability is a pure-Simple `aarch64-unknown-linux-gnu` binary, which needs
a bootstrap deploy. The CPU layout/paint path itself needs neither a browser nor a
display and was exercised end to end under the seed interpreter.

## Simple renderer: no geometry defect; a text-raster divergence IS open

Geometry probes at 96x64, backend `software`. All correct:

| probe | result |
|---|---|
| 10x10 `#ff0000` at margin 0 | exactly 100 px at (0,0)-(9,9) |
| 200px-wide box in a 96px viewport | clipped to 960 px = 96x10 |
| 200px-tall box in a 64px viewport | clipped to 640 px = 10x64 |
| `width:0;height:0` box | not painted; background only |
| bare `<main>hello</main>`, bg-only body | text rendered (14 colors), not blank |

**But the two public entry points of this renderer disagree on text** for byte-identical
input (same HTML, 96x64, backend `software`). Reproduced in a single process, both
orders, deterministic — so it is not first-call font-cache warm-up:

| entry point | distinct | text px | text bbox | checksum |
|---|---|---|---|---|
| `simple_web_engine2d_render_html_pixels(html, 96, 64, "software")` | 3 | 252, hard `0xFF000000` | (11,52)-(58,63) | 26302553201484 |
| `SimpleWebEngine2DStaticPixelCache.create(96,64,"software").pixels_for_html(html)` | 15 | 171, antialiased (13 shades) | (8,49)-(49,61) | 26302749665251 |

Both paint the identical 3200 px `#445566` titlebar box at (8,8)-(87,47), so box layout
agrees; only the glyph run differs — origin (x 11 vs 8, y 52 vs 49), extent (47x11 vs
41x12) and raster (hard-edged vs antialiased). One of the two is wrong and neither has
been established as the reference.

**Observed and reproduced, not diagnosed.** It matters for the gates because the gate
fixture uses the cache path, so any oracle or baseline authored against the direct path
is measuring a different renderer. Not chased further in this lane.

## Also found, not fixed here (gate reporting, other lane)

`check-budgeted-simple-web-engine2d-scene-matrix-bitmap-evidence.shs` invokes
`scripts/check-node-simple-web-engine2d-*.shs` — missing the `check/` path
segment. Those files do not exist. The sibling layout matrix gate uses the correct
`scripts/check/...`.
