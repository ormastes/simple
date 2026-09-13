# Chrome Dynlib Feature Expert

## Role

Own process knowledge for the **CEF-backed Chrome dynlib render module**:
loading an embeddable Chromium (CEF, BSD-3) as a host-process shared library
through the existing SFFI dynlib facade, compositing its offscreen BGRA
frames through Engine2D onto Vulkan, and driving the shared 4K-lane HTML/CSS
catalog across seven tabs for receipts comparable to the Simple web
renderer's own.

## Feature Links

- Requirements/goal: `.spipe/chrome_dynlib_vulkan_render/state.md`
- Research (authoritative): `doc/01_research/ui/chrome_dynlib/chrome_dynlib_vulkan_render_module_2026-09-11.md`
- Plan: `doc/03_plan/ui/chrome_dynlib/chrome_dynlib_vulkan_showcase_plan.md`
- Related campaign: `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md`
  § "CPU<->GPU boundary fix campaign" (Simple-side Vulkan path this composites onto)
- Landed: PR #530 `land/chrome-dynlib-showcase-2026-09-11`

## Key facts

- **CEF is the only viable candidate**: real Chromium, a shared library, with
  accelerated offscreen output. Headless-shell is a process not a library;
  Ultralight/Servo/WKWebView are not Chrome.
- **A "chrome dynlib" already existed as a broker, not the real thing**:
  `libsimple_chromium_primitive_oracle` spawns a pinned Electron and returns a
  CPU capture — reused for its LOAD PATTERN, not its rendering.
- **Load pattern (reused verbatim)**: `chromium_reference_oracle_sffi.spl:236-287`
  — sha256-before, `DynLib.load` + exact symbol set, sha256-after,
  `spl_wffi_call_i64`, `spl_dlclose`, `*_into(buf, cap)` out-params.
- **C shim required**: CEF delivers frames via callbacks (`on_paint`); repo FFI
  calls only forward host->library. A Simple twin of the shim's pure logic is
  required for the dual-run shadow gate (`scripts/check/check-dual-run-shadow.shs`).
- **New ABI v1**: sibling of the oracle's frozen 5-symbol ABI, same nm-exact
  symbol-set discipline, disjoint `simple_chrome_render_` prefix (e.g.
  `simple_chrome_render_event`, `simple_chrome_render_read_pixels_into`).
- **v1 frame path is CPU BGRA**: Engine2D Vulkan only accepts CPU
  `pixels: [u32]` (`engine2d/backend_vulkan.spl:176`) — no external-memory
  import yet, same zero-copy gap as the gpu_offload_check campaign.
- **Catalog reuse**: drives the 4K lane's `web_renderable_feature_inventory.spl`
  (7 tabs, shared composer); owner: `.spipe/web_renderer_vulkan_4k_showcase_hardening`.
- **Sabotage discipline**: green/red/green proven by renaming
  `simple_chrome_render_event` out of a built copy (call fails, exit 1).
- **`spl_wffi_call_i64_into_bytes` facade (2026-09-11)**: wraps the real
  `read_pixels_into` out-param call; on a stub library `call_rcs=-4,2,2,2,2,2,2,2`
  is the stub signature, not a Vulkan failure.

## Blocked/deferred rows (never claim passed)

`renderdoccmd` absent -> RenderDoc rows `blocked`; Chrome ANGLE Vulkan
unavailable on macOS -> `vulkan-angle-unavailable` (resume on Linux); zero-copy
GPU handover deferred. Verdicts: `passed`/`failed`/`environment-blocked`/
`could-not-complete-in-time`; Chrome availability alone is never Vulkan proof.

## Pixel diff vs real Chrome (2026-09-12)

`sh scripts/check/check-chrome-catalog-pixel-diff.shs [--out DIR] [--selftest]`
drives Chrome headless + the pure-Simple web lane over
`examples/06_io/ui/web_catalog/*.html`, prints
`page= chrome_ms= simple_ms= mismatch_pct= max_delta=` per page and a
`PASS/FAIL/ERROR` verdict (0 pages = ERROR; no Chrome = ERROR naming the paths).
Differ: `src/app/ui/chrome_showcase/pixel_diff.spl` (pure Simple; PNG, BMP and
P6 PPM). `SIMPLE_BIN=<path>` is required from a git worktree.
Wire-in: `check-chrome-web-showcase-perf.shs --pixel-diff` (sets
`chrome_vs_simple_pixel_diff_status=chrome-compared`).

## RenderDoc capture diff (API-level sibling of the pixel diff)

Pixel diff answers "do the frames match"; `src/app/ui/renderdoc_diff/` answers "which
draw call diverged". Export both captures with
`scripts/tool/renderdoc-export-events.shs` (schema `renderdoc-events/v1`; the only
Python is the extended `renderdoc-qrenderdoc-python-smoke.py`), then
`scripts/check/check-renderdoc-web-diff.shs` prints `renderdoc_diff_status=`,
`renderdoc_diff_first_divergent=` and a class of `missing-draw|extra-draw|order|
output-mismatch|size-mismatch|format-mismatch`. Captures come from the Linux lane;
on macOS only `--selftest` (10 fixtures) runs. Guide:
`doc/07_guide/app/ui/renderdoc_web_diff.md`.

## RenderDoc diff lane + Linux lavapipe CI (2026-09-12)

`.github/workflows/renderdoc-web-diff.yml` produces RenderDoc `.rdc` captures
for both sides of the web differential on a GPU-less `ubuntu-latest` runner
using Mesa lavapipe as the software Vulkan ICD (RenderDoc captures lavapipe
fine). Deliberately **never a required check** — triggers are
`workflow_dispatch` plus a path-filtered `pull_request` only, so the slow CI
queue and the red baseline don't gate unrelated PRs. Local equivalent of the
diff step: `scripts/check/check-renderdoc-web-diff.shs` (see the RenderDoc
capture-diff paragraph already in this file).

## Geometry differ (2026-09-12)

`scripts/check/check-chrome-layout-geometry-diff.shs` +
`src/app/ui/chrome_showcase/layout_geometry_diff.spl` (spec
`test/01_unit/app/ui/layout_geometry_diff_spec.spl`) is a BUG-FINDER, not a
regression gate: per catalog page it keys Chrome headless's per-element
border-box geometry and the pure-Simple renderer's geometry on the same
body-relative nth-path, flags any `|dx|,|dy|,|dw|,|dh| > 1px`, clustered by
CSS feature. Chrome has no JS-eval flag in headless dump-dom mode, so the
harvest writes a walker-injected COPY of each page beside the original
(relative CSS/img URLs must still resolve; an iframe wrapper was rejected —
`file://` origins are opaque without `--allow-file-access-from-files`).
Verdict is the last stdout line; 0 elements compared or no Chrome is ERROR,
never PASS.

**Current mismatch table** (`doc/10_metrics/ui/chrome_layout_geometry_diff_macos_2026-09-12.md`,
Chrome 152.0.7977.83, tolerance 1px, interpreter `39368072 1789171430`):
overall **158 compared, 136 mismatched**. Per page (compared / root
mismatches / inherited / Chrome-elements-with-no-Simple-box): overview
18/9/5/0, html 28/16/5/403, css-layout 23/21/1/378, css-paint 25/22/2/503,
forms-media 27/22/2/76, animation 24/20/2/57. Read the full doc for the
remaining pages and root-cause clustering — do not re-derive counts by hand.

## Pixel differ zero-pixel-render fallback

`scripts/check/check-chrome-catalog-pixel-diff.shs` classifies an
all-background (uninked) captured image as `zero-pixel-render` rather than a
false "0% mismatch" pass — an all-background Simple frame and a real Chrome
frame can both read as trivially identical otherwise. `--selftest` (5
fixtures) asserts an inked image is never misclassified as zero-pixel-render
and that the differ discriminates. A run with any `zero-pixel-render` page is
FAIL, named per page, never silently averaged into the pass rate.

## Update Rule

Update this skill with new links, current ABI/symbol inventory, and handoff
notes BEFORE committing feature work.
