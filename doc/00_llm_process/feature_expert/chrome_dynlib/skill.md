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

## Update Rule

Update this skill with new links, current ABI/symbol inventory, and handoff
notes BEFORE committing feature work.
