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
  (TL;DR: `..._tldr.md`)
- Plan: `doc/03_plan/ui/chrome_dynlib/chrome_dynlib_vulkan_showcase_plan.md`
- Related campaign: `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md`
  § "CPU<->GPU boundary fix campaign" (owns the Simple-side Vulkan path this
  module composites onto)
- Landed: PR #530 `land/chrome-dynlib-showcase-2026-09-11` — "Chrome (CEF)
  dynlib render module, showcase + perf-check infra; honest vk2d bench verdict"

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
  (7 tabs, shared composer); ownership stays with
  `.spipe/web_renderer_vulkan_4k_showcase_hardening`.
- **Sabotage discipline**: green/red/green proven by renaming
  `simple_chrome_render_event` out of a built copy (call fails, exit 1); the
  unmodified library passes both sides.

## Blocked/deferred rows (never claim passed)

`renderdoccmd` absent on this host -> RenderDoc rows `blocked`; Chrome ANGLE
Vulkan unavailable on macOS -> `vulkan-angle-unavailable` (resume on Linux);
zero-copy GPU handover deferred to a separate lane. Verdicts are exactly
`passed`/`failed`/`environment-blocked`/`could-not-complete-in-time`; Chrome
availability alone is never Vulkan proof, and a missing
field/binary/library/zero-tab run is never `passed`.

## Update Rule

When research, plan, design, tests, implementation, verification, or release
artifacts for this feature change, update this skill with the new links,
current ABI/symbol inventory, and handoff notes BEFORE committing.
