# Web Render Backend — pure_simple vs chromium

One interface, two interchangeable web-render engines, so the *same* HTML can be
rendered (and compared) by Simple's own renderer or by real Chromium.

- **API:** `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl`
- **Sample app:** `examples/06_io/ui/web_render_backend_gui.spl`
- **Chromium helper:** `tools/web-render-backend/chromium_render.js`
- **WebGPU draw evidence helper:** `tools/web-render-backend/chromium-webgpu-draw/`
- **WebGPU compute evidence helper:** `tools/web-render-backend/chromium-webgpu-compute/`

## The interface

```spl
use std.gc_async_mut.gpu.browser_engine.web_render_backend.{WebRenderBackend}

val r = WebRenderBackend.create("pure_simple", w, h)   # or "chromium"
val pixels = r.render_html_to_pixels(html)             # [u32] 0xAARRGGBB  (comparison)
val opened = r.show_live_window(html_path)             # true for chromium (live window)
```

| backend | display | nature |
|---------|---------|--------|
| `pure_simple` | Engine2D raster frame in a winit window | Simple's HTML layout → Engine2D `auto` (Metal, CUDA/HIP, Vulkan, then CPU fallbacks). No browser. |
| `chromium` | **live, interactive** Electron `BrowserWindow` | real Chromium renders the live DOM. |

`render_html_to_pixels` produces a comparable buffer from **both** engines — this
is what the honest bit-level gate uses (pure-Simple ≡ Chromium OSR, `mismatch=0`).
Pure-Simple pixel artifacts stamp their `engine2d_backend` from the same
Engine2D `auto` resolution path used for rendering; do not hard-code default
artifact provenance as `software`.
Pure-Simple GPU paint is opt-in with `SIMPLE_WEB_GPU_PAINT=1`. The default path
uploads the completed CPU layout image to Engine2D because small or residual-heavy
pages can lose more time to command/upload/readback traffic than they save on
device fill work. `web_gpu_paint_economics(frame, base)` is the local decision
helper: it compares total CPU paint plus upload/readback cost against primitive
fill commands plus residual upload cost, and only returns an offload win when
estimated total work is lower. Solid-only pages build the frame from fill ops; mixed pages
still keep CPU ground truth for residual parity. The forced GPU paint path
predicts the residual from the local fill list, so it avoids an extra full-frame
GPU readback before the final pixel-returning API readback. The deterministic
policy gate is
`test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl`.
The browser backend keeps a retained one-entry pixel artifact cache for
unchanged static full HTML at the same viewport and resolved backend. Requests
with `data-simple-dynamic`, `data-live`, `data-ui-patch`, or WebSocket JS bypass
that retained cache and render directly.
`show_live_window` opens each backend's native window (chromium = live DOM;
pure_simple has no live shell and returns false so the caller presents pixels).

## WebGPU evidence boundary

`WebRenderBackend("chromium")` is not the Chrome WebGPU proof path. It renders
HTML through Electron offscreen and returns comparable pixels for web-renderer
parity. Use `std.gc_async_mut.gpu.browser_engine.chrome_webgpu_draw_evidence`
and `tools/web-render-backend/chromium-webgpu-draw/` when the requirement is
Chrome/Electron WebGPU drawing. That wrapper reports either positive adapter,
non-fallback adapter, device, pipeline, draw, capture, and pixel evidence, or a
deterministic `host-unavailable:*` status without falling back to Simple
software replay. For WASM-originated Simple3D evidence, use
`chrome_webgpu_draw_wasm_simple3d_triangle_payload_evidence`; it parses
`simple3d:canvas:w,h:triangle:x1,y1,z1,x2,y2,z2,x3,y3,z3:rgba:r,g,b,a`,
converts RGB to `#rrggbb`, and records payload byte/checksum provenance even
when the host reports unavailable WebGPU.

For in-process browser Simple-script drawing evidence, use
`canvas_get_context_simple2d` or `canvas_get_context_simple3d` from
`std.gc_async_mut.gpu.browser_engine.script.canvas_api`. Those facades prove the
Simple browser command capture and software-replayed WebGPU submit path. The
Simple3D facade records scene payload bytes/checksum and submission counters; it
does not prove Chrome/Electron hardware-backed WebGPU pixels.

## Running the sample (macOS)

```bash
# pure-Simple raster window (Engine2D auto backend; explicit software remains available)
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl pure_simple 384x288
# live Chromium window (real DOM, interactive) — viewport arg sets CSS width
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl chromium 1280x960
```

A `WxH` argv sets the CSS viewport (the page lays out at desktop width so fonts are
proportional); the result is downscaled to the window. A `.html` argv overrides the
page (default: `test/09_baselines/web_html_input/vanillastyle_demo.html`).

## Performance note (pure_simple)

The pure-Simple raster runs interpreted and is canvas-bound. Two O(n²) traps were
fixed (see `doc/08_tracking/bug/pure_simple_web_render_interpreter_bound_2026-06-06.md`):
1. heuristic-surface buffer built with a `push` loop → use `[0; w*h]` array-repeat;
2. the in-place array-write fix (`2d4579a0`) must be in the **running binary** —
   a stale `bin/simple` clones the framebuffer on every pixel write. Keep the
   driver current (rebuild on a stale deploy). Keep pure_simple viewports modest
   (≤ ~400 wide); chromium opens a live window and is unaffected.

## Honest comparison (no memorized pixels)

Use two **independently produced** artifacts + an absolute oracle, never hard-coded
captured pixels. Gate: `scripts/check/check-electron-simple-web-engine2d-bitmap-evidence.shs`
(pure-Simple Engine2D vs real Chromium OSR → `mismatch_count=0`).

**Draw-IR structured items (2026-07-06).** The optimized Engine2D Draw-IR
executor (`draw_ir_adv.spl`) now renders HTML/CSS box structure — box-shadow,
background (solid or linear-gradient), corner-radius, and per-side borders — via
the existing backend primitives, instead of collapsing each box to one flat
`draw_rect_filled`. Transparent-bg boxes that have a border or shadow now paint.
`<img>`/background-image is still not emitted as an image op (blocked:
`doc/08_tracking/bug/engine2d_draw_ir_image_path_no_resolver_2026-07-06.md`).
Honest backend caveats a comparison must respect: Vulkan `line`/`circle_outline`/
`rounded_rect` are empty-shader no-ops, Metal `clip` is a no-op, and `cpu_simd`
is the SIMD-instrumented CPU lane with native x86 row evidence, exact
scalar-compatible RVV rows, and
native-row proof required where enabled. Coverage plan +
baseline: `doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md`.

For GUI/web/2D Vulkan verification on macOS, run the stronger comparison through
the RenderDoc setup wrapper. This top-level runbook is macOS-only until Windows
and Linux get separate host notes. It exercises the same fixture across
Electron Chromium, original Chrome, and pure-Simple Engine2D Vulkan, then
records whether each lane produced Vulkan-backed evidence or fell back:

```bash
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

On macOS, `vulkaninfo --summary` with `driverName = MoltenVK` only proves the
host loader/ICD. Electron or Chrome can still render a bitmap while rejecting
`--use-angle=vulkan`; in that case evidence records
`vulkan-angle-unavailable` and the browser Vulkan lane remains failed. The
wrapper records whether the Simple lane used a repo-local self-hosted driver in
`gui_web_2d_vulkan_simple_bin_selection_reason` and
`gui_web_2d_vulkan_simple_bin_status`; Rust seed binaries are recorded as
forbidden and are not executed for this lane. RenderDoc proof requires
`.rdc` files with `RDOC` magic for the Electron, original Chrome, and Simple
capture lanes; browser bitmaps alone are not Vulkan proof.
The aggregate audit emits `gui_web_2d_vulkan_direct_run_source` and
`gui_web_2d_vulkan_direct_run_evidence_env` so direct runtime comparison fields
can come from a real `--run` env even when the setup env is readiness-only.

For host/GPU lane event-flow and less-ms evidence around
`target.later(...) gpu \:`, use
`doc/09_report/perf/host_gpu_lane_event_flow_perf_evidence_2026-06-14.md`.
That lane records `Engine2dHostGpuEventFlowEvidence`, Draw IR rendered-command
counts, pixel/readback hashes, fallback state, and p50/p95 baseline-vs-candidate
timings. Do not count fallback-only or smoke-size software runs as a real GPU
speedup.

For 8K GUI/web/2D performance claims, keep a retained 8K evidence row in
`doc/09_report` or `doc/10_metrics` that names viewport, backend, binary/source
revision, readback mode, p50/p95 timing, RSS or memory budget, fallback state,
and checksum/readback proof. If the host cannot produce the row, record an
explicit blocker such as `8k-host-unavailable`; do not convert a small viewport,
software fallback, or cached replay into an 8K pass.

Before accepting GUI/web/2D implementation, wrapper, benchmark, or platform
agent patches, run the diff-scoped source-coupling guard:

```bash
sh scripts/check/check-rendering-source-coupling.shs
```

For a specific jj change, set `RENDERING_SOURCE_COUPLING_REVISION=<rev>`. The
guard rejects new raw `rt_*` calls, direct backend proof/status pokes, and forced
backend pass states in rendering-scoped files. The only raw RenderDoc helper
exception is the canonical `scripts/tool/renderdoc-evidence.shs` path.

For Metal claims, only macOS native raw Metal readback is proof. Linux and other
non-macOS hosts must report `metal-requires-macos`, not a Metal pass. A Metal
claim without raw readback, backend handle, and checksum/readback provenance is
only a host capability note, not GUI/web/2D production evidence.

See also: [`web_render_backend_tldr.md`](web_render_backend_tldr.md).

## Production Browser Hardening

Simple Web production checks combine renderer parity with web-boundary auth
evidence. The canonical live renderer parity gate is:

```bash
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

Production evidence should use the in-tree Simple release binary or an explicit
`SIMPLE_BIN=...` override. The Electron generated-GUI and Simple Web layout
evidence wrappers only use `command -v simple` when the caller deliberately
sets `ALLOW_PATH_SIMPLE_BIN=1`; otherwise missing in-tree Simple binaries remain
fail-closed as `missing-simple-bin`. The wrappers emit
`*_simple_bin` and `*_simple_bin_source` so reports can distinguish
`explicit-env`, `in-tree-release`, `repo-bin`, `path-opt-in`, and
`default-missing` evidence.
The Node/Web bitmap parity wrapper follows the same fail-closed contract under
`js_web_render_bitmap_simple_bin*`: it selects only self-hosted Simple binaries
from the repository by default, records missing binaries as `simple-bin-missing`,
and records any `src/compiler_rust/**` override as `simple-bin-forbidden`
without executing the seed.
The Simple Web Engine2D JavaScript bitmap wrapper uses the matching
`simple_web_engine2d_js_simple_bin*` fields. A Web/Engine2D bitmap parity row is
not production evidence unless `simple_web_engine2d_js_simple_bin_status=pass`
and the source is a self-hosted or explicit non-seed Simple binary.
The Chrome HTML compatibility geometry manifest uses generic summary fields
`simple_bin`, `simple_bin_source`, and `simple_bin_status`; Chrome geometry
manifest evidence is not production evidence if that status is `missing` or
`forbidden`.
The single-fixture Electron HTML compatibility geometry wrapper writes the same
generic fields to `evidence.env`; an Electron geometry row is not production
evidence if `simple_bin_status` is `missing` or `forbidden`, even if Electron
itself could capture the fixture.

The renderer parity wrapper also runs the Electron/Chromium event-routing probe
before a top-level pass. Saved evidence must include
`production_gui_web_renderer_parity_event_routing_status=pass`, readiness and
WM discovery flags, focus/move/maximize/title-command/text-input/pointer
counts, `production_gui_web_renderer_parity_event_routing_performance_now_available=true`,
`production_gui_web_renderer_parity_event_routing_performance_now_delta_ms>0`,
`production_gui_web_renderer_parity_event_routing_input_to_paint_ms>0`,
`production_gui_web_renderer_parity_event_routing_animation_frame_count>=2`,
`production_gui_web_renderer_parity_event_routing_css_animation_probe=true`, and
`production_gui_web_renderer_parity_event_routing_blur_or_tolerance_used=false`.
This keeps a visually correct capture from passing when visible controls no
longer receive DOM events or the browser timing, input-to-paint, and animation
loop are not proven.

The focused Electron MDI wrapper follows the same rule for the live
Electron/Chromium shell: `electron_mdi_interaction_latency_status=pass` and
`electron_mdi_input_to_paint_ms>0` are required alongside event routing,
screenshot binding, `performance.now()`, and animation-frame proof.

The focused production web endpoint gate is:

```bash
bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360
```

Production clients should pass bearer tokens through the WebSocket subprotocol
instead of `/ui/ws?token=...`. Query-string bearer extraction is rejected by
default and remains non-authorizing even when
`SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` is present. Legacy `/ws` is hidden with
`404`; canonical `/ui/ws` requires an origin-bound bearer. The selected release
scope is Feature Option C plus NFR Option C. macOS Metal, AMD ROCm/HIP, Windows
DirectX, and real browser WebGPU native device-readback rows require native host
evidence. Linux-only runs may record deterministic `host-unavailable` verdicts
but must not translate them into native pass claims.

## Chrome WebGPU Evidence Helpers

`std.gc_async_mut.gpu.browser_engine.chrome_webgpu_draw_evidence` is the
canonical host-adaptive draw probe for real Chromium WebGPU pixels.
`std.gc_async_mut.gpu.browser_engine.chrome_webgpu_compute_evidence` is the
matching processing probe for real Chromium WebGPU compute readback. The
compute helper accepts compiler-emitted WGSL through `CWC_WGSL_SOURCE` and can
run both `u32_add` and `simple2d_fill` operations. For WASM-backed Simple2D
processing evidence, use
`chrome_webgpu_compute_wasm_simple2d_fill_payload_bytes_evidence(...)` so the
evidence carries the payload byte count and checksum beside the WGSL source
metadata.
