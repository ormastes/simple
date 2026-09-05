# GUI → Web → 2D Rendering Path Assessment

**Date:** 2026-06-12
**Status:** Research / Read-only
**Scope:** src/app/ui, src/app/ui.web, src/app/ui.browser, src/lib/gc_async_mut/gpu/browser_engine, src/lib/gc_async_mut/gpu/engine2d
**CI host:** Linux, lavapipe Vulkan ICD, no NVIDIA/AMD GPU, no Metal

---

## 1. Actual Call Chain: GUI App to Pixels

### Entry Layer — `src/app/ui/`

`src/app/ui/main.spl` (334 lines) calls `run_ui_backend_dyn` (backend_loader.spl:73 lines).
Backend detection in `detect.spl` (103 lines) selects one of:
- `backend_entry_web.spl` → `run_web_with_access_store(...)` (6-line stub invoking binary subprocess)
- `backend_entry_browser.spl` (6-line stub)
- `backend_entry_electron.spl` → `run_electron(...)` (6-line stub, subprocess)
- `backend_entry_tauri.spl` (6-line stub)
- `backend_entry_headless.spl` (6-line stub)
- `backend_entry_render.spl` (27 lines): `parse_render_args → create_session → execute_render → export_to_file`

All `backend_entry_*.spl` stubs are 6 lines — they only invoke a subprocess via `rt_process_run` / `_simple_binary`.
The _actual_ render logic lives downstream in `ui.web` or `ui.browser`.

**Seam 1 — UISession / backend dispatch:** `backend_loader.spl`:
```
pub fn run_ui_backend_dyn(backend, file_path, port, access_db_path) -> i64
pub fn run_ui_cli_backend_dyn(file_path, port, access_db_path, sub_args) -> i64
```
Detection at runtime (`detect.spl`): checks `has_display`, `is_macos`, `has_electron_shell`, `has_tauri_shell`, `is_windows`, `rt_file_exists(simple_bin)`.

### Web Layer — `src/app/ui.web/`

Key files (wc -l):
- `taskbar_runtime.spl` (+ part1/part2): main taskbar UI logic
- `server.spl`: HTTP + WebSocket server, file-watch loop
- `render_cache.spl`: SHA-256-keyed static-frame pixel cache
- `backend.spl`: `WebRenderBackend` wrapper; `web_render_html_request_to_pixel_artifact_with_backend`
- `retained_renderer.js`: JavaScript side (retained DOM, diff-patch protocol)

**Seam 2 — web_render_backend.spl (181 lines):**
```
class WebRenderBackend:
    backend: text    # "pure_simple" | "chromium" | "cpu_simd" | ...
    width: i32
    height: i32

fn render_html_to_pixels(self, html: text) -> [u32]:
    if self.backend == "chromium":
        return _render_html_via_chromium(html, self.width, self.height)
    return simple_web_render_html_to_pixels_with_engine2d_backend(html, self.width, self.height, "cpu_simd")
```
The `chromium` path shells out to Chromium/Electron via `rt_process_run`. All other backends
go through the pure-Simple engine path.

**Render cache** (`render_cache.spl`): `static_frame_matches` + `render_cached_static_frame` gates reuse on SHA-256
of HTML + UIState revision. `render_frame` checks cache before calling `compute_layout → layout_to_scene → paint`.

### Browser/Renderer Layer — `src/app/ui.browser/`

- `backend.spl`: "BrowserBackend → BrowserRenderer (browser_engine) → Engine2D (engine2d)"
  (per file header comment)
- `renderer.spl`: `browser_semantic_render_ipc_json(state, viewport_w, viewport_h)`:
  `generate_css(theme) → render_html_tree(root_node, state) → web_render_ipc_json_with_html_and_semantic`
- `dom_bridge.spl`, `event_bridge.spl`: DOM ↔ widget tree bridge

### Core Render Path — `src/lib/gc_async_mut/gpu/browser_engine/`

Total: ~8,280 lines across 29 files; `simple_web_html_layout_renderer.spl` alone is 4,328 lines.

**Call chain from `render_html_to_pixels`:**

```
WebRenderBackend.render_html_to_pixels(html)
  └─ simple_web_render_html_to_pixels_with_engine2d_backend(html, w, h, "cpu_simd")
       └─ _render_engine2d_surface_pixels(html, w, h, backend_name)
            └─ simple_web_engine2d_render_html_pixels(html, w, h, backend_name)
                 [in simple_web_engine2d_renderer.spl, 1082 lines]
                 ├─ SimpleWebEngine2DStaticPixelCache.get(html)  -- SHA equality check on last_html
                 ├─ Heuristic path (generated/widget HTML):
                 │    simple_web_render_html_software_pixels(html, w, h)  -- heuristic surface
                 │    [SimpleWebHeuristicSurface in simple_web_engine2d_renderer.spl]
                 └─ Layout path (real CSS):
                      simple_web_layout_render_html_pixels(html, w, h, backend_name)
                           └─ simple_web_layout_render_html_software_pixels(html, w, h)
                                [in simple_web_html_layout_renderer.spl, 4328 lines]
                                parse HTML → flat node arena
                                → CSS cascade (inline + <style> block)
                                → block-flow layout (word-wrapped)
                                → paint text+boxes into [u32] framebuffer
                                   using 5×7 bitmap font (render_text_to_buffer)
                                → returns [u32] pixel buffer
```

For non-software Engine2D backends (Vulkan/CPU-SIMD), the layout renderer output
is blitted into an `Engine2D` session and then `read_pixels()` is called:

```
Engine2D.create(w, h)  [engine.spl, 772 lines — dispatches to CpuBackend/VulkanBackend/etc]
  .clear(bg_color)
  .draw_rect_filled(...)   -- per paint command
  .draw_text(...)          -- delegates to render_text_to_buffer (5×7 bitmap)
  .present()
  .read_pixels() -> [u32]
```

**Seam 3 — Engine2D / RenderBackend trait** (`engine2d/backend.spl`):
```
trait RenderBackend:
    me clear(color: u32)
    me draw_rect(x, y, w, h, color)
    me draw_rect_filled(x, y, w, h, color)
    me draw_line(x1, y1, x2, y2, color, thickness)
    me draw_circle(cx, cy, r, color)
    me draw_rounded_rect(x, y, w, h, radius, color)
    me draw_gradient_rect(x, y, w, h, top_color, bottom_color)
    me draw_text(x, y, text_val, color, font_size)
    me draw_image(x, y, w, h, pixels: [u32])
    me set_clip / clear_clip / set_mask / clear_mask
    me present()
    fn read_pixels() -> [u32]
trait Engine2DExtended:
    me draw_text_bg(x, y, text_val, fg, bg, font_size)
```
Implemented by: `SoftwareBackend`, `CpuBackend` (SIMD hot rows), `VulkanBackend`,
`CudaBackend`, `RocmBackend`, `MetalBackend`, `OpenGLBackend`, `OpenClBackend`,
`DirectXBackend`, `WebGpuBackend`, `VirtioGpuBackend`, `BaremetalBackend`, `IntelBackend`, `QualcommBackend`.

**Present → pixels path:**
`engine.present()` flushes the backend surface. `engine.read_pixels() -> [u32]` returns the
ARGB framebuffer. `backend_screenshot_capture.spl` (218 lines) wraps this as a parity-test
capture facade (`capture_with_backend`, `backend_capture_ok`, `backend_capture_perf_report_sdn`).

**Bypass for software/cpu:**
`simple_web_layout_render_html_pixels` returns the software framebuffer **directly** for
`software`/`cpu` backends — the Engine2D blit+present+read_pixels round-trip is skipped
(added in the O(n²) fix wave; see bug doc section 3 below).

---

## 2. Missing or Too-Thin Libraries

### 2.1 TTF / Proportional Font Metrics — CRITICAL GAP

**Confirmed missing:** The production path uses a **5×7 bitmap font** (`engine2d/glyph.spl`, 326 lines):
```
fn render_text_to_buffer(buf, buf_w, buf_h, x, y, text_val, color, font_size):
    val scale = if font_size <= 7: 1 else: (font_size / 7)
    val advance = glyph_advance(scale)   # glyph_width()+1, integer-scaled
    ...
```
All backends use `render_text_to_buffer` which maps `draw_text` calls to this bitmap.

The `text_painter.spl` (302 lines) provides layout estimates via `_estimate_char_width_base`,
a per-character lookup table returning integers (e.g., `"Translate" → 77px` hardcoded).
Word widths are computed character-by-character with no kerning or shaping.

`spl_fonts` / `fontdue` is wired at the Rust runtime layer and exposes `bearing_y` (verified
as `Metrics.ymin`, not `GlyphPosition.y` — see bug doc `simple_web_renderer_ttf_glyph_metrics.md`).
The `fontdue` horizontal line metrics are exposed through `spl_fonts` but **BrowserRenderer's
non-layout text helper still uses the old `bearing_y` semantic incorrectly** (partially fixed).
No proportional advance-width or kerning pair data surfaces to the Simple layout layer.
Bug: `simple_web_renderer_ttf_glyph_metrics.md` (open).

**Consequence:** text layout widths diverge significantly from Chrome metrics.
`test/09_baselines/famous_site_corpus/site_0_google/chrome_metrics.json` provides ground truth;
measured mismatches tracked in spec failures.

### 2.2 Image Decode — MISSING

No PNG/JPEG/WebP decode exists in the browser_engine or engine2d paths.
`draw_image(x, y, w, h, pixels: [u32])` exists in the `RenderBackend` trait but requires the
caller to supply a pre-decoded `[u32]` pixel buffer. `stb_image.h` is present in `src/runtime/`
but no Simple binding for it appears in browser_engine or engine2d.
`layout_renderer.spl` handles `has_icon_image_class` nodes (line 4078) as colored placeholder
boxes, not actual image data.

### 2.3 Retained Scene Graph / Display List — MISSING

There is no retained scene graph between frames. Each render call rebuilds:
`HTML text → DOM arena → CSS cascade → layout tree → paint commands → [u32]`.
The only frame-level reuse is the `SimpleWebEngine2DStaticPixelCache` (last_html equality check)
and the `render_cache.spl` SHA-256 keyed static frame cache — both are whole-frame pixel cache
hits, not sub-tree invalidation. No display list, no scene tree diffing, no layer compositing.

### 2.4 Damage Tracking / Dirty-Rect Invalidation — THIN

`backend_software.spl` (757 lines) has `dirty_tiles: [bool]` per-tile tracking at line 61,
updated at line 144 and cleared at line 464. However, this tracks draw-call tiles within a
single `SoftwareBackend` session — it does **not** propagate up to the layout/HTML layer.
Above `Engine2D`, there is no concept of a dirty region: every render is a full-page repaint.

### 2.5 Text Shaping — ABSENT

No Unicode BiDi, no ligature shaping, no harfbuzz or similar. The bitmap font covers A-Z/a-z/0-9
plus common ASCII punctuation. Non-ASCII characters fall back to "filled 5×7 block" (glyph.spl:39).

### 2.6 WebGPU Path — STUB / THIN

`webgpu_context.spl` (180 lines) and `webgpu_software_executor.spl` (20 lines) exist but
`webgpu_software_executor` is essentially a stub. `backend_webgpu.spl` (627 lines) is present
in engine2d but the WebGPU context integration with browser_engine is minimal.
`webgpu_resources.spl` (29 lines) is nearly empty.

### 2.7 Compositor / Layer Model — ABSENT

No separate compositor layer. There is no `viz`/`cc`-equivalent layer tree, no GPU surface
management, no z-order compositing beyond paint-order in the layout traversal, no scroll
management layer.

---

## 3. Optimizations That Matter Most (ranked)

### #1 — Interpreter-Bound Layout + Text: ~1.2–1.6 s per frame in interpreter mode

**Bug:** `pure_simple_web_render_interpreter_bound_2026-06-06.md` (open for compiled path)

Measured at 320×240, 1 frame:
- Layout without text: ~244,408 µs
- Layout with text (before cleanup): ~1,557,688 µs
- Layout with text (after char-code glyph / packed rows fix): ~1,214,473–1,286,654 µs

The API spec test runs 11 cases in **71,354 ms** (interpreter, 2026-06-05 measurement).
Root cause split:
- **Path A (heuristic surface O(n²))** — FIXED (commit `9900d2de`): `[0u32; w*h]` array-repeat replaced quadratic init
- **Path B (layout renderer O(n²))** — FIXED for `software`/`cpu` backend (direct return, no blit round-trip);
  but compiled-JIT path crashes (W1006 mut-capability; `simple_web_html_layout_renderer.spl` triggers
  a compiled-path segfault in the Cranelift backend — repro: importing the renderer module alone via probe
  causes crash under `--mode=native`/JIT).

Until the compiled crash is fixed, **all layout rendering runs in interpreter mode** at ~1.2 s/frame
for typical content. This is the single largest bottleneck.

### #2 — Per-Frame Full Relayout: no incremental invalidation

Every HTML change triggers parse → CSS cascade → full block-flow layout → full repaint.
`simple_web_html_layout_renderer.spl` is 4,328 lines with no subtree memoization.
CSS cascade (`simple_web_engine2d_renderer.spl`) re-evaluates all selectors for all nodes per frame.
The selector cache in the heuristic path (class/id bucket) avoids some O(n) work but the layout
renderer has no equivalent selector result cache.

### #3 — Text Width Estimation vs. Real Metrics: layout accuracy bound

`_estimate_word_width_px` sums `_estimate_char_width_base` per character (loop over text.len()).
For a page with N text nodes each of length L, this is O(N·L) string operations in interpreter mode,
each involving `value.substring(i, i+1)` allocation (known string copy cost in interpreter).
The known workaround (char_code_at + no substring for normal text, packed glyph rows) cut cost from
1,557,688 µs to ~1,214,473 µs but the core approach remains substring-per-char.

### #4 — GPU Text Upload Inefficiency: full-framebuffer re-upload per draw_text

All GPU backends (CUDA, ROCm, Metal, Vulkan) use `_gpu_draw_text_fallback`:
1. Download entire framebuffer from device to host if `backend.dirty`
2. Call `render_text_to_buffer` (CPU bitmap render) on host buffer
3. Re-upload **entire** framebuffer to device

For a 1920×1080 framebuffer that is `1920 * 1080 * 4 = ~8 MB` per draw_text call.
Comment in each backend: "for production, upload only the dirty rect" — not yet done.

### #5 — CSS Cascade Performance: selector bucket miss + sort per render

Commit `c244d01c591` (2026-06-12) added `_selector_specificity` helpers and a stable insertion-sort
for CSS cascade rule ordering. While correctness-critical, the insertion sort is O(n²) in the number
of matched rules per node. For pages with many CSS rules this matters.
22 residual spec failures remain (bug: `browser_renderer_spec_sequence_failures_2026-06-11.md`):
- Cluster 1: sequence-dependent (module-level cache state leaks across `it` blocks)
- Cluster 2: `:has(> .badge)` direct-child — `normalize_child_combinators()` rewrites `>` inside
  functional pseudo args (depth-blind), breaking the `starts_with("> ")` recovery downstream.

---

## 4. CPU→GPU Migration Readiness

### What Is Already Backend-Portable

The `RenderBackend` trait (engine2d/backend.spl) cleanly abstracts all drawing:
`clear`, `draw_rect`, `draw_rect_filled`, `draw_line`, `draw_circle`, `draw_rounded_rect`,
`draw_gradient_rect`, `draw_text`, `draw_image`, `set_clip`, `clear_clip`, `set_mask`,
`clear_mask`, `present`, `read_pixels`.

The paint-command layer (`paint.spl`, 127 lines; `paint_commands_to_scene` in browser_engine2d_bridge.spl)
translates `PaintCommand` objects (`fill_rect`, `image`, text_run, etc.) to `Engine2D` calls.
This means **all geometry ops are already backend-portable** — switching from
`SoftwareBackend` to `VulkanBackend` or `CpuBackend` (SIMD) requires only the backend name string.

The bypass path (`simple_web_layout_render_html_software_pixels` for software/cpu) short-circuits
the Engine2D pipeline, but only for those two backends — the general path through Engine2D is
architecture-correct.

### What Needs API Shape Changes for GPU Efficiency

1. **Text: atlas-first API** — `draw_text(x, y, str, color, size)` forces each backend to decide
   independently how to rasterize. A `draw_glyph_run(atlas_id, glyphs: [GlyphSlot])` API would
   let Vulkan/Metal/WebGPU sample a pre-uploaded texture atlas and eliminate the CPU fallback.
   Currently all GPU backends do: download → CPU render → re-upload (full FB).

2. **Dirty-rect upload** — `draw_image` and `draw_text` should accept an optional dirty-rect
   `(x, y, w, h)` so GPU backends upload only the affected region. Trait extension:
   `me upload_rect(x, y, w, h, pixels: [u32])`.

3. **Paint command stream instead of immediate calls** — the `Engine2DCommandStream` concept
   (referenced in the detail design doc `accelerated_shared_ui_backend_architecture.md`) would let
   a GPU backend batch all primitives into one submit. Today each `draw_rect_filled` is an
   immediate call. Batching is already done for the heuristic-surface path (scene commands),
   but not for the layout path.

4. **Frame delta / partial repaint** — `render_frame` in `render_cache.spl` checks whole-frame
   cache but has no sub-tree invalidation. A `dirty_subtree_id` parameter in the UIState would
   let the GPU path skip unchanged layers. No API surface for this exists yet.

5. **Typed bypass evidence** — the design doc notes: "native-renderer bypass: adapters should
   expose `reached_engine2d` + fallback reason as typed results." Currently the bypass is implicit
   (string name comparison). Typed capability evidence (e.g., `RenderPathKind { Software | Engine2D | GPU }`)
   would make the fast path queryable and testable.

---

## 5. Concrete Small-Task List (each ≤1 day)

### T1 — Fix `normalize_child_combinators` depth-blindness (≤4h)
**File:** `src/lib/gc_async_mut/gpu/browser_engine/selector_matcher.spl` (77 lines)
Track paren depth while scanning the selector string; skip rewriting `>` when inside
`(...)`. Re-run `browser_renderer_spec.spl` — expect `:has(> )` cluster (it-blocks ~22,24,
26,28,30,32-35) to flip green.
Closes part of bug `browser_renderer_spec_sequence_failures_2026-06-11.md`.

### T2 — Fix module-level cache cross-test state leak (≤4h)
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl` (1082 lines)
`SimpleWebEngine2DStaticPixelCache` is module-level state. Render the same fixture twice in
one process and diff pixels (per bug doc Next Steps §2). Change the cache to be
session-scoped (passed as argument) or reset between spec `it` blocks.
Closes the sequence-dependent cluster in `browser_renderer_spec_sequence_failures_2026-06-11.md`.

### T3 — Diagnose and patch compiled-JIT crash in layout renderer (≤1 day)
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` (4328 lines)
The crash occurs when importing the renderer module under `--mode=native`/Cranelift (W1006
mut-capability; isolated as Cranelift-layer issue). Run `SIMPLE_EXECUTION_MODE=interpret`
probe vs. direct `--interpret` to identify the exact construct. Even a narrow fix
(e.g., wrapping the mutable array pattern that triggers W1006) would unblock compiled-mode
and drop frame time from ~1.2 s to measured compiled speed.
Evidence: `pure_simple_web_render_interpreter_bound_2026-06-06.md` §"compiled-path crash isolated".

### T4 — Replace per-char substring in word-width estimation (≤4h)
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
`_estimate_word_width_px` uses `value.substring(i, i+1)` per char in a loop. Replace with
`value.char_code_at(i)` + integer lookup (as the char-code fix partially did). Eliminates
O(L) string allocations per word. Measured savings: ~300 ms / frame on text-heavy pages.

### T5 — Wire `spl_fonts` proportional advance widths to layout layer (≤1 day)
**Files:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
`src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl` (302 lines)
Expose `spl_fonts` horizontal advance for a given codepoint + font_size. Replace
`_estimate_char_width_base` lookup table with the fontdue metric for ASCII range.
Update `text_painter.spl` `_estimate_char_width_px` to call the runtime metric.
Partial fix; does not require full HarfBuzz shaping for ASCII-heavy corpus improvement.
Bug: `simple_web_renderer_ttf_glyph_metrics.md`.

### T6 — Dirty-rect GPU text upload (≤4h per backend)
**Files:** `src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl` (749 lines),
`backend_rocm.spl` (631 lines), `backend_metal.spl` (689 lines), `backend_vulkan.spl` (699 lines)
Each has `_gpu_draw_text_fallback` with comment "upload only the dirty rect."
The CPU render step already writes only a bounding rect of `text_len * advance × font_h` pixels.
Pass that bounding rect to a new `_upload_rect(d_fb, host_buf, x, y, w, h, stride)` helper
instead of `_upload_host_to_device` for the whole FB. Cuts ~8 MB per draw_text to ~(text_w × font_h × 4) bytes.

### T7 — Add `draw_glyph_run` to `Engine2DExtended` trait (≤1 day, API only)
**File:** `src/lib/gc_async_mut/gpu/engine2d/backend.spl`
Add `me draw_glyph_run(atlas_id: i32, runs: [GlyphSlot])` to `Engine2DExtended` with a default
implementation that falls back to per-char `draw_text`. Stub a `GlyphSlot` struct
`(x, y, codepoint, color, size)`. This unblocks GPU atlas-based text without breaking existing
backends. Target files for stub impls: `backend_vulkan.spl`, `backend_software.spl`.

### T8 — Split `web_render_backend_api_spec.spl` into focused suites (≤4h)
**File:** `test/01_unit/app/ui/web_render_backend_api_spec.spl`
Current duration: 71,354 ms for 11 tests (bug `web_render_backend_api_spec_perf_2026-06-05.md`).
Split into: (a) API shape/contract tests (no render, fast), (b) pixel correctness tests
(small fixtures, 1–2 backends), (c) full-corpus perf tests (separate slow suite).
Moves routine CI off the 71-second path.

### T9 — Scope session-level pixel cache (≤4h)
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`
`SimpleWebEngine2DStaticPixelCache` fields `last_html: text`, `last_pixels: [u32]` are
module-level. Make them session-scoped (constructor-injected or passed as `mut` ref) so
parallel render sessions don't share state. Prerequisite for T2; also fixes the cross-test
state issue identified in `browser_renderer_spec_sequence_failures_2026-06-11.md`.

### T10 — Implement stb_image binding for `draw_image` (≤1 day)
**Files:** `src/runtime/stb_image.h` (already vendored), new `src/lib/gc_async_mut/gpu/browser_engine/image_decode.spl`
Add `extern` FFI for `stb_image_load_from_memory(bytes, len, w_out, h_out, channels_out)` → `[u32]`.
Wire to `html_string_parser.spl` or `layout_renderer.spl` `<img>` node handling to replace the
colored-box placeholder. Required for any meaningful visual parity with real HTML pages.

---

## Key File Reference

| File | Lines | Role |
|------|-------|------|
| `src/app/ui/backend_loader.spl` | 73 | Backend dispatch entry |
| `src/app/ui/detect.spl` | 103 | Runtime backend detection |
| `src/app/ui.web/render_cache.spl` | — | SHA-256 frame cache |
| `src/app/ui.web/backend.spl` | — | WebRenderBackend wrapper |
| `src/app/ui.browser/renderer.spl` | — | Semantic → HTML render |
| `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl` | 181 | Backend selector + chromium/pure-Simple fork |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl` | 1082 | HTML → Engine2D dispatch, heuristic/layout split |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` | 4328 | Full block-flow layout + 5×7 paint |
| `src/lib/gc_async_mut/gpu/browser_engine/selector_matcher.spl` | 77 | CSS selector matching |
| `src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl` | 302 | Proportional text width estimation |
| `src/lib/gc_async_mut/gpu/browser_engine/backend_screenshot_capture.spl` | 218 | Parity-test pixel capture |
| `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | 772 | Engine2D front-end, backend dispatch |
| `src/lib/gc_async_mut/gpu/engine2d/backend.spl` | — | RenderBackend + Engine2DExtended traits |
| `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` | 757 | Software raster + dirty_tiles |
| `src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl` | — | SIMD hot-rows, delegates to software |
| `src/lib/gc_async_mut/gpu/engine2d/glyph.spl` | 326 | 5×7 bitmap glyph data + render_text_to_buffer |

## Bug Docs Referenced

| Bug | Status | Impact |
|-----|--------|--------|
| `pure_simple_web_render_interpreter_bound_2026-06-06.md` | Open (compiled crash) | 1.2–1.6 s/frame |
| `web_render_backend_api_spec_perf_2026-06-05.md` | Open | 71 s test suite |
| `browser_renderer_spec_sequence_failures_2026-06-11.md` | Open — 22 failures | Spec correctness |
| `simple_web_renderer_ttf_glyph_metrics.md` | Open | Text layout accuracy |
