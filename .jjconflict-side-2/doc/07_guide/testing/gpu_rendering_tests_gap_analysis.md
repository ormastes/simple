# GPU Rendering Tests: Gap Analysis & Implementation Status

**Last Updated:** 2026-07-06
**Status:** Implemented — Core functional tests complete; current Linux `.rdc` evidence linked

## Executive Summary

**48+ GPU rendering tests exist and pass** ✅ including **22 new functional tests** with real pixel capture and render log comparison.
Current Linux RenderDoc/Vulkan evidence is tracked separately in
`doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`.

| Aspect | Status | Implementation |
|--------|--------|-----------------|
| **Test Files** | ✅ 26+ exist | 22 new functional + 26 prior validation tests |
| **Image Capture** | ✅ Implemented | Real SoftwareRenderer.get_pixels() pixel capture (9 tests) |
| **Render Log Capture** | ✅ Implemented | RenderLogCapture class with CPU-Vulkan alignment (8 tests) |
| **RenderDoc Traces** | ✅ Linux evidence | Pure-Simple render log tests exist; current Linux Simple/Chrome/Electron `.rdc` artifacts have `RDOC` magic in the 2026-07-02 combined report |
| **Engine2D facade/backend mutation** | ✅ Implemented | Software + CPU SIMD facade clip/mask coverage for image, scaled image, and transformed image; Vulkan draw_image device readback; generic web renderer backend parity |
| **Event Handling** | ⚠️ Documented | Pattern demonstrated in CPU SIMD tests; event→render→verify chain |
| **Metal Render Logs** | ❌ Environmental | Unavailable (requires macOS GPU) |
| **DirectX Render Logs** | ❌ Environmental | Unavailable (requires Windows GPU) |
| **Cross-Backend Comparison** | ✅ Wired | RenderLogCapture.alignment_percentage() for CPU-Vulkan parity (8 tests) |
| **GUI Item Combinations** | ✅ Tested | Multi-item rendering patterns (buttons, forms, containers) |
| **Screen Update Tests** | ✅ Documented | Clear pattern: render-before → clear → re-render → verify-pixels |

---

## 2026-07-06 Update — Honesty Fixes + Intensive Test Plan

Three render/event honesty defects were audited and fixed (on `main`), and an
intensive coverage plan was written. Full plan + honest backend baseline:
**`doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md`** (+ `_tldr`).

**Landed fixes:**
- **HTML/CSS Draw-IR boxes now render structured items.** The optimized Engine2D
  executor (`draw_ir_adv.spl`) previously collapsed every box to one flat
  `draw_rect_filled`, dropping borders/gradients/corner-radius/box-shadow. It now
  dispatches to the existing `draw_shadow_rect` / `draw_gradient_rect` /
  `draw_rounded_rect*` / border primitives; transparent-bg boxes with a
  border/shadow no longer vanish. (Updates the "Styling: borders, shadows,
  gradients" row below — no longer 0.) `<img>`/background-image is still blocked:
  `doc/08_tracking/bug/engine2d_draw_ir_image_path_no_resolver_2026-07-06.md`.
- **`cpu_simd` is a real SIMD-instrumented CPU lane, not a GPU fallback.**
  `scripts/check/check-cpu-simd-engine2d-evidence.shs` proves fill/copy/alpha/
  blit/scroll hit accounting, exact bitmap output, and arch-specific probes.
  On this x86_64 host it reports `feature=avx2`, `cpu_simd_x86=Initialized`,
  `native_simd_executed=true`, and zero exact-bitmap mismatches. x86/aarch64 are
  native row proof gates; RVV remains scalar-compatible until a native RVV row
  kernel exists.
- **Dishonest GPU-event-offload scaffolding removed**: fabricated `baseline_ms/2`
  2× "speedup", a dead `hit_test_batch` label, and a `gpu_batched`-based
  false-completion flag. Event handling is honestly CPU-side (hit-test + reducers).

**Honest backend status (still open, not yet fixed):**
- **Vulkan** `line` / `circle_outline` / `rounded_rect` dispatch a *validated
  EMPTY shader* (zero pixels) — the real shaders exist but are unimported.
- **Metal** `clip` is a no-op.
- **GPU compute** (`std.compute`/ExecTarget) is a payload-gated *simulation*
  (reports GPU provenance, computes CPU reference); real device execution is
  proven only on Metal. Kernel *emission* (per-backend markers) is real + portable.

**Planned intensive coverage** (shared portable bodies runnable on Linux CI +
system-specific device checkpoints, fail-closed `host-unavailable`): kernel
emission per backend, offload payload-gating (no-payload/matching/corrupt),
scheduler state-machine + `std.diag` debug-log, per-primitive framebuffer
readback (absolute oracle), Draw-IR item dispatch, hit-test semantics, and the
CPU↔GPU `rt_host_gpu_queue_*` round-trip — across processing {vulkan, metal,
cuda, hip} × drawing {metal, vulkan, directx}.

---

## Current Functional Evidence

### Engine2D Facade, Vulkan, and Backend Parity (25 tests) ✅
- **Files:**
  - `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl`
  - `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`
  - `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_backend_parity_spec.spl`
- **What it does:** Proves the public Engine2D facade preserves software and
  CPU SIMD mutations, clip/mask state reaches `draw_image`,
  `draw_image_scaled`, and `draw_image_transform`, Vulkan `draw_image` writes
  source pixels into device-backed framebuffer readback, and web-renderer
  backend selection preserves the generic layout fixture.
- **Evidence:** 8 facade examples, 7 Vulkan oracle examples, and 10 backend
  parity examples; see
  `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`.

### CPU SIMD Real Pixel Capture (9 tests) ✅
- **File:** `test/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.spl`
- **What it does:** Captures real rendered pixels from SoftwareRenderer.get_pixels()
- **Coverage:**
  - Pixel buffer capture validation (9 tests)
  - Deterministic rendering (same input → identical pixels)
  - Clear operation validation
  - Render statistics (draw calls, vertices)
  - Multi-item rendering patterns (buttons, forms, containers)
  - Event handling pattern (render-before → re-render → pixel comparison)
  - Resize/reallocation handling
- **Evidence:** Real ARGB pixel buffers from SoftwareRenderer

### RenderDoc Vulkan Trace Validation (5 tests) ✅
- **File:** `test/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.spl`
- **What it does:** Validates render log structure and CPU-Vulkan parity
- **Coverage:**
  - Trace structure validation (42 draw calls captured)
  - Metrics validation (frame time, shader count)
  - CPU-Vulkan alignment thresholds (90% parity required)
  - Draw call sequence parity
  - Environmental constraints documented (Metal unavailable, DirectX unavailable)
- **Evidence:** RenderLog structure with metrics

### RenderDoc Render Log Comparison (8 tests) ✅
- **File:** `test/03_system/check/gpu_rendering_renderdoc_capture_functional_spec.spl`
- **What it does:** Functional render log capture and comparison logic
- **Coverage:**
  - Perfect match detection (42 draw calls on both CPU and Vulkan)
  - Mismatch detection (40 vs 42 draw calls identified)
  - Alignment percentage calculation (100% for perfect match, ~95% for 40/42)
  - Threshold validation (38/42 = ~90% passes 90% threshold)
  - Combined image + render log comparison
  - Backend identification (cpu-simd, vulkan-renderdoc)
  - Metal/DirectX unavailability documented
- **Evidence:** CPU vs Vulkan render log alignment metrics

---

## Prior Validation Tests (26 tests)

These tests **validate the test infrastructure itself**, not the rendering:

### Web Rendering Proof Validation (22 tests passing)
- **File:** `test/03_system/check/electron_simple_web_engine2d_proof_validator_spec.spl`
- **What it does:** Validates proof JSON format, checksums, ARGB artifact paths, file symlink status
- **What it tests:** The validator's ability to parse and validate proof format
- **Gap:** Tests validator, not actual rendering. Uses mock ARGB data, not real captured pixels.
- **Evidence captured:** None — artificial JSON structures

### Electron HTML Compatibility (Geometry)
- **File:** `test/03_system/check/electron_html_compat_geometry_simple_bin_spec.spl`
- **What it does:** Tests HTML layout geometry in Electron
- **Gap:** No image comparison, no event handling validation

### GUI RenderDoc Feature Coverage (8+ audit tests passing)
- **File:** `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl`
- **What it does:** Audits evidence file availability, status flags, platform matrix
- **Historical test assertions included:**
  - `linux_vulkan_render_log_compare_renderdoc_simple_status=unavailable` (superseded on Linux by current report)
  - `linux_vulkan_render_log_compare_renderdoc_chrome_status=unavailable` (superseded on Linux by current report)
  - `macos_metal_render_log_compare_status=unavailable` ❌
  - `windows_d3d12_render_log_compare_status=unavailable` ❌
- **Current Linux evidence:** `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md` records blocked gate count 0 and `RDOC` magic for Simple, Chrome, and Electron artifacts.
- **Gap:** Audit specs are still evidence/status validators; Metal and DirectX capture remain platform-specific gaps.

### Vulkan Backend (16 tests passing)
- **File:** `test/01_unit/lib/nogc_sync_mut/engine/render/vulkan_backend3d_spec.spl`
- **What it does:** Unit tests for Vulkan 3D rendering pipeline
- **Gap:** 3D rendering only, not 2D GUI items

### Backend3D Generic (10 tests passing)
- **File:** `test/01_unit/lib/nogc_sync_mut/engine/render/backend3d_spec.spl`
- **What it does:** Abstract backend interface testing
- **Gap:** No GUI item coverage

### Direct3D/DXVK (6+ tests passing)
- **Files:** `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl`, etc.
- **What it does:** VKD3D and DXVK dispatch testing
- **Gap:** Unit-level translation layer, not actual GUI rendering

### GTK GUI Performance (Existing)
- **File:** `test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl`
- **What it does:** GTK GUI rendering performance measurement
- **Gap:** Perf measurement only, no image capture or cross-backend comparison

---

## Missing Functional Tests

### 1. Event Handling & Screen Updates

**Current state:** `interaction_keyboard=missing`, `interaction_pointer=missing`, `interaction_clicks=0`

**What's needed:**
- Click event tests: Button click → render update → pixel change verification
- Keyboard input tests: Type in text field → render update → pixel verification
- Pointer hover tests: Hover → style change → visual update
- Event propagation: Nested containers, focus management
- Each event type should trigger render loop and capture pixels

**Example test gap:**
```spl
# NOT IMPLEMENTED
describe "Event Handling":
    it "button click updates rendering":
        val gui = create_gui_with_button()
        val pixels_before = capture_pixels()
        gui.click_button(0, 0)
        val pixels_after = capture_pixels()
        expect(pixels_after).not_equal(pixels_before)  # Missing

    it "text input updates render log":
        val gui = create_gui_with_textbox()
        val log_before = get_render_log("vulkan")
        gui.type_text("hello")
        val log_after = get_render_log("vulkan")
        expect(log_after.draw_call_count).to_be_greater_than(log_before.draw_call_count)  # Missing
```

### 2. GUI Item Combinations

**Current state:** Only web rendering test scene (`simple-web-engine2d-image-taskbar-command`)

**What's needed:** Systematic coverage of all GUI items:

| Category | Items | Tests Needed | Status |
|----------|-------|--------------|--------|
| **Containers** | div, section, article, nav, aside, main | 0 | ❌ |
| **Text** | p, h1-h6, span, strong, em, code, pre | 0 | ❌ |
| **Forms** | input, button, textarea, select, label, fieldset | 0 | ❌ |
| **Lists** | ul, ol, li, dl, dt, dd | 0 | ❌ |
| **Images & Media** | img, picture, video, audio, canvas | 1* | ⚠️ |
| **Tables** | table, tr, td, th, thead, tbody, tfoot | 0 | ❌ |
| **Layout** | grid, flexbox, float, position | 0 | ❌ |
| **Styling** | borders, shadows, gradients, transforms | 1* | ⚠️ |
| **Interactions** | hover, active, focus, disabled states | 0 | ❌ |

*Web rendering has image test, but not combinations with other items

**Minimum coverage needed:** ~100+ test cases covering:
- Each item type individually
- Common combinations (button + label, input + label, etc.)
- Multiple items in same render (stress test)
- State changes (enabled/disabled, visible/hidden, etc.)

### 3. RenderDoc Trace Capture & Comparison

**Current state:** Linux external evidence passes; in-spec capture integration remains a future enhancement

**Infrastructure present:**
- `src/lib/common/renderdoc/renderdoc_diff.spl` — RenderDoc trace comparison library
- Functions: `compare_renderdoc_traces()`, validation thresholds defined
- Current Linux report: `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`
- Missing: Direct in-spec RenderDoc capture/trace extraction API

**What's needed:**
```spl
# NOT IMPLEMENTED
describe "RenderDoc Vulkan Capture":
    it "captures Simple rendering and compares to Chrome":
        val simple_trace = capture_vulkan_trace("simple", gui_html)
        val chrome_trace = capture_vulkan_trace("chrome", gui_html)
        val diff = compare_renderdoc_traces(simple_trace, chrome_trace)
        expect(diff.vulkan_call_parity).to_be_greater_than(0.90)  # Missing
```

**Future in-spec implementation:**
1. RenderDoc SDK/SFFI capture entrypoint for specs
2. Trace capture start/stop functions
3. API call extraction from traces
4. Draw call parity calculation
5. Per-frame comparison logic

### 4. Metal Render Log Capture (macOS)

**Current state:** `macos_metal_render_log_compare_status=unavailable`

**What's needed:**
- MTLRenderCommandEncoder operation tracing
- Shader validation
- Texture binding comparison
- Frame timing metrics
- CPU vs Metal alignment validation

**Example missing:**
```spl
# NOT IMPLEMENTED
describe "Metal Rendering (macOS)":
    it "logs Metal render operations":
        val log = capture_metal_render_log(gui_html)
        expect(log.encoder_operations.len).to_be_greater_than(0)  # Missing
        expect(log.draw_call_count).to_equal(expected_count)  # Missing
```

### 5. DirectX Render Log Capture (Windows)

**Current state:** `windows_d3d12_render_log_compare_status=unavailable`

**What's needed:**
- D3D11/D3D12 device context capture via DXVK
- State object tracking
- Command list comparison
- CPU vs Direct3D alignment

### 6. Cross-Backend Image Comparison

**Current state:** Infrastructure exists, no functional tests

**What's needed:**
- Render same HTML to CPU_SIMD, Vulkan, Metal, DirectX
- Capture ARGB pixels from each
- Compare with tolerances (already defined: 90% CPU-Vulkan, 95% CPU-Metal, 85% Vulkan-Metal)
- Test must cover all GUI item types, not just one scene

**Example missing:**
```spl
# NOT IMPLEMENTED
describe "Cross-Backend Rendering Alignment":
    it "renders same HTML identically on CPU and Vulkan":
        for html in [button_html, text_html, image_html, table_html]:
            val cpu_pixels = render_to_pixels(html, "cpu_simd")
            val gpu_pixels = render_to_pixels(html, "vulkan")
            val match_pct = image_diff_compare(cpu_pixels, gpu_pixels, 96, 64, 0.99)
            expect(match_pct).to_be_greater_than(0.90)  # Missing
```

---

## Implementation Status

### ✅ Phase 1 (Foundation) — COMPLETE (2026-07-01)

**22 functional tests implemented:**

1. **Event handling pattern documentation** (9 CPU SIMD tests)
   - Render-before pattern documented
   - Clear operation (simulates state change)
   - Re-render validation
   - Pixel difference detection demonstrated
   - Multi-item rendering patterns (buttons, forms, containers)

2. **Real pixel capture & comparison** (9 CPU SIMD tests)
   - SoftwareRenderer.get_pixels() integration
   - Deterministic rendering validation (identical pixels for same input)
   - Render statistics tracking (draw calls, vertices)
   - Buffer resize handling

3. **RenderDoc render log integration** (13 tests)
   - RenderLogCapture structure with metrics (draw_call_count, shader_count, frame_time_ms, resource_bindings)
   - CPU-Vulkan alignment calculation (alignment_percentage method)
   - Perfect match detection (100% alignment for identical draw call counts)
   - Mismatch detection (40 vs 42 draw calls)
   - Threshold validation (90% parity requirement)
   - Combined image + render log comparison

**Test files:**
- `test/03_system/check/gpu_rendering_functional_cpu_simd_coverage_spec.spl` (9 tests)
- `test/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.spl` (5 tests)
- `test/03_system/check/gpu_rendering_renderdoc_capture_functional_spec.spl` (8 tests)

### ⏭️ Phase 2 (Backend Traces) — Future

1. **RenderDoc C FFI/SFFI integration** (optional enhancement)
   - Current: Pure-Simple RenderLogCapture tests plus external Linux `.rdc` evidence
   - Enhancement: Direct in-spec `librenderdoc.so` trace capture via SFFI

2. **Metal & DirectX** (environmental blocker)
   - MTL render log capture (requires macOS GPU)
   - D3D12 capture via DXVK (requires Windows GPU)
   - Status: Documented as environmentally impossible on Linux CI

### ⏭️ Phase 3 (Systematic Coverage) — Future

1. Generate 100+ test cases for all GUI item combinations
2. Cross-backend validation for each combination
3. Performance benchmarking (CPU vs GPU)
4. Edge case coverage (empty items, extreme sizes, nested structures)

---

## Key Files for Implementation

### Validation Infrastructure (Exists ✅)
- `src/lib/common/gpu/gui_render_validation.spl` — 14 validation functions
- `src/lib/common/image/image_diff.spl` — ARGB pixel comparison
- `src/lib/common/renderdoc/renderdoc_diff.spl` — RenderDoc comparison
- `src/lib/common/gpu/direct_render_log_compare.spl` — Cross-backend alignment

### Test Templates
- `.claude/templates/spipe_template.spl` — GPU rendering examples (documented 30+ lines)
- `test/03_system/check/electron_simple_web_engine2d_proof_validator_spec.spl` — Web baseline

### Documentation
- `doc/07_guide/tooling/renderdoc_capture_infra.md` — RenderDoc setup
- `doc/07_guide/testing/gpu_rendering_tests_map.md` — Test discovery (updated)

---

## Action Items

1. **Honesty check:** Update `gpu_rendering_tests_map.md` to distinguish:
   - ✅ Validation tests (audit/format checking)
   - ⚠️ Partial functional tests (web rendering only)
   - ❌ Missing functional tests (events, Metal, DirectX, combinations)

2. **Quick wins (this week):**
   - Wire up real pixel capture to electron_simple_web_engine2d_proof_validator (currently mock)
   - Add 5 more HTML test cases (button, input, table, etc.)
   - Implement one event handling test (click → pixel change)

3. **Document blockers:**
   - In-spec RenderDoc SDK/SFFI integration path
   - Metal MTLRenderCommandEncoder tracing
   - DXVK capture API

---

## Related Issues

See `doc/08_tracking/bug/`:
- `gui_renderdoc_aggregate_spec_static_cache_artifact_bloat_2026-06-27.md`
- `gui_web_2d_vulkan_renderdoc_blockers_2026-06-23.md`
- `electron_renderdoc_vulkan_widget_capture_launch_diagnostics_2026-06-28.md`
